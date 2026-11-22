//! The cut-and-choose's shared parts (BABE; agent notes:
//! docs/BABE_GADGET_PLAN.md), as the hub-proves opening uses them
//! ([`crate::hp`]): an opened instance, the network's cut-and-choose, the
//! dealing's and the shares' encodings; and what a dispute reads off the
//! chain: a link's arguments, `assert`'s proof.

use anyhow::{ensure, Context, Result};
use lichen_babe::opening;
pub use lichen_babe::opening::soundness;
use lichen_babe::setup::{Secret, DIGITS, VALUES};
use lichen_babe::vsss::Dealing;
use serde::{Deserialize, Serialize};

use crate::Net;

/// An opened instance: its index, seed and secrets (hex), on the wire
/// ([`lichen_babe::opening::Opened`]).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Opened {
    pub i: u32,
    pub seed: String,
    pub shares: String,
}

impl Opened {
    pub fn of(o: &opening::Opened) -> Opened {
        Opened { i: o.i, seed: hex::encode(o.seed), shares: shares_to_hex(&o.shares) }
    }
    pub fn read(&self) -> Result<opening::Opened> {
        let seed = hex::decode(&self.seed)?.try_into().map_err(|_| anyhow::anyhow!("a seed of other than 32 bytes"))?;
        Ok(opening::Opened { i: self.i, seed, shares: shares_from_hex(&self.shares)? })
    }
}

/// The cut-and-choose on a network: `N` instances, `M` kept. BABE's
/// smallest point with secret sharing, (78, 10): a cheating garbler
/// escapes with odds of 1 in `C(78, 10)`, about 2^40. Regtest's tests keep
/// 2 of 4. Fixed, not the hub's choice: the dealing is drawn from the
/// contract's seed and journal alone, so an opening resumed with another
/// `N` would open shares of other polynomials from the same draw, and
/// with the first opening's, solve for the whole dealing.
pub fn cut_and_choose(net: Net) -> (u32, u32) {
    match net {
        Net::Regtest => (4, 2),
        _ => (78, 10),
    }
}

pub fn dealing_to_hex(d: &Dealing) -> String {
    use k256::elliptic_curve::sec1::ToEncodedPoint;
    let mut v = Vec::new();
    for poly in &d.commitments {
        for coeffs in poly {
            for p in coeffs {
                v.extend_from_slice(p.to_affine().to_encoded_point(true).as_bytes());
            }
        }
    }
    hex::encode(v)
}

/// The dealing of `hex` for `DIGITS` digits of polynomials of `degree`.
pub fn dealing_from_hex(h: &str, degree: usize) -> Result<Dealing> {
    use k256::elliptic_curve::sec1::FromEncodedPoint;
    let b = hex::decode(h)?;
    ensure!(b.len() == DIGITS * VALUES * (degree + 1) * 33, "a dealing of {} bytes", b.len());
    let mut points = b.chunks(33).map(|c| {
        let e = k256::EncodedPoint::from_bytes(c).ok().context("a point's encoding")?;
        Option::<k256::AffinePoint>::from(k256::AffinePoint::from_encoded_point(&e)).map(k256::ProjectivePoint::from).context("not a point")
    });
    let mut commitments = Vec::with_capacity(DIGITS);
    for _ in 0..DIGITS {
        let mut poly: [Vec<k256::ProjectivePoint>; VALUES] = Default::default();
        for c in poly.iter_mut() {
            *c = (0..=degree).map(|_| points.next().expect("counted")).collect::<Result<_>>()?;
        }
        commitments.push(poly);
    }
    Ok(Dealing { commitments })
}

pub fn shares_to_hex(s: &[[Secret; VALUES]]) -> String {
    hex::encode(s.iter().flatten().flatten().copied().collect::<Vec<u8>>())
}

pub fn shares_from_hex(h: &str) -> Result<Vec<[Secret; VALUES]>> {
    let b = hex::decode(h)?;
    ensure!(b.len() == DIGITS * VALUES * 32, "shares of {} bytes", b.len());
    Ok(b.chunks(VALUES * 32).map(|d| core::array::from_fn(|v| d[32 * v..32 * v + 32].try_into().expect("32"))).collect())
}

/// A link's witness arguments below both signatures, consumption order.
pub fn link_args(tx: &bitcoin::Transaction) -> Vec<Vec<u8>> {
    lichen_btc::witness::witness_args_consumption_order(&tx.input[0].witness).into_iter().skip(2).collect()
}

/// What `assert` put on chain.
pub struct Asserted {
    pub digits: Vec<u8>,
    pub bits: Vec<bool>,
    pub preimages: Vec<lichen_babe::reveal::Preimage>,
    pub proof: Option<ark_groth16::Proof<ark_bn254::Bn254>>,
}
