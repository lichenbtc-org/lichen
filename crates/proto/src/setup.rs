//! The cut-and-choose's shared parts (BABE; agent notes:
//! docs/BABE_GADGET_PLAN.md), as the hub-proves opening uses them
//! ([`crate::hp`]): an opened instance, the soundness a wallet asks, the
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

/// The least soundness a wallet accepts of the cut-and-choose, as bits:
/// `C(N, M) ≥ 2^bits` (regtest's tests keep a few instances).
pub fn min_soundness(net: Net) -> u32 {
    match net {
        Net::Regtest => 2,
        _ => 40,
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

/// What `assert` put on chain: π1, signed. π2 and π3 the hub hands over
/// off chain ([`crate::ProofParts`]).
pub struct Asserted {
    pub digits: Vec<u8>,
    pub bits: Vec<bool>,
    pub preimages: Vec<lichen_babe::reveal::Preimage>,
}

impl Asserted {
    /// The whole proof, π1 the chain's and π2 and π3 `pi2` and `pi3` (as
    /// the hub hands them over), if they are points.
    pub fn proof(&self, pi2: &[u8], pi3: &[u8]) -> Option<ark_groth16::Proof<ark_bn254::Bn254>> {
        lichen_babe::statement::proof_of(&self.bits, pi2, pi3)
    }

    /// The proof the hub answers a challenge on: `own`, the one it made
    /// and asserted, if it is of the π1 on chain. The chain carries no π2
    /// and π3 to fall back on.
    pub fn answered_on(&self, own: Option<ark_groth16::Proof<ark_bn254::Bn254>>) -> Option<ark_groth16::Proof<ark_bn254::Bn254>> {
        own.filter(|p| lichen_babe::gadget::input(&p.a) == self.bits)
    }
}

#[cfg(test)]
mod tests {
    use super::Asserted;
    use lichen_babe::statement::{mock_prove, pi23_to_bytes};

    fn asserted(proof: &ark_groth16::Proof<ark_bn254::Bn254>) -> Asserted {
        let bits = lichen_babe::gadget::input(&proof.a);
        let digits = lichen_babe::setup::digits(&bits);
        Asserted { digits, bits, preimages: vec![] }
    }

    #[test]
    fn a_challenge_is_answered_on_the_hubs_own_proof_of_the_asserted_pi1() {
        let proof = mock_prove(b"journal");
        let on_chain = asserted(&proof);
        assert_eq!(on_chain.answered_on(Some(proof.clone())), Some(proof.clone()));
        assert_eq!(on_chain.answered_on(None), None);
        // Another π1 than the one asserted (say, of another journal): none.
        let other = mock_prove(b"another journal");
        assert_eq!(on_chain.answered_on(Some(other)), None);
    }

    #[test]
    fn the_whole_proof_is_the_chains_pi1_and_the_hubs_pi2_and_pi3() {
        let proof = mock_prove(b"journal");
        let on_chain = asserted(&proof);
        let (pi2, pi3) = pi23_to_bytes(&proof);
        assert_eq!(on_chain.proof(&pi2, &pi3), Some(proof.clone()));
        // Of another proof: no point mismatch, but another proof, which
        // does not verify.
        let (pi2, pi3) = pi23_to_bytes(&mock_prove(b"another journal"));
        let mixed = on_chain.proof(&pi2, &pi3).unwrap();
        assert!(!lichen_babe::statement::Kind::Mock.verify(b"journal", &mixed));
        // None handed over: no proof.
        assert_eq!(on_chain.proof(&[], &[]), None);
    }
}
