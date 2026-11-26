//! The contract's terms, its leaves (`default`, and the payout's bit and
//! reserve leaves), and the outputs that pay a withdrawal `b` on the
//! dispute path or end the contract by default at `T_close`.
//!
//! The payout's outputs are `2^i` units for `i < K` and, for a contract
//! of any other size than `2^K - 1` units, one more of `R` units: a word's
//! bit `i` gives output `i` to Alice, clear to the hub ([`Terms::word`]).
//!
//! The contract output's key path is both parties' MuSig2 key: the fold,
//! the cooperative withdrawal, signed when it happens ([`crate::Fold`]).
//! Its leaves are `default` and the dispute's `escalate` (BABE's
//! `request`, `lichen_babe`):
//! - `default`: after `T_close`, a pre-signed transaction paying the hub
//!   and returning Alice's reserve (not withdrawing is not a lie);
//! - `escalate`: Alice's claim on chain, the dispute's first move.

use anyhow::{ensure, Result};
use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::{Amount, ScriptBuf, TxOut};
use lichen_btc::script::BuilderExt;
use lichen_btc::taptree::{Leaf, TapTree};
use lichen_btc::tx::Timelock;
use crate::keys::{ContractCtx, Role};
use lichen_wots::{Chain, WotsExt, WotsPublicOf};

/// A contract's terms.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Terms {
    /// The contract's identifier `c`, the memo a return must carry.
    pub id: u32,
    /// The payout's granularity `u`.
    pub unit: Amount,
    /// `K`: the payout's binary outputs, of `2^i` units for `i < K`.
    pub bits: u32,
    /// On the dispute path, bits below this get no output (they would be
    /// dust): `b` is paid rounded down to a multiple of `2^low_bits` units,
    /// the remainder to the hub. 0 pays every bit; with sats as the unit,
    /// 9 (512 sats).
    pub low_bits: u32,
    /// Alice's deposit `D`, in units.
    pub deposit: u32,
    /// `T_close`: after it, with no claim, everything goes to the hub.
    pub t_close: u32,
    /// The contract reserves `r_A`, `r_H`: returned in every honest
    /// outcome, forfeited to the other side by losing a dispute.
    pub reserve_alice: Amount,
    pub reserve_hub: Amount,
    /// `R`, in units: the payout's one output beyond its binary ones, so
    /// that `V_max = (2^K - 1 + R) u` is any size, not only `2^K - 1`
    /// units. 0, none; else `2^low_bits <= R < 2^K` and `K <= 31`: below
    /// `2^K` the binary outputs pay `0..=2^K - 1` and, with `R`'s,
    /// `R..=V_max`, which meet. Bit `K` of the signed word selects it
    /// ([`Terms::word`]).
    #[serde(default, skip_serializing_if = "is_zero")]
    pub rest: u32,
}

fn is_zero(n: &u32) -> bool {
    *n == 0
}

impl Terms {
    /// `V_max` in units: the binary outputs' `2^K - 1` and `R`.
    pub fn v_max_units(&self) -> u64 {
        (1u64 << self.bits) - 1 + u64::from(self.rest)
    }
    pub fn v_max(&self) -> Amount {
        self.unit * self.v_max_units()
    }
    /// Refused unless `R` is none, or an output of at least `2^low_bits`
    /// units below `2^K`, with bit `K` in the 32-bit word.
    pub fn check_rest(&self) -> Result<()> {
        ensure!(self.bits <= 32 && self.low_bits <= self.bits, "a payout of {} bits, {} low", self.bits, self.low_bits);
        if self.rest > 0 {
            ensure!(self.bits <= 31, "a rest output beyond the word's 32 bits");
            ensure!(u64::from(self.rest) < 1u64 << self.bits, "a rest of {} units, not below 2^{}", self.rest, self.bits);
            ensure!(u64::from(self.rest) >= 1u64 << self.low_bits, "a rest of {} units, below 2^{}", self.rest, self.low_bits);
        }
        Ok(())
    }
    /// The word a party signs to be paid `amount` units: `amount` itself
    /// if the binary outputs pay it (at most `2^K - 1`), else bit `K` set,
    /// `R` selected, over `amount - R` in the binary outputs. Fixed: a
    /// party that signs again after a restart must sign the same word, or
    /// it signed two.
    pub fn word(&self, amount: u64) -> Result<u32> {
        self.check_rest()?;
        ensure!(amount <= self.v_max_units(), "{amount} units, above the cap of {}", self.v_max_units());
        let binary = (1u64 << self.bits) - 1;
        let word = match amount > binary {
            true => (1u64 << self.bits) | (amount - u64::from(self.rest)),
            false => amount,
        };
        Ok(word as u32)
    }
    /// What a signed `word` counts, in units: the word itself, but with
    /// `R`, whose bit `K` counts `R`, not `2^K`. Bits above `K` count as
    /// they would in a number (no output pays them), so a word is never
    /// paid more on chain than it counts, and the outputs it selects pay it
    /// less only by its bits below `low_bits`. Total: any word counts.
    pub fn amount(&self, word: u32) -> u64 {
        let k = 1u64 << self.bits;
        match self.rest > 0 && u64::from(word) & k != 0 {
            true => u64::from(word) - k + u64::from(self.rest),
            false => u64::from(word),
        }
    }
    /// The bits of the signed word with an output: `low_bits..K`, and `K`
    /// with `R`.
    pub fn paid_bits(&self) -> std::ops::Range<u32> {
        self.low_bits..self.bits + u32::from(self.rest > 0)
    }
    /// Bit `i`'s output, in units: `2^i`, or `R` at `K`.
    pub fn bit_units(&self, i: u32) -> u64 {
        match i == self.bits {
            true => u64::from(self.rest),
            false => 1u64 << i,
        }
    }
    /// The index `equiv_b` takes on the reserve output: `K`, after the bit
    /// outputs', or `K + 1` with `R`'s output at `K`.
    fn reserve_index(&self) -> u32 {
        self.bits + u32::from(self.rest > 0)
    }
    /// Both reserves: what the winner of a dispute takes on top of its
    /// share of `V_max`.
    pub fn reserves(&self) -> Amount {
        self.reserve_alice + self.reserve_hub
    }
}

/// Bit `i` of `b`'s input-word signature (the prover's depth-1 key for
/// word 0, which signs `b` big-endian): `want` 1 for Alice's leaf, 0 for
/// the hub's. Alice's leaf waits `delta`, so that if she signed two values
/// of `b` the hub's `equiv_b` takes the output first. Witness, wire order:
/// the word's reveal, the spender's signature. [`bit_leaf_signed`] by
/// Alice.
pub fn bit_leaf<H: Chain>(ctx: &ContractCtx, i: u32, b_key: &WotsPublicOf<H>, want: bool) -> Leaf {
    bit_leaf_signed(ctx, i, b_key, Role::User, want)
}

/// Bit `i` of the value `signer` signed under `b_key` (a one-time key for
/// a 4-byte word, the value big-endian): `want` 1 for Alice's leaf, 0 for
/// the hub's. The signer's leaf waits `delta`, so that if it signed two
/// values the other party's `equiv_b` takes the output first; the other's
/// is immediate. Alice signs her claim `b`; a hub that proves signs what
/// it says she is owed, `b′` (an L2's front, `lichen_babe::graph`).
/// Witness, wire order: the word's reveal, the spender's signature.
pub fn bit_leaf_signed<H: Chain>(ctx: &ContractCtx, i: u32, b_key: &WotsPublicOf<H>, signer: Role, want: bool) -> Leaf {
    let who = if want { Role::User } else { Role::Hub };
    let m = b_key.params.message_digits as usize;
    assert_eq!(m, 8, "a word's key signs 4 bytes");
    // digit k (0 the most significant nibble) sits at depth m - 1 - k
    let (nibble, j) = (7 - i / 4, i % 4);
    let (mut b, tl) = if who == signer { (Builder::new().csv(ctx.params.delta), Timelock::csv(ctx.params.delta)) } else { (Builder::new(), Timelock::NONE) };
    b = b.checksigverify(&ctx.key(who).payment).wots_verify(b_key);
    b = b.push_int((m - 1 - nibble as usize) as i64).push_opcode(OP_PICK);
    // reduce the nibble mod 2^(j+1), then compare with 2^j
    for h in (j + 1..4).rev() {
        b = b.push_opcode(OP_DUP).push_int(1 << h).push_opcode(OP_GREATERTHANOREQUAL).push_opcode(OP_IF).push_int(1 << h).push_opcode(OP_SUB).push_opcode(OP_ENDIF);
    }
    b = b.push_int(1 << j).push_opcode(OP_GREATERTHANOREQUAL);
    if !want {
        b = b.push_opcode(OP_NOT);
    }
    b = b.push_opcode(OP_VERIFY);
    for _ in 0..m / 2 {
        b = b.push_opcode(OP_2DROP);
    }
    let name = if want { format!("alice_bit_{i}") } else { format!("hub_bit_{i}") };
    Leaf::new(name, b.push_int(1).into_script(), tl)
}

/// `equiv_b` on each bit output: two different signatures under `b`'s
/// one-time key (Alice signed two values of `b`); the hub takes the
/// output. `i` only makes the leaf distinct per output. Witness, wire
/// order: one reveal, the other, the hub's signature.
/// [`equiv_b_leaf_signed`] by Alice.
pub fn equiv_b_leaf<H: Chain>(ctx: &ContractCtx, i: u32, b_key: &WotsPublicOf<H>) -> Leaf {
    equiv_b_leaf_signed(ctx, i, b_key, Role::User)
}

/// `equiv_b` on each output of a payout of a value `signer` signed: two
/// different signatures under `b_key` (it signed two values); the other
/// party takes the output. `i` only makes the leaf distinct per output.
/// Witness, wire order: one reveal, the other, the taker's signature.
pub fn equiv_b_leaf_signed<H: Chain>(ctx: &ContractCtx, i: u32, b_key: &WotsPublicOf<H>, signer: Role) -> Leaf {
    let m = b_key.params.message_digits as usize;
    let mut b = Builder::new().push_int(i64::from(i)).push_opcode(OP_DROP).checksigverify(&ctx.key(signer.other()).payment).wots_verify(b_key);
    for _ in 0..m {
        b = b.push_opcode(OP_TOALTSTACK);
    }
    b = b.wots_verify(b_key);
    for _ in 0..m {
        b = b.push_opcode(OP_FROMALTSTACK);
    }
    // count the digits that differ; at least one must
    b = b.push_int(0);
    for j in 0..m {
        b = b
            .push_int((m - j) as i64)
            .push_opcode(OP_PICK)
            .push_int((2 * m - j + 1) as i64)
            .push_opcode(OP_PICK)
            .push_opcode(OP_SUB)
            .push_opcode(OP_0NOTEQUAL)
            .push_opcode(OP_ADD);
    }
    b = b.push_opcode(OP_VERIFY);
    for _ in 0..m {
        b = b.push_opcode(OP_2DROP);
    }
    Leaf::new(format!("equiv_b_{i}"), b.push_int(1).into_script(), Timelock::NONE)
}

/// The output for bit `i`: Alice's leaf, the hub's, and `equiv_b`.
/// [`bit_tree_signed`] by Alice.
pub fn bit_tree<H: Chain>(ctx: &ContractCtx, i: u32, b_key: &WotsPublicOf<H>) -> Result<TapTree> {
    bit_tree_signed(ctx, i, b_key, Role::User)
}

/// The output for bit `i` of the value `signer` signed: Alice's leaf, the
/// hub's, and `equiv_b`.
pub fn bit_tree_signed<H: Chain>(ctx: &ContractCtx, i: u32, b_key: &WotsPublicOf<H>, signer: Role) -> Result<TapTree> {
    TapTree::new(vec![bit_leaf_signed(ctx, i, b_key, signer, true), bit_leaf_signed(ctx, i, b_key, signer, false), equiv_b_leaf_signed(ctx, i, b_key, signer)])
}

/// `alice_reserve` on the reserve output: Alice, after `delta` (the hub's
/// chance to show an equivocation on `b`). Witness: her signature.
/// [`reserve_leaf_signed`] by Alice.
pub fn reserve_leaf(ctx: &ContractCtx) -> Leaf {
    reserve_leaf_signed(ctx, Role::User)
}

/// The signer's leaf on the reserve output (`alice_reserve`,
/// `hub_reserve`): the signer, after `delta` (the other party's chance to
/// show an equivocation). Witness: its signature.
pub fn reserve_leaf_signed(ctx: &ContractCtx, signer: Role) -> Leaf {
    let b = Builder::new().csv(ctx.params.delta).checksig(&ctx.key(signer).payment);
    let name = match signer {
        Role::User => "alice_reserve",
        Role::Hub => "hub_reserve",
    };
    Leaf::new(name, b.into_script(), Timelock::csv(ctx.params.delta))
}

/// The reserve output of a payout to Alice: both reserves, hers after
/// `delta`, the hub's with `equiv_b` (index `K`, after the bit outputs',
/// or `K + 1` with `R`).
/// [`reserve_tree_signed`] by Alice.
pub fn reserve_tree<H: Chain>(ctx: &ContractCtx, t: &Terms, b_key: &WotsPublicOf<H>) -> Result<TapTree> {
    reserve_tree_signed(ctx, t, b_key, Role::User)
}

/// The reserve output of a payout of a value `signer` signed: the
/// signer's after `delta`, the other party's with `equiv_b` (index `K`,
/// after the bit outputs', or `K + 1` with `R`).
pub fn reserve_tree_signed<H: Chain>(ctx: &ContractCtx, t: &Terms, b_key: &WotsPublicOf<H>, signer: Role) -> Result<TapTree> {
    TapTree::new(vec![reserve_leaf_signed(ctx, signer), equiv_b_leaf_signed(ctx, t.reserve_index(), b_key, signer)])
}

/// The outputs of every transaction that pays Alice's withdrawal (her
/// proof, the hub's timeout): for each bit `i` from `low_bits` to `K - 1`,
/// an output of `u 2^i`, and with `R` one of `u R` for bit `K`, Alice's iff
/// bit `i` of her signed word ([`Terms::word`]) is set; then
/// both reserves, Alice's; the rest of `available` (less `fee`) to the
/// hub.
pub fn payout<H: Chain>(ctx: &ContractCtx, t: &Terms, b_key: &WotsPublicOf<H>, available: Amount, fee: Amount) -> Result<Vec<TxOut>> {
    payout_less(ctx, t, b_key, available, fee, Amount::ZERO)
}

/// [`payout`] after a dispute whose links carried fee floors totalling
/// `floors` out of the contract: the hub, the loser, forfeits its reserve
/// less them (Alice receives `r_A + r_H - floors` with her bits; the hub
/// still `V_max - b`). [`payout_less_signed`] by Alice.
pub fn payout_less<H: Chain>(ctx: &ContractCtx, t: &Terms, b_key: &WotsPublicOf<H>, available: Amount, fee: Amount, floors: Amount) -> Result<Vec<TxOut>> {
    payout_less_signed(ctx, t, b_key, Role::User, available, fee, floors)
}

/// The outputs paying the value `signer` signed under `b_key`, after a
/// dispute whose links carried fee floors totalling `floors` out of the
/// contract (they come from the hub's reserve): for each bit `i` from
/// `low_bits` to `K - 1`, an output of `u 2^i`, and with `R` one of `u R`
/// for bit `K`, Alice's iff bit `i` is set, then:
/// - Alice signed (her claim stood, [`payout_less`]): both reserves less
///   the floors, hers after `delta` (the hub, the loser, forfeits its
///   own; it still gets `V_max - b`);
/// - the hub signed (what it proved she is owed): `r_A` to Alice's payout
///   address (she risked nothing), then the hub's reserve less the floors
///   in its reserve output, after `delta`. Below dust, that remainder goes
///   with the rest to the hub's payout address, outside `equiv_b`: a hub
///   that signs a second value then loses its bits but not that dust.
///
/// The rest of `available` (less `fee`) to the hub, if not dust.
///
/// Whoever did not sign must take its outputs, or post `equiv_b` with a
/// second signed value, within `delta` of the payout confirming: after
/// it, a signer that signed a second value can take the other's bits by
/// its own leaves. Paying the hub's value, that duty is Alice's.
pub fn payout_less_signed<H: Chain>(ctx: &ContractCtx, t: &Terms, b_key: &WotsPublicOf<H>, signer: Role, available: Amount, fee: Amount, floors: Amount) -> Result<Vec<TxOut>> {
    t.check_rest()?;
    let total = available.checked_sub(fee).ok_or_else(|| anyhow::anyhow!("the fee exceeds the output"))?;
    let reserves = t.reserves().checked_sub(floors).filter(|r| *r >= t.reserve_alice).ok_or_else(|| anyhow::anyhow!("the floors {floors} exceed the hub's reserve"))?;
    ensure!(total >= t.v_max() + reserves, "{total} cannot pay V_max {} and the reserves less the floors", t.v_max());
    let mut outs: Vec<TxOut> = t.paid_bits().map(|i| Ok(TxOut { value: t.unit * t.bit_units(i), script_pubkey: bit_tree_signed(ctx, i, b_key, signer)?.script_pubkey() })).collect::<Result<_>>()?;
    let reserve = |value| -> Result<TxOut> { Ok(TxOut { value, script_pubkey: reserve_tree_signed(ctx, t, b_key, signer)?.script_pubkey() }) };
    match signer {
        Role::User => outs.push(reserve(reserves)?),
        Role::Hub => {
            ensure!(t.reserve_alice >= ctx.params.dust, "Alice's reserve {} is dust", t.reserve_alice);
            outs.push(TxOut { value: t.reserve_alice, script_pubkey: ctx.key(Role::User).payout_spk.clone() });
            let hub = reserves - t.reserve_alice;
            if hub >= ctx.params.dust {
                outs.push(reserve(hub)?);
            }
        }
    }
    let paid: Amount = outs.iter().map(|o| o.value).sum();
    let rest = total - paid;
    if rest >= ctx.params.dust {
        outs.push(TxOut { value: rest, script_pubkey: ctx.key(Role::Hub).payout_spk.clone() });
    }
    Ok(outs)
}

/// The outputs of the transaction that ends the contract by default after
/// `T_close`: Alice's reserve back to `close_spk`, the rest (less `fee`) to
/// the hub's payout script.
pub fn default_outputs(ctx: &ContractCtx, t: &Terms, close_spk: &ScriptBuf, available: Amount, fee: Amount) -> Result<Vec<TxOut>> {
    let total = available.checked_sub(fee).ok_or_else(|| anyhow::anyhow!("the fee exceeds the output"))?;
    ensure!(total > t.reserve_alice, "{total} cannot return the reserve");
    Ok(vec![
        TxOut { value: t.reserve_alice, script_pubkey: close_spk.clone() },
        TxOut { value: total - t.reserve_alice, script_pubkey: ctx.key(Role::Hub).payout_spk.clone() },
    ])
}

/// `default` on the contract output: after `T_close`, 2-of-2 pre-signed
/// at the opening, paying [`default_outputs`]. Witness: the hub's
/// signature, the user's.
pub fn default_leaf(ctx: &ContractCtx, t_close: u32) -> Leaf {
    let b = ctx.two_of_two_verify(Builder::new().cltv(t_close));
    Leaf::new("default", b.push_int(1).into_script(), Timelock::cltv(t_close))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn terms(bits: u32, low_bits: u32, rest: u32) -> Terms {
        Terms { id: 1, unit: Amount::from_sat(1), bits, low_bits, deposit: 0, t_close: 0, reserve_alice: Amount::ZERO, reserve_hub: Amount::ZERO, rest }
    }

    /// What the outputs a word selects pay, in units.
    fn paid(t: &Terms, word: u32) -> u64 {
        t.paid_bits().filter(|i| (word >> i) & 1 == 1).map(|i| t.bit_units(i)).sum()
    }

    /// Every amount up to the cap has a word that counts it, and the
    /// outputs it selects pay it but for its bits below `low_bits`; any
    /// word is paid at most what it counts.
    #[test]
    fn every_amount_is_paid_by_its_word() {
        for bits in 1..=7 {
            for low_bits in 0..=bits.min(3) {
                for rest in std::iter::once(0).chain((1u32 << low_bits)..(1 << bits)) {
                    let t = terms(bits, low_bits, rest);
                    t.check_rest().unwrap();
                    for amount in 0..=t.v_max_units() {
                        let word = t.word(amount).unwrap();
                        assert_eq!(t.amount(word), amount, "{t:?}: {amount}");
                        let short = amount - paid(&t, word);
                        assert!(short < 1 << low_bits, "{t:?}: {amount} paid {short} short");
                    }
                    assert!(t.word(t.v_max_units() + 1).is_err());
                    for word in 0..(4u32 << bits) {
                        assert!(paid(&t, word) <= t.amount(word), "{t:?}: word {word}");
                    }
                }
            }
        }
    }

    /// No rest, the word is the amount, as before there was one; the
    /// words of a rest frozen (a restarted signer signs the same).
    #[test]
    fn the_words_are_fixed() {
        let none = terms(10, 0, 0);
        assert_eq!(none.v_max_units(), 1_023);
        assert_eq!(none.paid_bits(), 0..10);
        for a in [0, 1, 300, 1_023] {
            assert_eq!(none.word(a).unwrap(), a as u32);
        }
        assert_eq!(none.amount(u32::MAX), u64::from(u32::MAX), "no rest: the word as a number");
        // 12 units: 1, 2, 4 and 5
        let twelve = terms(3, 0, 5);
        assert_eq!(twelve.v_max_units(), 12);
        assert_eq!((twelve.paid_bits(), twelve.bit_units(3)), (0..4, 5));
        assert_eq!([0, 7, 8, 10, 12].map(|a| twelve.word(a).unwrap()), [0, 7, 0b1011, 0b1101, 0b1111]);
        // 23 437 units of 512 sats (12M sats): 14 bits and 7 054
        let t = terms(14, 0, 7_054);
        assert_eq!(t.v_max_units(), 23_437);
        assert_eq!(t.word(16_383).unwrap(), 16_383);
        assert_eq!(t.word(16_384).unwrap(), (1 << 14) | 9_330);
        assert_eq!(t.word(23_437).unwrap(), (1 << 15) - 1);
        assert_eq!(t.amount((1 << 14) | 9_330), 16_384);
    }

    /// A rest is an output (at least `2^low_bits`) below `2^K`, its bit in
    /// the word.
    #[test]
    fn a_rest_is_checked() {
        assert!(terms(10, 9, 511).check_rest().is_err());
        assert!(terms(10, 9, 512).check_rest().is_ok());
        assert!(terms(10, 0, 1_024).check_rest().is_err());
        assert!(terms(32, 0, 1).check_rest().is_err());
        assert!(terms(31, 0, 1).check_rest().is_ok());
        assert!(terms(32, 0, 0).check_rest().is_ok());
    }
}
