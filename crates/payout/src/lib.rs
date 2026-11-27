//! What a word signed on a contract's payout means: the outputs it
//! selects ([`Payout::paid_bits`]) and the units it counts
//! ([`Payout::amount`]).
//!
//! A payout pays `2^i` units for each bit `i` of the word from `low_bits`
//! below `K` (`bits`) and, with a rest `R > 0`, one output more of `R`
//! units selected by bit `K`, so that `V_max = 2^K - 1 + R` units is any
//! size, not only `2^K - 1`: below `2^K` the binary outputs pay
//! `0..=2^K - 1` and, with `R`'s, `R..=V_max`, which meet.
//!
//! One definition for everything that reads a word: `lichen-contract`
//! builds the payout on it, and an L2's statement (in its zkVM guest:
//! this crate is `no_std`, of no dependencies) reads the words both
//! parties signed with it.
#![no_std]

#[cfg(test)]
extern crate std;

use core::{fmt, ops::Range};

/// A word a party signs on a payout: the bits selecting its outputs, not
/// an amount. [`Payout::word`] makes one of an amount, [`Payout::amount`]
/// reads one back. Not ordered, and no number: compare what words count.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Word(u32);

impl Word {
    /// The word of these bits, as signed (read off a signature, say).
    pub const fn new(bits: u32) -> Word {
        Word(bits)
    }
    /// Its bits, to sign.
    pub const fn to_u32(self) -> u32 {
        self.0
    }
    /// Whether its bit `i` is set (none at 32 or above).
    pub const fn is_set(self, i: u32) -> bool {
        i < 32 && (self.0 >> i) & 1 == 1
    }
}

/// A payout's outputs: `bits` (`K`), the binary outputs' from `low_bits`,
/// and the rest (`R`, none if 0).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Payout {
    pub bits: u32,
    pub low_bits: u32,
    pub rest: u32,
}

/// Why a payout, or an amount on one, is refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Invalid {
    /// More than 32 bits, or more low bits than bits.
    Shape { bits: u32, low_bits: u32 },
    /// A rest of 32 bits: its bit `K` is beyond the word.
    RestPastWord,
    /// A rest not below `2^K`, which the binary outputs pay.
    RestHigh { rest: u32, bits: u32 },
    /// A rest below `2^low_bits`, which no output is.
    RestLow { rest: u32, low_bits: u32 },
    /// An amount above `V_max`, which no word pays.
    AboveCap { amount: u64, cap: u64 },
}

impl fmt::Display for Invalid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Invalid::Shape { bits, low_bits } => {
                write!(f, "a payout of {bits} bits, {low_bits} low")
            }
            Invalid::RestPastWord => f.write_str("a rest output beyond the word's 32 bits"),
            Invalid::RestHigh { rest, bits } => {
                write!(f, "a rest of {rest} units, not below 2^{bits}")
            }
            Invalid::RestLow { rest, low_bits } => {
                write!(f, "a rest of {rest} units, below 2^{low_bits}")
            }
            Invalid::AboveCap { amount, cap } => {
                write!(f, "{amount} units, above the cap of {cap}")
            }
        }
    }
}

impl core::error::Error for Invalid {}

impl Payout {
    /// Refused unless of 32 bits at most, `low_bits` of them, and of no
    /// rest or one of at least `2^low_bits` units below `2^K`, with bit
    /// `K` in the 32-bit word.
    pub fn check(&self) -> Result<(), Invalid> {
        let (bits, low_bits, rest) = (self.bits, self.low_bits, self.rest);
        if bits > 32 || low_bits > bits {
            return Err(Invalid::Shape { bits, low_bits });
        }
        if rest > 0 {
            if bits > 31 {
                return Err(Invalid::RestPastWord);
            }
            if u64::from(rest) >= 1 << bits {
                return Err(Invalid::RestHigh { rest, bits });
            }
            if u64::from(rest) < 1 << low_bits {
                return Err(Invalid::RestLow { rest, low_bits });
            }
        }
        Ok(())
    }

    /// `V_max` in units: the binary outputs' `2^K - 1` and `R`.
    pub fn v_max(&self) -> u64 {
        1u64.checked_shl(self.bits).map_or(u64::MAX, |k| k - 1).saturating_add(u64::from(self.rest))
    }

    /// The bits a word has outputs at: `low_bits..K`, and `K` with `R`.
    /// A word's bits below `low_bits` count ([`Payout::amount`]) but no
    /// output pays them; those from the end of this range on neither.
    pub fn paid_bits(&self) -> Range<u32> {
        self.low_bits..self.bits.saturating_add(u32::from(self.rest > 0))
    }

    /// Bit `i`'s output, in units: `2^i`, or `R` at `K`.
    pub fn bit_units(&self, i: u32) -> u64 {
        match self.rest > 0 && i == self.bits {
            true => u64::from(self.rest),
            false => 1u64.checked_shl(i).unwrap_or(0),
        }
    }

    /// The word a party signs to be paid `amount` units: `amount` itself
    /// if the binary outputs pay it (at most `2^K - 1`), else bit `K` set,
    /// `R` selected, over `amount - R` in the binary outputs. Fixed: a
    /// party that signs again after a restart must sign the same word, or
    /// it signed two.
    pub fn word(&self, amount: u64) -> Result<Word, Invalid> {
        self.check()?;
        let cap = self.v_max();
        if amount > cap {
            return Err(Invalid::AboveCap { amount, cap });
        }
        let binary = (1u64 << self.bits) - 1;
        let word = match amount > binary {
            true => (1u64 << self.bits) | (amount - u64::from(self.rest)),
            false => amount,
        };
        Ok(Word(word as u32))
    }

    /// What `word` counts, in units, if it is of this payout: none if it
    /// sets a bit no output is at nor below ([`Payout::paid_bits`]'s end
    /// or above), which would count more than any output pays. Else the
    /// word, its bit `K` counting `R` (not `2^K`): what the outputs it
    /// selects pay, and its bits below `low_bits`, which none does.
    pub fn amount(&self, word: Word) -> Option<u64> {
        match word.0.checked_shr(self.paid_bits().end) {
            Some(above) if above != 0 => None,
            _ => Some(self.count(word)),
        }
    }

    /// What `word` counts, in units, whatever bits it sets: as
    /// [`Payout::amount`], but a bit beyond the outputs counted as in a
    /// number. No word is paid more on chain than it counts; one beyond
    /// the outputs counts more than it is paid. For a word only ever
    /// weighed against what it would be paid at most (her claim, which
    /// her bits beyond the outputs only inflate), so that a word of no
    /// meaning still counts; else [`Payout::amount`].
    pub fn count(&self, word: Word) -> u64 {
        let w = u64::from(word.0);
        match self.rest > 0 && word.is_set(self.bits) {
            true => w - (1 << self.bits) + u64::from(self.rest),
            false => w,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::iter;

    fn payout(bits: u32, low_bits: u32, rest: u32) -> Payout {
        Payout { bits, low_bits, rest }
    }

    /// What the outputs a word selects pay, in units.
    fn paid(p: &Payout, word: Word) -> u64 {
        p.paid_bits().filter(|i| word.is_set(*i)).map(|i| p.bit_units(i)).sum()
    }

    /// Every amount up to the cap has a word that counts it, and the
    /// outputs it selects pay it but for its bits below `low_bits`; any
    /// word is paid at most what it counts, and any of the payout's
    /// exactly that but for them.
    #[test]
    fn every_amount_is_paid_by_its_word() {
        for bits in 1..=7 {
            for low_bits in 0..=bits.min(3) {
                for rest in iter::once(0).chain((1u32 << low_bits)..(1 << bits)) {
                    let p = payout(bits, low_bits, rest);
                    p.check().unwrap();
                    for amount in 0..=p.v_max() {
                        let word = p.word(amount).unwrap();
                        assert_eq!(p.amount(word), Some(amount), "{p:?}: {amount}");
                        let short = amount - paid(&p, word);
                        assert!(short < 1 << low_bits, "{p:?}: {amount} paid {short} short");
                    }
                    assert!(p.word(p.v_max() + 1).is_err());
                    for word in (0..(4u32 << bits)).map(Word::new) {
                        assert!(paid(&p, word) <= p.count(word), "{p:?}: {word:?}");
                        if let Some(amount) = p.amount(word) {
                            assert!(amount - paid(&p, word) < 1 << low_bits, "{p:?}: {word:?}");
                        }
                    }
                }
            }
        }
    }

    /// No rest, the word is the amount, as before there was one; the
    /// words of a rest frozen (a restarted signer signs the same).
    #[test]
    fn the_words_are_fixed() {
        let none = payout(10, 0, 0);
        assert_eq!(none.v_max(), 1_023);
        assert_eq!(none.paid_bits(), 0..10);
        for a in [0, 1, 300, 1_023] {
            assert_eq!(none.word(a).unwrap(), Word::new(a as u32));
        }
        assert_eq!(none.count(Word::new(u32::MAX)), u64::from(u32::MAX), "the word as a number");
        // 12 units: 1, 2, 4 and 5
        let twelve = payout(3, 0, 5);
        assert_eq!(twelve.v_max(), 12);
        assert_eq!((twelve.paid_bits(), twelve.bit_units(3)), (0..4, 5));
        let words = [0, 7, 8, 10, 12].map(|a| twelve.word(a).unwrap().to_u32());
        assert_eq!(words, [0, 7, 0b1011, 0b1101, 0b1111]);
        // 23 437 units of 512 sats (12M sats): 14 bits and 7 054
        let p = payout(14, 0, 7_054);
        assert_eq!(p.v_max(), 23_437);
        assert_eq!(p.word(16_383).unwrap(), Word::new(16_383));
        assert_eq!(p.word(16_384).unwrap(), Word::new((1 << 14) | 9_330));
        assert_eq!(p.word(23_437).unwrap(), Word::new((1 << 15) - 1));
        assert_eq!(p.amount(Word::new((1 << 14) | 9_330)), Some(16_384));
        // a word of 32 bits, the most
        let wide = payout(32, 0, 0);
        assert_eq!(wide.v_max(), u64::from(u32::MAX));
        assert_eq!(wide.amount(Word::new(u32::MAX)), Some(u64::from(u32::MAX)));
        let widest_rest = payout(31, 0, (1 << 31) - 1);
        assert_eq!(widest_rest.amount(Word::new(u32::MAX)), Some(u64::from(u32::MAX) - 1));
    }

    /// A word setting a bit beyond the outputs counts as a number, more
    /// than it is paid: no amount of the payout.
    #[test]
    fn a_word_beyond_the_outputs_is_no_amount() {
        let none = payout(10, 9, 0);
        assert_eq!(none.amount(Word::new(1_023)), Some(1_023));
        assert_eq!(none.amount(Word::new(1 << 10)), None);
        assert_eq!(none.count(Word::new(1 << 10)), 1_024);
        assert_eq!(paid(&none, Word::new(1 << 10)), 0);
        let rest = payout(10, 9, 600);
        assert_eq!(rest.amount(Word::new((1 << 10) | 1_023)), Some(1_623));
        assert_eq!(rest.amount(Word::new(1 << 11)), None);
        assert_eq!(rest.count(Word::new(1 << 11)), 2_048);
        assert_eq!(rest.amount(Word::new(u32::MAX)), None);
        // bits below `low_bits` count, no output paying them
        assert_eq!(rest.amount(Word::new(23)), Some(23));
        assert_eq!(paid(&rest, Word::new(23)), 0);
    }

    /// A rest is an output (at least `2^low_bits`) below `2^K`, its bit in
    /// the word.
    #[test]
    fn a_rest_is_checked() {
        assert_eq!(payout(10, 9, 511).check(), Err(Invalid::RestLow { rest: 511, low_bits: 9 }));
        assert!(payout(10, 9, 512).check().is_ok());
        assert_eq!(payout(10, 0, 1_024).check(), Err(Invalid::RestHigh { rest: 1_024, bits: 10 }));
        assert_eq!(payout(32, 0, 1).check(), Err(Invalid::RestPastWord));
        assert!(payout(31, 0, 1).check().is_ok());
        assert!(payout(32, 0, 0).check().is_ok());
        assert_eq!(payout(33, 0, 0).check(), Err(Invalid::Shape { bits: 33, low_bits: 0 }));
        assert_eq!(payout(8, 9, 0).check(), Err(Invalid::Shape { bits: 8, low_bits: 9 }));
        assert!(payout(33, 0, 0).word(0).is_err());
        assert_eq!(
            payout(3, 0, 5).word(13),
            Err(Invalid::AboveCap { amount: 13, cap: 12 })
        );
        // unchecked, no panic
        let wild = payout(u32::MAX, u32::MAX, u32::MAX);
        let _ = (wild.v_max(), wild.amount(Word::new(u32::MAX)), wild.count(Word::new(1)));
    }
}
