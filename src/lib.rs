use num::{traits::Pow, BigUint, Integer};
use std::{cmp::Ordering, num::NonZeroU32, num::NonZeroU8, ops::Mul};

// Idea for setting up the tokens in primitives
lazy_static::lazy_static! {
    // Idea of how to define the multipliers and use these statics
    pub static ref M1: Multiplier = Multiplier::new(NonZeroU8::new(1).expect("OK"));
    pub static ref M2: Multiplier = Multiplier::new(NonZeroU8::new(2).expect("OK"));
    pub static ref M18: Multiplier = Multiplier::new(NonZeroU8::new(18).expect("OK"));
    pub static ref M30: Multiplier = Multiplier::new(NonZeroU8::new(30).expect("OK"));

    pub static ref DAI: Token = Token {
        address: [0_u8; 20],
        multiplier: M18.clone(),
    };
}

// TODO: Is this necessary?
pub struct Token {
    pub address: [u8; 20],
    pub multiplier: Multiplier,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Multiplier(BigUint);

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct BigNum(BigUint, Multiplier);

impl Multiplier {
    fn new(multiplier: NonZeroU8) -> Self {
        let multiplier_pow = u32::from(NonZeroU32::from(multiplier));

        Self(BigUint::from(10_u16).pow(multiplier_pow))
    }
}

impl std::ops::Sub<&Multiplier> for &Multiplier {
    type Output = (Ordering, Multiplier);

    fn sub(self, rhs: &Multiplier) -> Self::Output {
        let order = self.0.cmp(&rhs.0);

        match &order {
            Ordering::Less => (order, Multiplier((&rhs.0).div_floor(&self.0))),
            Ordering::Equal => (order, Multiplier(self.0.to_owned())),
            Ordering::Greater => (order, Multiplier((&self.0).div_floor(&rhs.0))),
        }
    }
}

impl std::ops::Sub<Multiplier> for BigNum {
    type Output = BigNum;

    fn sub(self, rhs: Multiplier) -> Self::Output {
        convert_multipliers(rhs, self)
    }
}

pub fn convert_multipliers(into_multiplier: Multiplier, from_bignum: BigNum) -> BigNum {
    match &into_multiplier - &from_bignum.1 {
        (Ordering::Less, multiplier) => BigNum(from_bignum.0.div_floor(&multiplier.0), into_multiplier),
        (Ordering::Greater, multiplier) => BigNum(from_bignum.0.mul(&multiplier.0), into_multiplier),
        (Ordering::Equal, _) => from_bignum
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_multiplier_and_multiplier_subtraction() {
        let ten = Multiplier::new(NonZeroU8::new(10).unwrap());

        assert_eq!(&BigUint::from(10_000_000_000_u64), &ten.0);

        let twenty = Multiplier::new(NonZeroU8::new(20).unwrap());

        assert_eq!((Ordering::Greater, ten.clone()), &twenty - &ten);
        assert_eq!((Ordering::Less, ten.clone()), &ten - &twenty);
        assert_eq!((Ordering::Equal, ten.clone()), &ten - &ten);
    }



    #[test]
    fn test_convert_multipliers_roundtrip() {
        let dai_multiplier = Multiplier::new(NonZeroU8::new(18).unwrap());
        let other_multiplier = Multiplier::new(NonZeroU8::new(30).unwrap());

        let input_value = BigNum(
            BigUint::from(321_000_000_000_000_u64),
            other_multiplier.clone(),
        );

        let dai_actual = convert_multipliers(dai_multiplier.clone(), input_value.clone());
        let dai_expected = BigNum(BigUint::from(321_u16), dai_multiplier);
        assert_eq!(dai_actual, dai_expected);

        let other_actual = convert_multipliers(other_multiplier, dai_actual);

        assert_eq!(
            other_actual, input_value,
            "No flooring involved so it should result in the same as input"
        );
    }

    #[test]
    fn test_convert_multipliers_roundtrip_with_flooring() {
        let dai_multiplier = Multiplier::new(NonZeroU8::new(18).unwrap());
        let other_multiplier = Multiplier::new(NonZeroU8::new(30).unwrap());

        let input_value = BigNum(
            BigUint::from(321_999_999_999_999_u64),
            other_multiplier.clone(),
        );

        let dai_actual = convert_multipliers(dai_multiplier.clone(), input_value.clone());
        let dai_expected = BigNum(BigUint::from(321_u16), dai_multiplier);

        assert_eq!(dai_actual, dai_expected);

        let other_actual = convert_multipliers(other_multiplier.clone(), dai_actual);
        let other_expected = BigNum(BigUint::from(321_000_000_000_000_u64), other_multiplier);

        assert_eq!(other_actual, other_expected);
    }
}
