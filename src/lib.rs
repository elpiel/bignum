use num::{traits::Pow, BigUint, Integer, Zero};
use std::{cmp::Ordering, fmt, marker::PhantomData, num::NonZeroU32, num::NonZeroU8, ops::Mul};
use typenum::{NonZero, Unsigned};
// use thiserror::Error;

// Idea for setting up the tokens in primitives
lazy_static::lazy_static! {
    // Idea of how to define the precisions and use these statics
    pub static ref M1: Precision = Precision::new(NonZeroU8::new(1).expect("OK"));
    pub static ref M2: Precision = Precision::new(NonZeroU8::new(2).expect("OK"));
    pub static ref M18: Precision = Precision::new(NonZeroU8::new(18).expect("OK"));
    pub static ref M30: Precision = Precision::new(NonZeroU8::new(30).expect("OK"));

    pub static ref DAI: Token = Token {
        address: [0_u8; 20],
        precision: M18.clone(),
    };
}

// TODO: Is this necessary?
pub struct Token {
    pub address: [u8; 20],
    pub precision: Precision,
}

#[derive(Debug, Clone, Eq, PartialEq)]
/// Precision is the number of decimal points that the number contains.
/// Example:
/// 10.00 (value: 10 with Precision(2)) - Precision(4) = 10.0000 (value 10 with Precision(4))
///
pub struct Precision(BigUint);

pub struct Float<U: NonZero + Unsigned>(BigUint, PhantomData<U>);

impl<U: NonZero + Unsigned> Float<U> {
    pub fn new(value: BigUint) -> Self {
        Self(value, PhantomData::<U>)
    }
}

impl<U: NonZero + Unsigned> fmt::Display for Float<U> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let float_string =
            String::from_utf8(to_str_bytes(self)).expect("Should never ever NEVER fails");

        f.pad_integral(true, "", &float_string)
    }
}

pub(crate) fn to_str_bytes<U: NonZero + Unsigned>(float: &Float<U>) -> Vec<u8> {
    let res = float.0.to_radix_le(10);

    let map_to_ascii = |mut r: u8| {
        if r < 10 {
            r += b'0';
        } else {
            r += b'a' - 10;
        }

        r
    };
    let precision = U::to_usize();

    let mut float_ascii = if precision >= res.len() {
        let zeros_after_comma = precision - res.len();

        res.into_iter().map(map_to_ascii)
            .chain(vec![map_to_ascii(0); zeros_after_comma].into_iter())
            .chain(".0".as_bytes().to_vec())
            .collect()
    } else {
        let float_ascii = res
            .into_iter()
            .enumerate()
            .fold(Vec::new(), |mut acc, (index, r)| {
                // are we at the point where we need the decimal point?
                if index == precision {
                    acc.extend(".".as_bytes());
                }

                let ascii_num = map_to_ascii(r);
                acc.push(ascii_num);

                acc
            });

        float_ascii
    };

    float_ascii.reverse();

    float_ascii
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct BigNum(BigUint, Precision);

impl Precision {
    fn new(precision: NonZeroU8) -> Self {
        let precision_pow = u32::from(NonZeroU32::from(precision));

        Self(BigUint::from(10_u16).pow(precision_pow))
    }

    // The actual power of 10 (10 ^ power)
    pub fn to_multiplier(self) -> BigUint {
        self.0
    }

    /// ```rust
    /// use bignum::Precision;
    /// use typenum::{U3, Unsigned};
    /// use num::BigUint;
    ///
    /// assert_eq!(BigUint::from(1_000_u16), Precision::new_type::<U3>().to_multiplier());
    /// // This will **not** compile at all, since `0_u8` does **not** impl `typenum::NonZero`
    /// // assert_eq!(expected, Precision::new_type::<typenum::U0>());
    /// ```
    pub fn new_type<U: NonZero + Unsigned>() -> Self {
        Self(BigUint::from(10_u16).pow(U::to_u32()))
    }

    pub fn phantom<U: NonZero + Unsigned>(_from: PhantomData<U>) -> Self {
        Self::new_type::<U>()
    }
}

impl std::ops::Sub<&Precision> for &Precision {
    type Output = (Ordering, Precision);

    fn sub(self, rhs: &Precision) -> Self::Output {
        let order = self.0.cmp(&rhs.0);

        match &order {
            Ordering::Less => (order, Precision((&rhs.0).div_floor(&self.0))),
            Ordering::Equal => (order, Precision(self.0.to_owned())),
            Ordering::Greater => (order, Precision((&self.0).div_floor(&rhs.0))),
        }
    }
}

impl std::ops::Sub<Precision> for BigNum {
    type Output = BigNum;

    fn sub(self, rhs: Precision) -> Self::Output {
        convert_precisions(rhs, self)
    }
}

pub fn convert_precisions(into_precision: Precision, from_bignum: BigNum) -> BigNum {
    match &into_precision - &from_bignum.1 {
        (Ordering::Less, precision) => {
            BigNum(from_bignum.0.div_floor(&precision.0), into_precision)
        }
        (Ordering::Greater, precision) => BigNum(from_bignum.0.mul(&precision.0), into_precision),
        (Ordering::Equal, _) => from_bignum,
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_precision_and_precision_subtraction() {
        let ten = Precision::new(NonZeroU8::new(10).unwrap());

        assert_eq!(&BigUint::from(10_000_000_000_u64), &ten.0);

        let twenty = Precision::new(NonZeroU8::new(20).unwrap());

        assert_eq!((Ordering::Greater, ten.clone()), &twenty - &ten);
        assert_eq!((Ordering::Less, ten.clone()), &ten - &twenty);
        assert_eq!((Ordering::Equal, ten.clone()), &ten - &ten);
    }

    #[test]
    fn test_convert_precisions_roundtrip() {
        let dai_precision = Precision::new(NonZeroU8::new(18).unwrap());
        let other_precision = Precision::new(NonZeroU8::new(30).unwrap());

        let input_value = BigNum(
            BigUint::from(321_000_000_000_000_u64),
            other_precision.clone(),
        );

        let dai_actual = convert_precisions(dai_precision.clone(), input_value.clone());
        let dai_expected = BigNum(BigUint::from(321_u16), dai_precision);
        assert_eq!(dai_actual, dai_expected);

        let other_actual = convert_precisions(other_precision, dai_actual);

        assert_eq!(
            other_actual, input_value,
            "No flooring involved so it should result in the same as input"
        );
    }

    #[test]
    fn test_convert_precisions_roundtrip_with_flooring() {
        let dai_precision = Precision::new(NonZeroU8::new(18).unwrap());
        let other_precision = Precision::new(NonZeroU8::new(30).unwrap());

        let input_value = BigNum(
            BigUint::from(321_999_999_999_999_u64),
            other_precision.clone(),
        );

        let dai_actual = convert_precisions(dai_precision.clone(), input_value.clone());
        let dai_expected = BigNum(BigUint::from(321_u16), dai_precision);

        assert_eq!(dai_actual, dai_expected);

        let other_actual = convert_precisions(other_precision.clone(), dai_actual);
        let other_expected = BigNum(BigUint::from(321_000_000_000_000_u64), other_precision);

        assert_eq!(other_actual, other_expected);
    }

    #[test]
    fn test_precision_from_type() {
        use typenum::{Unsigned, U0, U18, U3};

        let expected = Precision(BigUint::from(1_000_u64));
        assert_eq!(expected, Precision::new_type::<U3>());

        // assert_eq!(expected, Precision::new_type::<U0>());
    }

    #[test]
    fn test_float() {
        use typenum::{U12, U2, U20};
        let float = Float::<U12>::new(321_999_999_999_999_u64.into());
        assert_eq!("321.999999999999", float.to_string());

        let float = Float::<U2>::new(20_u16.into());
        assert_eq!("0.20", &float.to_string());

        let float = Float::<U20>::new(20_u16.into());
        assert_eq!("0.00000000000000000020", &float.to_string());

        let float = Float::<U20>::new(321_999_999_999_999_u64.into());
        assert_eq!("0.00000321999999999999", float.to_string());
    }
}
