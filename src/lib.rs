use num::{bigint::Sign, traits::Pow, BigInt, BigUint, Integer};
use std::{num::NonZeroI16, num::NonZeroU8, ops::Mul};

// Idea for setting up the tokens in primitives
lazy_static::lazy_static! {
    pub static ref DAI: Token = Token {
        address: [0_u8; 20],
        multiplier: NonZeroU8::new(18).expect("Should create NonZeroU8 from 18"),
    };
}

// TODO: Is this necessary
pub struct Token {
    pub address: [u8; 20],
    pub multiplier: NonZeroU8,
}



pub fn convert_multipliers(
    into_multiplier: NonZeroU8,
    (from_multiplier, value): (NonZeroU8, BigUint),
) -> BigUint {
    let diff_multiplier =
        i16::from(NonZeroI16::from(into_multiplier)) - i16::from(NonZeroI16::from(from_multiplier));

    match BigInt::from(diff_multiplier).into_parts() {
        (Sign::Plus, multiplier) => {
            let power = BigUint::from(10_u16).pow(&multiplier);
            BigUint::from(value).mul(power)
        }
        (Sign::Minus, multiplier) => {
            let power = BigUint::from(10_u16).pow(&multiplier);

            BigUint::from(value).div_floor(&power)
        }
        _ => unreachable!(),
    }
}

#[cfg(test)]
mod test {

    use super::*;

    #[test]
    fn test_convert_multipliers_roundtrip() {
        let dai_multiplier = NonZeroU8::new(18).unwrap();
        let other_multiplier = NonZeroU8::new(30).unwrap();

        let input_value: (NonZeroU8, BigUint) =
            (other_multiplier, BigUint::from(321_000_000_000_000_u64));

        let dai_actual = convert_multipliers(dai_multiplier, input_value.clone());

        assert_eq!(dai_actual, BigUint::from(321_u16));

        let other_actual = convert_multipliers(other_multiplier, (dai_multiplier, dai_actual));

        assert_eq!(
            other_actual, input_value.1,
            "No flooring involved so it should result in the same input"
        );
    }

    #[test]
    fn test_convert_multipliers_roundtrip_with_flooring() {
        let dai_multiplier = NonZeroU8::new(18).unwrap();
        let other_multiplier = NonZeroU8::new(30).unwrap();

        let input_value: (NonZeroU8, BigUint) =
            (other_multiplier, BigUint::from(321_999_999_999_999_u64));

        let dai_actual = convert_multipliers(dai_multiplier, input_value.clone());

        assert_eq!(dai_actual, BigUint::from(321_u16));

        let other_actual = convert_multipliers(other_multiplier, (dai_multiplier, dai_actual));
        let other_expected = BigUint::from(321_000_000_000_000_u64);

        assert_eq!(other_actual, other_expected);
    }

    #[test]
    #[ignore = "No reason yet, just testing"]
    fn multiplier_math() {
        let dai_multiplier: (u8, BigUint) = (18, BigUint::from(10_u16).pow(18_u32));
        let other_multiplier: (u8, BigUint) = (30, BigUint::from(10_u16).pow(30_u32));

        // In DAI this will be `321`
        let input_value: (u8, u64) = (other_multiplier.0, 321_000_000_000_000);

        let real_value_multiplier = i16::from(dai_multiplier.0) - i16::from(other_multiplier.0);

        assert_eq!(-12_i16, real_value_multiplier);

        let dai_value = match BigInt::from(real_value_multiplier).into_parts() {
            (Sign::Plus, multiplier) => {
                let power = BigUint::from(10_u16).pow(&multiplier);
                BigUint::from(input_value.1).mul(power)
            }
            (Sign::Minus, multiplier) => {
                let power = BigUint::from(10_u16).pow(&multiplier);

                BigUint::from(input_value.1).div_floor(&power)
            }
            _ => unreachable!(),
        };

        assert_eq!(dai_value, BigUint::from(321_u16))
    }
}
