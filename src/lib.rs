mod util;
use std::marker::PhantomData;

use bnum::types::{U128, U256};
use typenum::{NonZero, Zero};
use util::*;

mod _priv {
    pub trait Consts {
        type Underlying;
        type Doubled;

        const MIN_H: Self;
        const MAX_H: Self;
        const ZERO_H: Self;
        const FRACTIONAL_H: Self;
        const FRACTIONAL_SQ_H: Self;
    }
}

// macro_rules! into_doubled_unchecked {
//     ($var: expr) => {
//         match <Self as _priv::Consts>::Doubled::from_be_slice(&$var.to_be_bytes()) {
//             Some(v) => v,
//             None => panic!("Failed to convert to big number (unreachable)"),
//         }
//     };
// }

/// replacement for Option::map for const context
macro_rules! map_const {
    ($e: expr, $var: tt => $f: expr) => {
        match $e {
            Some($var) => Some($f),
            _ => None,
        }
    };
}

macro_rules! unsigned_fixed {
    ($name: ident ($digit_trait: ident) => $bits: literal $underlying: ident $double: ident) => {
        #[doc = concat!("An unsigned fixed-point decimal number with ", $bits, " bits of precision.")]
        #[doc = "\n\nThe number of decimal places is determined by the `Digits` type parameter."]
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
        pub struct $name<Digits: $digit_trait>($underlying, PhantomData<Digits>);

        impl<Digits: $digit_trait> _priv::Consts for $name<Digits> {
            type Underlying = $underlying;
            type Doubled = $double;

            const MIN_H: Self = $name($underlying::MIN, PhantomData);
            const MAX_H: Self = $name($underlying::MAX, PhantomData);
            const ZERO_H: Self = $name(0, PhantomData);
            const FRACTIONAL_H: Self = $name((Self::ZERO_H.0 + 10).pow(Digits::U32), PhantomData);
            const FRACTIONAL_SQ_H: Self =
                $name((Self::ZERO_H.0 + 10).pow(2 * Digits::U32), PhantomData);
        }

        impl<Digits: $digit_trait> $name<Digits> {
            #[doc = "The smallest value that can be represented by this decimal type."]
            pub const MIN: Self = <Self as _priv::Consts>::MIN_H;

            #[doc = "The largest value that can be represented by this decimal type."]
            pub const MAX: Self = <Self as _priv::Consts>::MAX_H;

            #[doc = "The value zero."]
            pub const ZERO: Self = <Self as _priv::Consts>::ZERO_H;

            #[doc = "The value one."]
            pub const ONE: Self = <Self as _priv::Consts>::FRACTIONAL_H;

            #[doc = "Creates a new decimal from a raw underlying value without any scaling."]
            #[doc = "\n\nThis is useful when you already have a properly scaled value and want to avoid additional calculations."]
            pub const fn raw(value: $underlying) -> Self {
                Self(value, PhantomData)
            }

            #[doc = "Creates a new decimal from a value that can be converted into the underlying type."]
            #[doc = concat!("\n\nThis is similar to [`Self::raw`] but accepts any type that implements [`Into<", stringify!($underlying), ">`].")]
            pub fn from_raw(value: impl Into<$underlying>) -> Self {
                Self(value.into(), PhantomData)
            }

            #[doc = "Returns the decimal value as a big-endian byte array"]
            #[doc = concat!("\n\nSee [`", stringify!($underlying), "::to_be_bytes`] for more information.")]
            pub const fn to_be_bytes(self) -> [u8; { $bits / 8 }] {
                self.0.to_be_bytes()
            }

            #[doc = "Returns the decimal value as a little-endian byte array"]
            #[doc = concat!("\n\nSee [`", stringify!($underlying), "::to_le_bytes`] for more information.")]
            pub const fn to_le_bytes(self) -> [u8; { $bits / 8 }] {
                self.0.to_le_bytes()
            }

            #[doc = "Creates a decimal value from a big-endian byte array"]
            #[doc = concat!("\n\nSee [`", stringify!($underlying), "::from_be_bytes`] for more information.")]
            pub const fn from_be_bytes(bytes: [u8; { $bits / 8 }]) -> Self {
                Self(
                    <Self as _priv::Consts>::Underlying::from_be_bytes(bytes),
                    PhantomData,
                )
            }

            #[doc = "Creates a decimal value from a little-endian byte array"]
            #[doc = concat!("\n\nSee [`", stringify!($underlying), "::from_le_bytes`] for more information.")]
            pub const fn from_le_bytes(bytes: [u8; { $bits / 8 }]) -> Self {
                Self(
                    <Self as _priv::Consts>::Underlying::from_le_bytes(bytes),
                    PhantomData,
                )
            }

            #[doc = "Returns `true` if the decimal is zero."]
            pub const fn is_zero(&self) -> bool {
                self.0 == 0
            }

            #[doc = "Performs full-precision multiplication without scaling"]
            #[doc = "\n\nThis internal method uses the double-width type for calculations."]
            fn full_mul(&self, other: Self) -> <Self as _priv::Consts>::Doubled {
                <Self as _priv::Consts>::Doubled::from(self.0)
                    * <Self as _priv::Consts>::Doubled::from(other.0)
            }

            #[doc = "Multiplies this value by a ratio (num/den) while maintaining maximum precision"]
            #[doc = "\n\nReturns `None` if the operation would overflow or if division by zero occurs."]
            pub fn mul_ratio(&self, num: Self, den: Self) -> Option<Self> {
                self.full_mul(num)
                    .checked_div(den.0.into())
                    .and_then(|v| v.try_into().ok())
                    .map(|v| Self(v, PhantomData))
            }

            #[doc = "Checked decimal addition"]
            #[doc = "\n\nComputes `self + other`, returning `None` if overflow occurred."]
            #[doc = concat!("\n\nSee [`", stringify!($underlying), "::checked_add`] for more information.")]
            pub const fn checked_add(&self, other: Self) -> Option<Self> {
                map_const!(self.0.checked_add(other.0), v => Self(v, PhantomData))
            }

            #[doc = "Checked decimal subtraction"]
            #[doc = "\n\nComputes `self - other`, returning `None` if overflow occurred."]
            #[doc = concat!("\n\nSee [`", stringify!($underlying), "::checked_sub`] for more information.")]
            pub fn checked_sub(&self, other: Self) -> Option<Self> {
                map_const!(self.0.checked_sub(other.0), v => Self(v, PhantomData))
            }

            #[doc = "Checked decimal multiplication"]
            #[doc = "\n\nComputes `self * other`, returning `None` if overflow occurred."]
            #[doc = "\n\nFor non-zero digit types, this performs scaled multiplication to maintain decimal places."]
            pub fn checked_mul(&self, other: Self) -> Option<Self> {
                if Digits::USIZE == 0 {
                    self.0.checked_mul(other.0).map(|v| Self(v, PhantomData))
                } else {
                    self.full_mul(other)
                        .checked_div(Self::ONE.0.into())
                        .and_then(|v| v.try_into().ok())
                        .map(|v| Self(v, PhantomData))
                }
            }

            #[doc = "Checked decimal division"]
            #[doc = "\n\nComputes `self / other`, returning `None` if overflow occurred or if `other` is zero."]
            #[doc = concat!("\n\nSee [`", stringify!($underlying), "::checked_div`] for more information.")]
            pub fn checked_div(&self, other: Self) -> Option<Self> {
                self.mul_ratio(Self::ONE, other)
                // self.0.checked_div(other.0)
                //     .and_then(|v| v.checked_mul(
                //         <Self as _priv::Consts>::FRACTIONAL_H.0
                //     ))
                //     .and_then(|v| v.try_into().ok())
                //     .map(|v| Self(v, PhantomData))
            }

            #[doc = "Checked decimal exponentiation"]
            #[doc = "\n\nComputes `self.pow(exp)`, returning `None` if overflow occurred."]
            #[doc = "\n\nThis operation maintains the correct decimal scaling."]
            pub fn checked_pow(&self, exp: u32) -> Option<Self> {
                todo!()
            }

            #[doc = "Saturating decimal addition"]
            #[doc = "\n\nComputes `self + other`, saturating at the numeric bounds instead of overflowing."]
            #[doc = concat!("\n\nSee [`", stringify!($underlying), "::saturating_add`] for more information.")]
            pub const fn saturating_add(&self, other: Self) -> Self {
                Self(self.0.saturating_add(other.0), PhantomData)
            }

            #[doc = "Saturating decimal subtraction"]
            #[doc = "\n\nComputes `self - other`, saturating at the numeric bounds instead of overflowing."]
            #[doc = concat!("\n\nSee [`", stringify!($underlying), "::saturating_sub`] for more information.")]
            pub const fn saturating_sub(&self, other: Self) -> Self {
                Self(self.0.saturating_sub(other.0), PhantomData)
            }

            #[doc = "Saturating decimal multiplication"]
            #[doc = "\n\nComputes `self * other`, saturating at the numeric bounds instead of overflowing."]
            #[doc = "\n\nThis operation maintains the correct decimal scaling."]
            pub fn saturating_mul(&self, other: Self) -> Self {
                todo!()
            }

            #[doc = "Computes the absolute difference between two decimal values"]
            #[doc = "\n\nReturns `|self - other|` without overflowing."]
            pub const fn abs_diff(&self, other: Self) -> Self {
                Self(
                    if self.0 >= other.0 {
                        self.0 - other.0
                    } else {
                        other.0 - self.0
                    },
                    PhantomData,
                )
            }

            #[doc = "Returns the maximum of two decimal values"]
            #[doc = concat!("\n\nSee [`", stringify!($underlying), "::max`] for more information.")]
            pub fn max(&self, other: Self) -> Self {
                Self(self.0.max(other.0), PhantomData)
            }

            #[doc = "Returns the minimum of two decimal values"]
            #[doc = concat!("\n\nSee [`", stringify!($underlying), "::min`] for more information.")]
            pub fn min(&self, other: Self) -> Self {
                Self(self.0.min(other.0), PhantomData)
            }
        }

        impl<Digits: $digit_trait> $name<Digits>
        where
            Digits: Zero,
        {
            #[doc = "Checked shift left"]
            #[doc = "\n\nShifts the bits in the underlying value left by `exp` positions."]
            #[doc = "\n\nReturns `None` if `exp` is larger than the number of bits in the type."]
            pub const fn checked_shl(&self, exp: u32) -> Option<Self> {
                map_const!(self.0.checked_shl(exp), v => Self(v, PhantomData))
            }

            #[doc = "Checked shift right"]
            #[doc = "\n\nShifts the bits in the underlying value right by `exp` positions."]
            #[doc = "\n\nReturns `None` if `exp` is larger than the number of bits in the type."]
            pub const fn checked_shr(&self, exp: u32) -> Option<Self> {
                map_const!(self.0.checked_shr(exp), v => Self(v, PhantomData))
            }
        }

        impl<Digits: $digit_trait> $name<Digits>
        where
            Digits: NonZero,
        {
            #[doc = "Computes the multiplicative inverse (reciprocal) of this decimal value"]
            #[doc = "\n\nReturns `None` if the value is zero."]
            #[doc = "\n\nFor a value `x`, computes `1/x` while maintaining the correct decimal scaling."]
            pub const fn reciprocal(&self) -> Option<Self> {
                if self.is_zero() {
                    None
                } else {
                    Some(Self(
                        <Self as _priv::Consts>::FRACTIONAL_SQ_H.0 / self.0,
                        PhantomData,
                    ))
                }
            }

            #[doc = "Returns the largest integer less than or equal to this decimal value"]
            #[doc = "\n\nThis operation maintains the correct decimal scaling."]
            pub fn floor(&self) -> Self {
                self.0.checked_div(<Self as _priv::Consts>::FRACTIONAL_H.0)
                    .and_then(|v| v.checked_mul(<Self as _priv::Consts>::FRACTIONAL_H.0))
                    .map(|v| Self(v, PhantomData))
                    .unwrap()
            }

            #[doc = "Returns the smallest integer greater than or equal to this decimal value"]
            #[doc = "\n\nReturns `None` if the operation would overflow."]
            #[doc = "\n\nThis operation maintains the correct decimal scaling."]
            pub fn checked_ceil(&self) -> Option<Self> {
                let floor = self.floor();
                if self.0 == floor.0 {
                    Some(floor)
                } else {
                    floor.checked_add(Self::ONE)
                }
            }

            #[doc = "Returns the smallest integer greater than or equal to this decimal value"]
            #[doc = "\n\nPanics if the operation would overflow."]
            #[doc = "\n\nThis operation maintains the correct decimal scaling."]
            pub fn unchecked_ceil(&self) -> Self {
                self.checked_ceil().unwrap()
            }
        }
    };
}

unsigned_fixed!(Dec128 (IsLeq38) => 128 u128 U256);
unsigned_fixed!(Dec64 (IsLeq19) => 64 u64 U128);

pub type Decimal128 = Dec128<typenum::U18>;
pub type Uint128 = Dec128<typenum::U0>;
pub type Uint64 = Dec64<typenum::U0>;

#[cfg(test)]
mod tests {
    use super::*;
    use typenum::{U0, U18};

    // Helper functions for Decimal128 (Dec128<U18>)
    fn d128(whole: u128) -> Decimal128 {
        Decimal128::raw(whole * Decimal128::ONE.0)
    }

    fn d128_parts(whole: u128, frac: u128) -> Decimal128 {
        Decimal128::raw(whole * Decimal128::ONE.0 + frac)
    }

    // Helper functions for Uint128 (Dec128<U0>)
    fn u128_dec(val: u128) -> Uint128 {
        Uint128::raw(val)
    }

    #[test]
    fn test_constants() {
        // Test basic constants
        assert_eq!(Decimal128::ZERO.0, 0);
        assert_eq!(Decimal128::ONE.0, 10u128.pow(18));
        assert_eq!(Decimal128::MIN.0, u128::MIN);
        assert_eq!(Decimal128::MAX.0, u128::MAX);

        // Ensure ONE is properly scaled for different decimal places
        assert_eq!(Uint128::ONE.0, 1); // 0 decimal places
        assert_eq!(Dec128::<typenum::U1>::ONE.0, 10); // 1 decimal place
        assert_eq!(Decimal128::ONE.0, 10u128.pow(18)); // 18 decimal places
    }

    #[test]
    fn test_raw_construction() {
        let value = 123456789;
        let dec = Decimal128::raw(value);
        assert_eq!(dec.0, value);

        let dec_from = Decimal128::from_raw(value);
        assert_eq!(dec_from.0, value);
    }

    #[test]
    fn test_byte_conversions() {
        let value = d128(12345);

        let be_bytes = value.to_be_bytes();
        let le_bytes = value.to_le_bytes();

        assert_eq!(Decimal128::from_be_bytes(be_bytes), value);
        assert_eq!(Decimal128::from_le_bytes(le_bytes), value);
    }

    #[test]
    fn test_zero() {
        let zero = Decimal128::ZERO;
        assert!(zero.is_zero());
        assert!(!d128(1).is_zero());
    }

    #[test]
    fn test_checked_arithmetic() {
        let a = d128(100);
        let b = d128(50);

        // Basic arithmetic
        assert_eq!(a.checked_add(b).unwrap(), d128(150));
        assert_eq!(a.checked_sub(b).unwrap(), d128(50));
        assert_eq!(a.checked_mul(b).unwrap(), d128(5000));
        assert_eq!(a.checked_div(b).unwrap(), d128(2));

        // Edge cases
        assert!(Decimal128::MAX.checked_add(d128(1)).is_none());
        assert!(Decimal128::MIN.checked_sub(d128(1)).is_none());
        assert!(d128(1).checked_div(Decimal128::ZERO).is_none());
    }

    #[test]
    fn test_fractional_arithmetic() {
        let one_half = d128_parts(0, Decimal128::ONE.0 / 2);
        let two = d128(2);

        // Test that 0.5 * 2 = 1
        assert_eq!(one_half.checked_mul(two).unwrap(), Decimal128::ONE);

        // Test that 1 / 2 = 0.5
        assert_eq!(Decimal128::ONE.checked_div(two).unwrap(), one_half);
    }

    #[test]
    fn test_saturating_arithmetic() {
        let max = Decimal128::MAX;
        let one = Decimal128::ONE;
        let min = Decimal128::ZERO; // For unsigned types, MIN is 0

        // Test saturation at upper bound
        assert_eq!(max.saturating_add(one), max);

        // Test saturation at lower bound
        assert_eq!(min.saturating_sub(one), min);
    }

    #[test]
    fn test_abs_diff() {
        let a = d128(100);
        let b = d128(50);

        assert_eq!(a.abs_diff(b), d128(50));
        assert_eq!(b.abs_diff(a), d128(50));
    }

    #[test]
    fn test_comparison() {
        let a = d128(100);
        let b = d128(50);
        let c = d128(100);

        assert!(a > b);
        assert!(b < a);
        assert_eq!(a, c);
        assert!(a >= c);
        assert!(a <= c);
    }

    #[test]
    fn test_mul_ratio() {
        let base = d128(100);
        let num = d128(3);
        let den = d128(4);

        // Test that 100 * (3/4) = 75
        assert_eq!(base.mul_ratio(num, den).unwrap(), d128(75));

        // Test division by zero
        assert!(base.mul_ratio(num, Decimal128::ZERO).is_none());
    }

    #[test]
    fn test_zero_type_operations() {
        // Test operations specific to Zero digit type (Uint128)
        let a = u128_dec(4);
        let b = u128_dec(2);

        assert_eq!(a.checked_shl(1).unwrap(), u128_dec(8));
        assert_eq!(a.checked_shr(1).unwrap(), u128_dec(2));

        // Test overflow cases
        assert!(a.checked_shl(128).is_none());
        assert!(a.checked_shr(128).is_none());
    }

    #[test]
    fn test_non_zero_type_operations() {
        // Test operations specific to NonZero digit type (Decimal128)
        let two = d128(2);
        let one_half = d128_parts(0, Decimal128::ONE.0 / 2);

        // Test reciprocal
        assert_eq!(two.reciprocal().unwrap(), one_half);
        assert_eq!(Decimal128::ONE.reciprocal().unwrap(), Decimal128::ONE);
        assert!(Decimal128::ZERO.reciprocal().is_none());

        // Test floor and ceil
        let val = d128_parts(3, Decimal128::ONE.0 / 2); // 3.5
        assert_eq!(val.floor(), d128(3));
        assert_eq!(val.checked_ceil().unwrap(), d128(4));
        assert_eq!(val.unchecked_ceil(), d128(4));

        // Test exact values
        let exact = d128(5);
        assert_eq!(exact.floor(), exact);
        assert_eq!(exact.checked_ceil().unwrap(), exact);
    }

    #[test]
    fn test_precision_loss() {
        // Test that multiplying two numbers with 18 decimal places
        // correctly handles the 36 decimal places of precision
        let small = d128_parts(0, 1); // Smallest possible positive value
        let result = small.checked_mul(small).unwrap();
        assert_eq!(result.0, 0); // Should round to zero due to precision loss
    }

    #[test]
    fn test_large_values() {
        let large = d128(u64::MAX as u128);
        let larger = d128((u64::MAX as u128) * 2);

        assert!(larger.checked_mul(d128(2)).is_some());
        assert!(larger.checked_mul(d128(u64::MAX as u128)).is_none());
    }

    #[test]
    #[should_panic]
    fn test_unchecked_ceil_panic() {
        let almost_max = Decimal128::from_raw(u128::MAX - 1);
        let _ = almost_max.unchecked_ceil(); // Should panic
    }

    // Tests for unimplemented functions (todo!())
    // These tests document the expected behavior when implemented

    #[test]
    #[should_panic]
    fn test_checked_pow() {
        let base = d128(2);
        let _ = base.checked_pow(3); // Currently panics with todo!()

        // Expected behavior when implemented:
        // assert_eq!(base.checked_pow(2).unwrap(), d128(4));
        // assert_eq!(base.checked_pow(0).unwrap(), d128(1));
        // assert!(base.checked_pow(128).is_none());  // Overflow
    }

    #[test]
    #[should_panic]
    fn test_saturating_mul() {
        let a = d128(100);
        let b = d128(2);
        let _ = a.saturating_mul(b); // Currently panics with todo!()

        // Expected behavior when implemented:
        // assert_eq!(a.saturating_mul(b), d128(200));
        // assert_eq!(Decimal128::MAX.saturating_mul(d128(2)), Decimal128::MAX);
    }
}
