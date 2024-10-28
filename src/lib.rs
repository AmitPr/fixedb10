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
            pub const fn checked_div(&self, other: Self) -> Option<Self> {
                map_const!(self.0.checked_div(other.0), v => Self(v, PhantomData))
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
                self.checked_div(<Self as _priv::Consts>::FRACTIONAL_H)
                    .and_then(|v| v.checked_mul(<Self as _priv::Consts>::FRACTIONAL_H))
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
