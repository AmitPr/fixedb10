mod util;
use std::marker::PhantomData;

use bnum::types::{U128, U256};
use typenum::{NonZero, Zero};
use util::*;

mod private {
    pub trait HelperTrait {
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
//         match <Self as private::HelperTrait>::Doubled::from_be_slice(&$var.to_be_bytes()) {
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
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
        pub struct $name<Digits: $digit_trait>($underlying, PhantomData<Digits>);

        impl<Digits: $digit_trait> private::HelperTrait for $name<Digits> {
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
            pub const MIN: Self = <Self as private::HelperTrait>::MIN_H;
            pub const MAX: Self = <Self as private::HelperTrait>::MAX_H;
            pub const ZERO: Self = <Self as private::HelperTrait>::ZERO_H;
            pub const ONE: Self = <Self as private::HelperTrait>::FRACTIONAL_H;

            pub const fn raw(value: $underlying) -> Self {
                Self(value, PhantomData)
            }

            pub fn from_raw(value: impl Into<$underlying>) -> Self {
                Self(value.into(), PhantomData)
            }

            pub const fn to_be_bytes(self) -> [u8; { $bits / 8 }] {
                self.0.to_be_bytes()
            }

            pub const fn to_le_bytes(self) -> [u8; { $bits / 8 }] {
                self.0.to_le_bytes()
            }

            pub const fn from_be_bytes(bytes: [u8; { $bits / 8 }]) -> Self {
                Self(
                    <Self as private::HelperTrait>::Underlying::from_be_bytes(bytes),
                    PhantomData,
                )
            }

            pub const fn from_le_bytes(bytes: [u8; { $bits / 8 }]) -> Self {
                Self(
                    <Self as private::HelperTrait>::Underlying::from_le_bytes(bytes),
                    PhantomData,
                )
            }

            pub const fn is_zero(&self) -> bool {
                self.0 == 0
            }

            fn full_mul(&self, other: Self) -> <Self as private::HelperTrait>::Doubled {
                <Self as private::HelperTrait>::Doubled::from(self.0)
                    * <Self as private::HelperTrait>::Doubled::from(other.0)
            }

            pub fn mul_ratio(&self, num: Self, den: Self) -> Option<Self> {
                // Perform multiplication first, then division to maintain precision
                self.full_mul(num)
                    .checked_div(den.0.into())
                    .and_then(|v| v.try_into().ok())
                    .map(|v| Self(v, PhantomData))
            }

            pub const fn checked_add(&self, other: Self) -> Option<Self> {
                map_const!(self.0.checked_add(other.0), v => Self(v, PhantomData))
            }

            pub fn checked_sub(&self, other: Self) -> Option<Self> {
                map_const!(self.0.checked_sub(other.0), v => Self(v, PhantomData))
            }

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

            pub const fn checked_div(&self, other: Self) -> Option<Self> {
                map_const!(self.0.checked_div(other.0), v => Self(v, PhantomData))
            }

            pub fn checked_pow(&self, exp: u32) -> Option<Self> {
                // d = x * (10 ** DIGITS)
                // d ^ n = x ^ n * (10 ** (DIGITS * n)) -> Not what we want!
                // (d/(10 ** DIGITS)) ^ n = x ^ n -> This is what we want, but without loss of precision
                todo!()
            }

            pub const fn saturating_add(&self, other: Self) -> Self {
                Self(self.0.saturating_add(other.0), PhantomData)
            }

            pub const fn saturating_sub(&self, other: Self) -> Self {
                Self(self.0.saturating_sub(other.0), PhantomData)
            }

            pub fn saturating_mul(&self, other: Self) -> Self {
                todo!()
            }

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

            pub fn max(&self, other: Self) -> Self {
                Self(self.0.max(other.0), PhantomData)
            }

            pub fn min(&self, other: Self) -> Self {
                Self(self.0.min(other.0), PhantomData)
            }
        }

        impl<Digits: $digit_trait> $name<Digits>
        where
            Digits: Zero,
        {
            pub const fn checked_shl(&self, exp: u32) -> Option<Self> {
                map_const!(self.0.checked_shl(exp), v => Self(v, PhantomData))
            }

            pub const fn checked_shr(&self, exp: u32) -> Option<Self> {
                map_const!(self.0.checked_shr(exp), v => Self(v, PhantomData))
            }
        }

        impl<Digits: $digit_trait> $name<Digits>
        where
            Digits: NonZero,
        {
            pub const fn reciprocal(&self) -> Option<Self> {
                if self.is_zero() {
                    None
                } else {
                    // If self=p/q, Find a/b = q/p s.t. b = Self::ONE
                    // a = (q*b)/p = (Self::ONE * Self::ONE) / p
                    Some(Self(
                        <Self as private::HelperTrait>::FRACTIONAL_SQ_H.0 / self.0,
                        PhantomData,
                    ))
                }
            }

            pub fn floor(&self) -> Self {
                // Never fails, we divide by denominator 1 and then multiply by 1
                self.checked_div(<Self as private::HelperTrait>::FRACTIONAL_H)
                    .and_then(|v| v.checked_mul(<Self as private::HelperTrait>::FRACTIONAL_H))
                    .unwrap()
            }

            pub fn checked_ceil(&self) -> Option<Self> {
                let floor = self.floor();
                if self.0 == floor.0 {
                    Some(floor)
                } else {
                    floor.checked_add(Self::ONE)
                }
            }

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
