use std::{
    cmp::Ordering,
    fmt::{
        Debug, Display, Formatter
    },
    ops::{
        Add,
        AddAssign,
        BitOr,
        BitOrAssign,
        Div,
        DivAssign,
        Mul,
        MulAssign,
        Neg,
        Not,
        Rem,
        Shl,
        ShlAssign,
        Shr,
        ShrAssign,
        Sub,
        SubAssign,
    },
};

use crate::barter_lib::{common::{SafeU256, SU256_ONE}, u256::u256_from_u128};

#[derive(Eq, PartialEq, Clone, Copy, Default)]
pub struct I256(primitive_types::U256);

impl Debug for I256 {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "I256({})", self)
    }
}

const NEG_BIT_PATTERN: primitive_types::U256 = primitive_types::U256([0, 0, 0, 1 << 63]);

impl I256 {
    pub const fn is_neg(&self) -> bool {
        self.0.bit(255)
    }

    pub fn abs(&self) -> SafeU256 {
        if self.is_neg() {
            self.neg().0
        } else {
            self.0
        }.into()
    }

    pub const fn is_zero(&self) -> bool {
        matches!(self, &Self::ZERO)
    }

    pub const ZERO: I256 = Self::from_u128(0);
    pub const ONE: I256 = Self::from_u128(1);
    pub const MAX: I256 = Self(primitive_types::U256([u64::MAX, u64::MAX, u64::MAX, u64::MAX >> 1]));
    pub const MIN: I256 = Self(NEG_BIT_PATTERN);

    pub const fn from_u256_pt(value: primitive_types::U256) -> Result<Self, U256ToI256ConversionError> {
        let result = Self(value);
        if result.is_neg() {
            Err(U256ToI256ConversionError {})
        } else {
            Ok(result)
        }
    }

    pub const fn from_u256(value: SafeU256) -> Result<Self, U256ToI256ConversionError> {
        Self::from_u256_pt(value.0)
    }

    pub const fn from_u128(value: u128) -> Self {
        Self(u256_from_u128(value).0)
    }

    pub const fn as_saturating_i32(&self) -> i32 {
        self.0 .0[0] as u32 as i32
    }
    pub const fn as_i32(&self) -> i32 {
        self.0.0[0] as u32 as i32
    }

    pub fn sqr(&self) -> Self {
        *self * *self
    }

    pub fn overflowing_add(self, rhs: Self) -> (Self, bool) {
        // rhs > 0 | result > self | overflow
        // true    | true          | false
        // true    | false         | true
        // false   | true          | true
        // false   | false         | false

        let (result, _) = self.0.overflowing_add(rhs.0);
        let result = Self(result);
        let overflow = (result > self) ^ (rhs > I256::ZERO);
        (result, overflow)
    }

    pub fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
        let (result, _) = self.0.overflowing_sub(rhs.0);
        let result = Self(result);
        let overflow = (result > self) ^ (rhs < I256::ZERO);
        (result, overflow)
    }

    pub fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
        let is_neg = self.is_neg() ^ rhs.is_neg();
        let (value, overflow) = self.abs().overflowing_mul(rhs.abs());
        let overflow = overflow || value.bit(255);
        let value = Self(value.0);
        let result = if is_neg { -value } else { value };
        (result, overflow)
    }

    pub fn unchecked_div(self, rhs: Self) -> (Self, bool) {
        if rhs.is_zero() {
            return (Self::ZERO, true);
        }
        (self / rhs, false)
    }

    pub fn checked_add(self, rhs: Self) -> Option<Self> {
        let (result, overflow) = self.overflowing_add(rhs);
        if overflow {
            None
        } else {
            Some(result)
        }
    }

    pub fn checked_sub(self, rhs: Self) -> Option<Self> {
        let (result, overflow) = self.overflowing_sub(rhs);
        if overflow {
            None
        } else {
            Some(result)
        }
    }

    pub fn checked_mul(self, rhs: Self) -> Option<Self> {
        let (result, overflow) = self.overflowing_mul(rhs);
        if overflow {
            None
        } else {
            Some(result)
        }
    }

    pub fn checked_div(self, rhs: Self) -> Option<Self> {
        let (result, overflow) = self.unchecked_div(rhs);
        if overflow {
            None
        } else {
            Some(result)
        }
    }
}

impl Display for I256 {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.is_neg() {
            write!(f, "-")?;
        }
        write!(f, "{}", self.abs())
    }
}

macro_rules! impl_from {
    ($typ:ty) => {
        impl From<$typ> for I256 {
            #[allow(unused_comparisons)]
            fn from(x: $typ) -> Self {
                let (neg, x) = if x >= 0 {
                    (false, x as u128)
                } else {
                    (true, (-(x as i128)) as u128) // TODO: handle i128::MIN (will panic
                                                   // in current impl)
                };
                let mut val = primitive_types::U256::from(x);
                if neg {
                    val = !val + $crate::barter_lib::common::SU256_ONE;
                }
                Self(val)
            }
        }

        impl From<&$typ> for I256 {
            fn from(x: &$typ) -> Self {
                Self::from(*x)
            }
        }
    };
}

pub const fn pow10_i128(val: u32) -> i128 {
    10_i128.pow(val)
}

#[doc(hidden)]
pub const fn i256_from_i128(val: i128) -> I256 {
    let [lo, hi]: [u64; 2] = unsafe { std::mem::transmute(val.to_le()) };
    let sign_bit = if val.is_negative() { u64::MAX } else { 0 };
    I256(primitive_types::U256([lo, hi, sign_bit, sign_bit]))
}

#[macro_export]
macro_rules! i256const {
    ($val:expr) => {
        const { $crate::barter_lib::i256::i256_from_i128($val) }
    };
}

impl_from!(i8);
impl_from!(i16);
impl_from!(i32);
impl_from!(i64);
impl_from!(i128);
impl_from!(u8);
impl_from!(u16);
impl_from!(u32);
impl_from!(u64);
impl_from!(u128);

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub struct I256ToU256ConversionError;

impl TryFrom<I256> for primitive_types::U256 {
    type Error = I256ToU256ConversionError;

    fn try_from(value: I256) -> Result<Self, Self::Error> {
        if value.is_neg() {
            Err(I256ToU256ConversionError {})
        } else {
            Ok(value.0)
        }
    }
}

impl TryFrom<I256> for SafeU256 {
    type Error = I256ToU256ConversionError;

    fn try_from(value: I256) -> Result<Self, Self::Error> {
        primitive_types::U256::try_from(value).map(SafeU256)
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub struct U256ToI256ConversionError;

impl TryFrom<primitive_types::U256> for I256 {
    type Error = U256ToI256ConversionError;

    fn try_from(value: primitive_types::U256) -> Result<Self, Self::Error> {
        Self::from_u256(value.into())
    }
}

impl TryFrom<SafeU256> for I256 {
    type Error = U256ToI256ConversionError;

    fn try_from(value: SafeU256) -> Result<Self, Self::Error> {
        Self::from_u256(value)
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Copy, derive_more::From)]
pub enum U256I256ConversionError {
    U256ToI256ConversionError(U256ToI256ConversionError),
    I256ToU256ConversionError(I256ToU256ConversionError),
}

impl Neg for I256 {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self((!self.0).overflowing_add(SU256_ONE.0).0)
    }
}

impl Not for I256 {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self(!self.0)
    }
}

impl Add for I256 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0.overflowing_add(rhs.0).0)
    }
}

impl AddAssign for I256 {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Sub for I256 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs)
    }
}

impl SubAssign for I256 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl Mul for I256 {
    type Output = Self;

    fn mul(mut self, rhs: Self) -> Self::Output {
        self *= rhs;
        self
    }
}

impl MulAssign for I256 {
    fn mul_assign(&mut self, rhs: Self) {
        let is_neg = self.is_neg() ^ rhs.is_neg();
        let value = Self(self.abs().0 * rhs.abs().0);
        *self = if is_neg { -value } else { value }
    }
}

impl Div for I256 {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        let is_neg = self.is_neg() ^ rhs.is_neg();
        let value = Self(self.abs().0 / rhs.abs().0);
        if is_neg {
            -value
        } else {
            value
        }
    }
}

impl DivAssign for I256 {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl Rem for I256 {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        let is_neg = self.is_neg();
        let value = Self(self.abs().0 % rhs.abs().0);
        if is_neg {
            -value
        } else {
            value
        }
    }
}

impl Shl<i32> for I256 {
    type Output = I256;

    fn shl(self, rhs: i32) -> Self::Output {
        let neg_bit = self.0 & NEG_BIT_PATTERN;
        Self(neg_bit | (self.0 << rhs)) // TODO: Not sure what should happen on
                                        // overflow
    }
}

impl ShlAssign<i32> for I256 {
    fn shl_assign(&mut self, rhs: i32) {
        *self = *self << rhs;
    }
}

impl Shr<i32> for I256 {
    type Output = I256;

    fn shr(self, rhs: i32) -> Self::Output {
        let neg_bit = self.0 & NEG_BIT_PATTERN;
        Self(neg_bit | (self.0 >> rhs)) // TODO: Not sure what should happen on
                                        // overflow
    }
}

impl ShrAssign<i32> for I256 {
    fn shr_assign(&mut self, rhs: i32) {
        *self = *self >> rhs;
    }
}

impl BitOr for I256 {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0.bitor(rhs.0))
    }
}

impl BitOrAssign for I256 {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

impl PartialOrd for I256 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for I256 {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.is_neg(), other.is_neg()) {
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
            _ => self.0.cmp(&other.0),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn neg() {
        for i in -10..10 {
            assert_eq!(I256::from(-i), -I256::from(i));
        }
    }

    #[test]
    fn not() {
        for i in -10..10 {
            assert_eq!(I256::from(!i), !I256::from(i));
        }
    }

    #[test]
    fn display() {
        assert_eq!("10", I256::from(10).to_string());
        assert_eq!("-10", I256::from(-10).to_string());
    }

    #[test]
    fn add_regular() {
        assert_eq!(I256::from(0), I256::from(0) + I256::from(0));
        assert_eq!(I256::from(1), I256::from(0) + I256::from(1));
        assert_eq!(I256::from(2), I256::from(1) + I256::from(1));
    }

    #[test]
    fn add_neg() {
        assert_eq!(I256::from(0), I256::from(-1) + I256::from(1));
        assert_eq!(I256::from(0), I256::from(-10) + I256::from(10));
        assert_eq!(I256::from(-5), I256::from(-10) + I256::from(5));
        assert_eq!(I256::from(5), I256::from(-10) + I256::from(15));
        assert_eq!(I256::from(-25), I256::from(-10) + I256::from(-15));
    }

    #[test]
    fn mul() {
        for i in -5..5 {
            for j in -6..6 {
                let expected = i * j;
                let result = I256::from(i) * I256::from(j);
                assert_eq!(
                    I256::from(expected),
                    result,
                    "{} {} ({}|{})",
                    i,
                    j,
                    expected,
                    result.abs()
                );
            }
        }
    }

    #[test]
    fn mul_neg_big() {
        let x = I256::from_u128(1000000000000000000000000000);
        let y = I256::from(-100000000000000000i64);
        assert_eq!("-100000000000000000000000000000000000000000000", (x*y).to_string());
        assert_eq!("-100000000000000000000000000000000000000000000", x.checked_mul(y).unwrap().to_string());
    }

    #[test]
    fn div() {
        for i in (-50..50).step_by(5) {
            for j in (-6..6).filter(|&x| x != 0) {
                let expected = i / j;
                let result = I256::from(i) / I256::from(j);
                assert_eq!(
                    I256::from(expected),
                    result,
                    "{} {} ({}|{})",
                    i,
                    j,
                    expected,
                    result.abs()
                );
            }
        }
    }

    #[test]
    fn rem() {
        for i in -5..5 {
            for j in (-6..6).filter(|&x| x != 0) {
                let expected = i % j;
                let result = I256::from(i) % I256::from(j);
                assert_eq!(
                    I256::from(expected),
                    result,
                    "{} {} ({}|{})",
                    i,
                    j,
                    expected,
                    result.abs()
                );
            }
        }
    }

    #[test]
    fn shl_pos() {
        for i in 0..127 {
            assert_eq!(I256::from(1_i128 << i), I256::from(1_i128) << i, "{}", i);
        }
    }

    #[test]
    fn shl_neg() {
        for i in 0..126 {
            assert_eq!(
                I256::from(-1_i128 << i),
                I256::from(-1_i128) << i,
                "\n{:x}, \n{:x}, \n{}",
                I256::from(-1_i128 << i).0,
                (I256::from(-1_i128) << i).0,
                i
            );
        }
    }

    #[test]
    fn bitor() {
        for i in -5..5 {
            for j in 10..20 {
                assert_eq!(I256::from(i | j), I256::from(i) | I256::from(j));
                assert_eq!(I256::from(i | -j), I256::from(i) | I256::from(-j))
            }
        }
        assert_eq!(
            I256::from((i128::MAX - 100) | (i128::MAX - 15)),
            I256::from(i128::MAX - 100) | I256::from(i128::MAX - 15)
        );
    }

    #[test]
    fn cmp() {
        for i in -5..5 {
            for j in -10..10 {
                assert_eq!(i.cmp(&j), I256::from(i).cmp(&I256::from(j)), "{} <> {}", i, j);
            }
        }
    }

    #[test]
    fn from_i128_const() {
        for i in -5..5 {
            let x = i256_from_i128(i);
            assert_eq!(x.to_string(), i.to_string());
        }

        for i in -5..5 {
            let i = u64::MAX as u128 as i128 + i;
            let x = i256_from_i128(i);
            assert_eq!(x.to_string(), i.to_string());
        }

        for i in -5..5 {
            let i = i - u64::MAX as u128 as i128;
            let x = i256_from_i128(i);
            assert_eq!(x.to_string(), i.to_string());
        }
    }

    #[test]
    fn checked_sub_works() {
        assert_eq!(I256::ZERO.checked_sub(100.into()), Some((-100).into()));
    }

    #[test]
    fn checked_add_neg() {
        assert_eq!(I256::from(10).checked_add(I256::from(-10)), Some(I256::ZERO));
        assert_eq!(I256::from(-10).checked_add(I256::from(10)), Some(I256::ZERO));
        assert_eq!(I256::from(-10).checked_add(I256::from(0)), Some(I256::from(-10)));
        assert_eq!(I256::from(10).checked_add(I256::from(0)), Some(I256::from(10)));
    }

    #[test]
    fn checked_sub_neg() {
        assert_eq!(I256::from(-10).checked_sub(I256::from(-10)), Some(I256::ZERO));
        assert_eq!(I256::from(-10).checked_sub(I256::from(0)), Some(I256::from(-10)));
    }
}
