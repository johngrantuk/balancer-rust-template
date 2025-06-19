use std::{convert, fmt::Debug, ops::{self, ControlFlow}};

use crate::{barter_lib::{common::{SafeU256, SU256_ONE, SU256_ZERO}, i256::I256, u256::{u256_from_u128, u512_to_u256}}, su256const};

#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
#[allow(unused)]
pub enum SafeMathError {
    Add,
    Sub,
    Div,
    Mul,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, derive_more::From, derive_more::Into)]
#[must_use = "this `Result` may be an `Err` variant, which should be handled"]
pub struct MathResult<T, E>(pub Result<T, E>);

impl<T, E> MathResult<T, E> {
    pub const fn into_result(self) -> Result<T, E> {
        self.0
    }

    pub const fn ok(value: T) -> Self {
        MathResult(Ok(value))
    }

    pub const fn err(error: E) -> Self {
        MathResult(Err(error))
    }

    pub const fn is_ok(&self) -> bool {
        self.0.is_ok()
    }

    pub const fn is_err(&self) -> bool {
        self.0.is_err()
    }

    pub const fn into_std(self) -> Result<T, E> {
        self.0
    }

    pub fn unwrap_or_default(self) -> T
    where
        T: Default,
    {
        self.0.unwrap_or_default()
    }

    pub fn map<U, F: FnOnce(T) -> U>(self, op: F) -> MathResult<U, E> {
        MathResult(self.0.map(op))
    }

    pub fn map_err<F, O: FnOnce(E) -> F>(self, op: O) -> MathResult<T, F> {
        MathResult(self.0.map_err(op))
    }

    pub fn cast_err<F: From<E>>(self) -> MathResult<T, F> {
        self.map_err(Into::into)
    }

    pub fn and_then<U, F: FnOnce(T) -> MathResult<U, E>>(self, op: F) -> MathResult<U, E> {
        MathResult(self.0.and_then(|t| op(t).into_std()))
    }
}

impl<T: Default, E> MathResult<T, E> {
    pub fn empty() -> Self {
        MathResult(Ok(Default::default()))
    }
}

impl<T, E> From<T> for MathResult<T, E> {
    fn from(value: T) -> Self {
        MathResult(Ok(value))
    }
}

impl<T: Copy, E> From<&T> for MathResult<T, E> {
    fn from(value: &T) -> Self {
        MathResult(Ok(*value))
    }
}

pub type SafeMathResult<T> = MathResult<T, SafeMathError>;
pub type SafeMathU256Result = SafeMathResult<SafeU256>;

impl<T: Into<primitive_types::U256>> std::ops::AddAssign<T> for MathResult<SafeU256, SafeMathError> {
    fn add_assign(&mut self, rhs: T) {
        *self = *self + rhs;
    }
}

impl<T: Into<primitive_types::U256>> std::ops::SubAssign<T> for MathResult<SafeU256, SafeMathError> {
    fn sub_assign(&mut self, rhs: T) {
        *self = *self - rhs;
    }
}

impl<T: Into<primitive_types::U256>> std::ops::MulAssign<T> for MathResult<SafeU256, SafeMathError> {
    fn mul_assign(&mut self, rhs: T) {
        *self = *self * rhs;
    }
}

impl<T: Into<primitive_types::U256>> std::ops::DivAssign<T> for MathResult<SafeU256, SafeMathError> {
    fn div_assign(&mut self, rhs: T) {
        *self = *self / rhs;
    }
}

impl<T: Into<SafeU256>> std::ops::AddAssign<MathResult<T, SafeMathError>> for MathResult<SafeU256, SafeMathError> {
    fn add_assign(&mut self, rhs: MathResult<T, SafeMathError>) {
        let a = *self;
        let b = rhs.map(Into::<SafeU256>::into);
        *self = a + b;
    }
}

impl<T: Into<SafeU256>> std::ops::SubAssign<MathResult<T, SafeMathError>> for MathResult<SafeU256, SafeMathError> {
    fn sub_assign(&mut self, rhs: MathResult<T, SafeMathError>) {
        let a = *self;
        let b = rhs.map(Into::<SafeU256>::into);
        *self = a - b;
    }
}

impl<T: Into<SafeU256>> std::ops::MulAssign<MathResult<T, SafeMathError>> for MathResult<SafeU256, SafeMathError> {
    fn mul_assign(&mut self, rhs: MathResult<T, SafeMathError>) {
        let a = *self;
        let b = rhs.map(Into::<SafeU256>::into);
        *self = a * b;
    }
}

impl<T: Into<SafeU256>> std::ops::DivAssign<MathResult<T, SafeMathError>> for MathResult<SafeU256, SafeMathError> {
    fn div_assign(&mut self, rhs: MathResult<T, SafeMathError>) {
        let a = *self;
        let b = rhs.map(Into::<SafeU256>::into);
        *self = a / b;
    }
}

impl<T, E: Debug> MathResult<T, E> {
    pub fn unwrap(self) -> T {
        self.0.unwrap()
    }

    pub fn expect(self, msg: &str) -> T {
        self.0.expect(msg)
    }
}

impl<T: Debug, E> MathResult<T, E> {
    pub fn unwrap_err(self) -> E {
        self.0.unwrap_err()
    }

    pub fn expect_err(self, msg: &str) -> E {
        self.0.expect_err(msg)
    }
}

impl<T, E> ops::Try for MathResult<T, E> {
    type Output = T;
    type Residual = MathResult<convert::Infallible, E>;

    fn from_output(output: Self::Output) -> Self {
        MathResult(Ok(output))
    }

    fn branch(self) -> ControlFlow<Self::Residual, Self::Output> {
        let result = self.0.branch();
        match result {
            ControlFlow::Continue(output) => ControlFlow::Continue(output),
            ControlFlow::Break(e) => ControlFlow::Break(MathResult(e)),
        }
    }
}

impl<T, E, F: From<E>> ops::FromResidual<MathResult<convert::Infallible, E>> for MathResult<T, F> {
    #[inline]
    #[track_caller]
    fn from_residual(residual: MathResult<convert::Infallible, E>) -> Self {
        let result = ops::FromResidual::from_residual(residual.0);
        MathResult(result)
    }
}

impl<T, E, F: From<E>> ops::FromResidual<ops::Yeet<E>> for MathResult<T, F> {
    #[inline]
    fn from_residual(e: ops::Yeet<E>) -> Self {
        let result = ops::FromResidual::from_residual(e);
        MathResult(result)
    }
}

impl<T, E> ops::Residual<T> for MathResult<convert::Infallible, E> {
    type TryType = MathResult<T, E>;
}

impl<T, E, F: From<E>> ops::FromResidual<MathResult<convert::Infallible, E>> for Result<T, F>
{
    #[inline]
    fn from_residual(residual: MathResult<convert::Infallible, E>) -> Self {
        ops::FromResidual::from_residual(residual.0)
    }
}

impl<T, E, F> ops::FromResidual<Result<convert::Infallible, E>> for MathResult<T, F>
where
    F: From<E>
{
    fn from_residual(residual: Result<convert::Infallible, E>) -> Self {
        let result = ops::FromResidual::from_residual(residual);
        MathResult(result)
    }
}

impl<A, E, V: FromIterator<A>> FromIterator<MathResult<A, E>> for MathResult<V, E> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = MathResult<A, E>>>(iter: I) -> MathResult<V, E> {
        let iter = FromIterator::from_iter(iter.into_iter().map(|x| x.0));
        MathResult(iter)
    }
}

pub trait SafeMath<T=Self>: Sized {
    type Output;

    fn sm_add(self, b: T) -> Self::Output;
    fn sm_sub(self, b: T) -> Self::Output;
    fn sm_mul(self, b: T) -> Self::Output;
    fn sm_div(self, b: T) -> Self::Output;
}

macro_rules! impl_safe_math {
    (
        $($name:ty),*
    ) => {
        $(
            impl SafeMath for $name {
                type Output = SafeMathResult<Self>;

                fn sm_add(self, b: Self) -> Self::Output {
                    self.checked_add(b).ok_or(SafeMathError::Add).into()
                }

                fn sm_sub(self, b: Self) -> Self::Output {
                    self.checked_sub(b).ok_or(SafeMathError::Sub).into()
                }

                fn sm_mul(self, b: Self) -> Self::Output {
                    self.checked_mul(b).ok_or(SafeMathError::Mul).into()
                }

                fn sm_div(self, b: Self) -> Self::Output {
                    self.checked_div(b).ok_or(SafeMathError::Div).into()
                }
            }

            impl SafeMath<SafeMathResult<$name>> for $name {
                type Output = SafeMathResult<Self>;

                fn sm_add(self, b: SafeMathResult<$name>) -> Self::Output {
                    self.checked_add(b?).ok_or(SafeMathError::Add).into()
                }

                fn sm_sub(self, b: SafeMathResult<$name>) -> Self::Output {
                    self.checked_sub(b?).ok_or(SafeMathError::Sub).into()
                }

                fn sm_mul(self, b: SafeMathResult<$name>) -> Self::Output {
                    self.checked_mul(b?).ok_or(SafeMathError::Mul).into()
                }

                fn sm_div(self, b: SafeMathResult<$name>) -> Self::Output {
                    self.checked_div(b?).ok_or(SafeMathError::Div).into()
                }
            }

            impl SafeMath<$name> for SafeMathResult<$name> {
                type Output = Self;

                fn sm_add(self, b: $name) -> Self::Output {
                    self?.checked_add(b).ok_or(SafeMathError::Add).into()
                }

                fn sm_sub(self, b: $name) -> Self::Output {
                    self?.checked_sub(b).ok_or(SafeMathError::Sub).into()
                }

                fn sm_mul(self, b: $name) -> Self::Output {
                    self?.checked_mul(b).ok_or(SafeMathError::Mul).into()
                }

                fn sm_div(self, b: $name) -> Self::Output {
                    self?.checked_div(b).ok_or(SafeMathError::Div).into()
                }
            }

            impl SafeMath for SafeMathResult<$name> {
                type Output = Self;

                fn sm_add(self, b: Self) -> Self::Output {
                    self?.checked_add(b?).ok_or(SafeMathError::Add).into()
                }

                fn sm_sub(self, b: Self) -> Self::Output {
                    self?.checked_sub(b?).ok_or(SafeMathError::Sub).into()
                }

                fn sm_mul(self, b: Self) -> Self::Output {
                    self?.checked_mul(b?).ok_or(SafeMathError::Mul).into()
                }

                fn sm_div(self, b: Self) -> Self::Output {
                    self?.checked_div(b?).ok_or(SafeMathError::Div).into()
                }
            }
        )*
    }
}

impl_safe_math!(u8, u16, u32, u64, u128, primitive_types::U256, i8, i16, i32, i64, i128, I256, usize, isize, crate::barter_lib::common::SafeU256);

pub fn div_ceil(a: impl Into<SafeMathU256Result>, b: impl Into<SafeMathU256Result>) -> SafeMathU256Result {
    let a = a.into()?;
    let b = b.into()?;
    let quotient = a.sm_div(b)?;
    let remainder = a.sm_sub(quotient.sm_mul(b)?)?;
    Ok(if remainder > SU256_ZERO {
        (quotient + SU256_ONE)?
    } else {
        quotient
    }).into()
}

pub fn sqrt(x: impl Into<SafeMathU256Result>) -> SafeMathU256Result {
    let x = x.into()?;
    let mut z = ((x / const { u256_from_u128(2) }) + SU256_ONE)?;
    let mut y = x;
    while z < y {
        y = z;
        z = ((x / z + z) / const { u256_from_u128(2) })?;
    }
    MathResult(Ok(y))
}

pub fn log2(x: impl Into<SafeMathU256Result>, roundup: bool) -> SafeMathResult<SafeU256> {
    let x = x.into()?;
    let mut value = x;
    let mut result = MathResult(Ok(SU256_ZERO));

    if x >> 128 != SU256_ZERO {
        value = x >> 128;
        result = MathResult(Ok(const { u256_from_u128(128) }));
    }
    if value >> 64 != SU256_ZERO {
        value >>= 64;
        result += const { u256_from_u128(64) };
    }
    if value >> 32 != SU256_ZERO {
        value >>= 32;
        result += const { u256_from_u128(32) };
    }
    if value >> 16 != SU256_ZERO {
        value >>= 16;
        result += const { u256_from_u128(16) };
    }
    if value >> 8 != SU256_ZERO {
        value >>= 8;
        result += const { u256_from_u128(8) };
    }
    if value >> 4 != SU256_ZERO {
        value >>= 4;
        result += const { u256_from_u128(4) };
    }
    if value >> 2 != SU256_ZERO {
        value >>= 2;
        result += const { u256_from_u128(2) };
    }
    if value >> 1 != SU256_ZERO {
        result += const { u256_from_u128(1) };
    }
    if roundup && (const { u256_from_u128(1) } << result?) < x {
        result += const { u256_from_u128(1) };
    }
    result
}

// Return the result of a ** b % (2 ** 256).
pub fn pow_mod256(mut base: SafeU256, mut exponent: SafeU256) -> SafeU256 {
    let mut result = su256const!(1);
    while exponent > SU256_ZERO {
        if exponent.0.bit(0) {
            result = u512_to_u256(result.0.full_mul(base.0)).0.into();
        }
        exponent >>= 1;
        base = u512_to_u256(base.0.full_mul(base.0)).0.into();
    }
    result
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Copy, Clone)]
#[allow(unused)]
pub enum UintIntMathError {
    Overflow,
    Underflow,
}

type UintIntMathResult<T> = Result<T, UintIntMathError>;

pub trait UintIntMath: Sized {
    fn ui_add(self, b: I256) -> UintIntMathResult<Self>;
}

impl UintIntMath for SafeU256 {
    fn ui_add(self, b: I256) -> UintIntMathResult<Self> {
        if b.is_neg() {
            self.checked_sub(unsafe { primitive_types::U256::try_from(-b).unwrap_unchecked() }.into())
                .ok_or(UintIntMathError::Underflow)
        } else {
            self.checked_add(unsafe { primitive_types::U256::try_from(b).unwrap_unchecked() }.into())
                .ok_or(UintIntMathError::Overflow)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pow_mod() {
        assert_eq!(primitive_types::U256::from(1), pow_mod256(2u32.into(), 0u32.into()).into());
        assert_eq!(primitive_types::U256::from(2), pow_mod256(2u32.into(), 1u32.into()).into());
        assert_eq!(primitive_types::U256::from(8), pow_mod256(2u32.into(), 3u32.into()).into());
        assert_eq!(primitive_types::U256::from_dec_str("100000000000000000000").unwrap(), pow_mod256(100.into(), 10.into()).into());
        assert_eq!(primitive_types::U256::from_dec_str("10000000000000000000000000000000000000000000000000000000000000000000000000000").unwrap(), pow_mod256(100.into(), 38.into()).into());
        assert_eq!(primitive_types::U256::from_dec_str("73663286101470436611432119930496737173840122674875487684339327936694962880512").unwrap(), pow_mod256(100.into(), 39.into()).into());
        assert_eq!(primitive_types::U256::from_dec_str("59041770658110225754900818312084884949620587934026984283048776718299468660736").unwrap(), pow_mod256(100.into(), 100.into()).into());
    }
}
