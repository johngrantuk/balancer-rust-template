use std::error::Error;
use std::fmt::{Display, Formatter};
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::num::ParseIntError;
pub use alloy_primitives::{address, Address};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use serde::de::Visitor;
use serde_with::de::DeserializeAsWrap;
use serde_with::ser::SerializeAsWrap;
use serde_with::{serde_as, DeserializeAs, SerializeAs};
use alloy_primitives::{U256, U512};
use std::fmt::Debug;
use std::hash::{Hash, Hasher};

use crate::barter_lib::i256::{pow10_i128, I256};
use crate::barter_lib::safe_math::SafeMath;
use crate::barter_lib::u256::{pow10_u256, u256_from_u128, u256_to_f64_lossy};
use crate::{i256const, su256const};
use crate::barter_lib::{safe_math};

pub const SU256_ZERO: SafeU256 = u256_from_u128(0);
pub const SU256_ONE: SafeU256 = u256_from_u128(1);
pub const SU256_TEN: SafeU256 = u256_from_u128(10);
pub const SU256_E18: SafeU256 = pow10_u256(18);
pub const U256_ZERO: U256 = SU256_ZERO.0;
pub const U256_ONE: U256 = SU256_ONE.0;
pub const U256_TEN: U256 = SU256_TEN.0;
pub const U256_E18: U256 = SU256_E18.0;
pub const I256_E18: I256 = i256const!(pow10_i128(18));

pub const EEE: Address = address!("0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee");

pub const fn is_eth(addr: Address) -> bool {
    match addr {
        Address::ZERO => true,
        EEE => true,
        _ => false,
    }
}

#[repr(transparent)]
#[serde_as]
#[derive(
    Serialize, Deserialize, Clone, Copy, PartialEq, Eq, Hash, Default, PartialOrd, Ord,
    derive_more::From, derive_more::Into,
    derive_more::BitAnd, derive_more::BitAndAssign, derive_more::BitOr, derive_more::BitOrAssign, derive_more::BitXor, derive_more::BitXorAssign, derive_more::Not,
    derive_more::Display,
)]
pub struct SafeU256(#[serde_as(as = "crate::barter_lib::common::NiceSerializer<alloy_primitives::U256>")] pub alloy_primitives::U256);

impl<T: Into<SafeU256>> std::ops::Rem<T> for SafeU256 {
    type Output = Self;

    fn rem(self, rhs: T) -> Self::Output {
        Self(self.0 % rhs.into().0)
    }
}

impl<T: Into<SafeU256>> std::ops::RemAssign<T> for SafeU256 {
    fn rem_assign(&mut self, rhs: T) {
        self.0 %= rhs.into().0;
    }
}

impl<T: Into<SafeU256>> std::ops::Shl<T> for SafeU256 {
    type Output = Self;

    fn shl(self, rhs: T) -> Self::Output {
        Self(self.0 << rhs.into().0)
    }
}

impl<T: Into<SafeU256>> std::ops::ShlAssign<T> for SafeU256 {
    fn shl_assign(&mut self, rhs: T) {
        self.0 <<= rhs.into().0;
    }
}

impl<T: Into<SafeU256>> std::ops::Shr<T> for SafeU256 {
    type Output = Self;

    fn shr(self, rhs: T) -> Self::Output {
        Self(self.0 >> rhs.into().0)
    }
}

impl<T: Into<SafeU256>> std::ops::ShrAssign<T> for SafeU256 {
    fn shr_assign(&mut self, rhs: T) {
        self.0 >>= rhs.into().0;
    }
}

impl SafeU256 {
    pub const MAX: Self = Self(alloy_primitives::U256::MAX);

    pub fn checked_add(self, other: Self) -> Option<Self> {
        self.0.checked_add(other.0).map(Self)
    }

    pub fn checked_sub(self, other: Self) -> Option<Self> {
        self.0.checked_sub(other.0).map(Self)
    }

    pub fn checked_mul(self, other: Self) -> Option<Self> {
        self.0.checked_mul(other.0).map(Self)
    }

    pub fn checked_div(self, other: Self) -> Option<Self> {
        self.0.checked_div(other.0).map(Self)
    }

    pub fn overflowing_add(self, other: Self) -> (Self, bool) {
        let (result, overflow) = self.0.overflowing_add(other.0);
        (Self(result), overflow)
    }

    pub fn overflowing_sub(self, other: Self) -> (Self, bool) {
        let (result, overflow) = self.0.overflowing_sub(other.0);
        (Self(result), overflow)
    }

    pub fn overflowing_mul(self, other: Self) -> (Self, bool) {
        let (result, overflow) = self.0.overflowing_mul(other.0);
        (Self(result), overflow)
    }

    // TODO: Make pow not panic on overflow
    pub fn pow(self, exp: impl Into<Self>) -> Self {
        Self(self.0.checked_pow(exp.into().0).unwrap())
    }

    pub const fn zero() -> Self {
        Self(alloy_primitives::U256::ZERO)
    }

    pub const fn is_zero(&self) -> bool {
        match self.0 {
            alloy_primitives::U256::ZERO => true,
            _ => false,
        }
    }

    pub fn exp10(n: impl Into<Self>) -> Self {
        su256const!(10).pow(n)
    }

    // TODO: remove this function
    pub fn from_dec_str(s: &str) -> Result<Self, ()> {
        Ok(Self(s.parse().unwrap()))
    }

    pub const fn one() -> Self {
        Self(alloy_primitives::U256::ONE)
    }

    pub fn as_u32(&self) -> u32 {
        self.0.to()
    }

    pub fn as_u64(&self) -> u64 {
        self.0.to()
    }

    pub fn as_u128(&self) -> u128 {
        self.0.to()
    }

    pub const fn bit(&self, index: usize) -> bool {
        self.0.bit(index)
    }

    pub const fn low_u128(&self) -> u128 {
        let [lo, hi, _, _] = self.0.into_limbs();
        (lo as u128) | ((hi as u128) << 64)
    }

    pub fn as_usize(&self) -> usize {
        self.as_u64().try_into().unwrap()
    }

    pub fn from_big_endian(bytes: &[u8]) -> Self {
        Self(U256::from_be_slice(bytes))
    }

    pub fn to_f64_lossy(&self) -> f64 {
        u256_to_f64_lossy(self.0)
    }
}

impl From<&SafeU256> for alloy_primitives::U256 {
    fn from(v: &SafeU256) -> Self {
        v.0
    }
}

impl From<SafeU256> for U512 {
    fn from(v: SafeU256) -> Self {
        v.0.to()
    }
}

impl TryFrom<U512> for SafeU256 {
    type Error = alloy_primitives::ruint::FromUintError<U256>;

    fn try_from(value: U512) -> Result<Self, Self::Error> {
        use alloy_primitives::ruint::UintTryTo;
        Ok(Self(value.uint_try_to()?))
    }
}

macro_rules! declare_conv {
    ($($t:ty),*) => {
        $(
            impl From<$t> for SafeU256 {
                fn from(v: $t) -> Self {
                    Self(alloy_primitives::U256::from(v))
                }
            }

            impl TryInto<$t> for SafeU256 {
                type Error = <alloy_primitives::U256 as TryInto<$t>>::Error;

                fn try_into(self) -> Result<$t, Self::Error> {
                    self.0.try_into()
                }
            }
        )*
    };
}

declare_conv!(u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, usize, isize);

impl<T: Into<SafeU256>> std::ops::Add<T> for SafeU256 {
    type Output = safe_math::SafeMathResult<Self>;

    fn add(self, rhs: T) -> Self::Output {
        safe_math::MathResult(Ok(self.sm_add(rhs.into())?))
    }
}

impl<T: Into<SafeU256>> std::ops::Sub<T> for SafeU256 {
    type Output = safe_math::SafeMathResult<Self>;

    fn sub(self, rhs: T) -> Self::Output {
        safe_math::MathResult(Ok(self.sm_sub(rhs.into())?))
    }
}

impl<T: Into<SafeU256>> std::ops::Mul<T> for SafeU256 {
    type Output = safe_math::SafeMathResult<Self>;

    fn mul(self, rhs: T) -> Self::Output {
        safe_math::MathResult(Ok(self.sm_mul(rhs.into())?))
    }
}

impl<T: Into<SafeU256>> std::ops::Div<T> for SafeU256 {
    type Output = safe_math::SafeMathResult<Self>;

    fn div(self, rhs: T) -> Self::Output {
        safe_math::MathResult(Ok(self.sm_div(rhs.into())?))
    }
}

impl From<&SafeU256> for SafeU256 {
    fn from(v: &SafeU256) -> Self {
        *v
    }
}

impl<T: Into<SafeU256>> std::ops::Add<safe_math::SafeMathResult<T>> for SafeU256 {
    type Output = safe_math::SafeMathResult<Self>;

    fn add(self, rhs: safe_math::SafeMathResult<T>) -> Self::Output {
        safe_math::MathResult(Ok((self + rhs?)?))
    }
}

impl<T: Into<SafeU256>> std::ops::Sub<safe_math::SafeMathResult<T>> for SafeU256 {
    type Output = safe_math::SafeMathResult<Self>;

    fn sub(self, rhs: safe_math::SafeMathResult<T>) -> Self::Output {
        safe_math::MathResult(Ok((self - rhs?)?))
    }
}

impl<T: Into<SafeU256>> std::ops::Mul<safe_math::SafeMathResult<T>> for SafeU256 {
    type Output = safe_math::SafeMathResult<Self>;

    fn mul(self, rhs: safe_math::SafeMathResult<T>) -> Self::Output {
        safe_math::MathResult(Ok((self * rhs?)?))
    }
}

impl<T: Into<SafeU256>> std::ops::Div<safe_math::SafeMathResult<T>> for SafeU256 {
    type Output = safe_math::SafeMathResult<Self>;

    fn div(self, rhs: safe_math::SafeMathResult<T>) -> Self::Output {
        safe_math::MathResult(Ok((self / rhs?)?))
    }
}

// impl SafeMath<$name> for SafeMathResult<$name> {

impl<T: Into<SafeU256>> std::ops::Add<T> for safe_math::SafeMathResult<SafeU256> {
    type Output = safe_math::SafeMathResult<SafeU256>;

    fn add(self, rhs: T) -> Self::Output {
        safe_math::MathResult(Ok((self? + rhs.into())?))
    }
}

impl<T: Into<SafeU256>> std::ops::Sub<T> for safe_math::SafeMathResult<SafeU256> {
    type Output = safe_math::SafeMathResult<SafeU256>;

    fn sub(self, rhs: T) -> Self::Output {
        safe_math::MathResult(Ok((self? - rhs.into())?))
    }
}

impl<T: Into<SafeU256>> std::ops::Mul<T> for safe_math::SafeMathResult<SafeU256> {
    type Output = safe_math::SafeMathResult<SafeU256>;

    fn mul(self, rhs: T) -> Self::Output {
        safe_math::MathResult(Ok((self? * rhs.into())?))
    }
}

impl<T: Into<SafeU256>> std::ops::Div<T> for safe_math::SafeMathResult<SafeU256> {
    type Output = safe_math::SafeMathResult<SafeU256>;

    fn div(self, rhs: T) -> Self::Output {
        safe_math::MathResult(Ok((self? / rhs.into())?))
    }
}

// impl SafeMath for SafeMathResult<$name> {

impl std::ops::Add<safe_math::SafeMathResult<SafeU256>> for safe_math::SafeMathResult<SafeU256> {
    type Output = safe_math::SafeMathResult<SafeU256>;

    fn add(self, rhs: safe_math::SafeMathResult<SafeU256>) -> Self::Output {
        safe_math::MathResult(Ok((self? + rhs?)?))
    }
}

impl std::ops::Sub<safe_math::SafeMathResult<SafeU256>> for safe_math::SafeMathResult<SafeU256> {
    type Output = safe_math::SafeMathResult<SafeU256>;

    fn sub(self, rhs: safe_math::SafeMathResult<SafeU256>) -> Self::Output {
        safe_math::MathResult(Ok((self? - rhs?)?))
    }
}

impl std::ops::Mul<safe_math::SafeMathResult<SafeU256>> for safe_math::SafeMathResult<SafeU256> {
    type Output = safe_math::SafeMathResult<SafeU256>;

    fn mul(self, rhs: safe_math::SafeMathResult<SafeU256>) -> Self::Output {
        safe_math::MathResult(Ok((self? * rhs?)?))
    }
}

impl std::ops::Div<safe_math::SafeMathResult<SafeU256>> for safe_math::SafeMathResult<SafeU256> {
    type Output = safe_math::SafeMathResult<SafeU256>;

    fn div(self, rhs: safe_math::SafeMathResult<SafeU256>) -> Self::Output {
        safe_math::MathResult(Ok((self? / rhs?)?))
    }
}

impl std::fmt::Debug for SafeU256 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Copy, Clone)]
pub enum CollectArrayError {
    TooFewElements,
    TooManyElements,
}

pub trait CollectArray<T, const N: usize> {
    fn try_collect(self) -> Result<[T; N], CollectArrayError>;
}

impl<I: Iterator<Item = T>, T, const N: usize> CollectArray<T, N> for I
// add Copy bound because code is not drop-safe
where
    T: Copy,
{
    fn try_collect(self) -> Result<[T; N], CollectArrayError> {
        let mut result: [MaybeUninit<T>; N] = [MaybeUninit::uninit(); N];
        let mut max_idx = 0;
        for i in self {
            if max_idx >= N {
                return Err(CollectArrayError::TooManyElements);
            }
            result[max_idx] = MaybeUninit::new(i);
            max_idx += 1;
        }
        if max_idx < N {
            return Err(CollectArrayError::TooFewElements);
        }

        Ok(unsafe { MaybeUninit::array_assume_init(result) })
    }
}

#[repr(transparent)]
#[derive(Debug, Default, Eq, PartialEq, Hash, Clone)]
pub struct NiceSerializer<T>(pub T);

pub trait FromStrRadix: Sized {
    type FromStrRadixErr: std::fmt::Display;
    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr>;
}

macro_rules! generate_from_str_impl {
    ($selfty:ty, $errty:ty) => {
        impl FromStrRadix for $selfty {
            type FromStrRadixErr = $errty;

            fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
                <$selfty>::from_str_radix(str, radix as _)
            }
        }

        #[cfg(test)]
        paste::paste! {
            #[test]
            fn [<to_string_generates_decimal_ $selfty:lower>]() {
                let value = $selfty::from(12 as u8);
                assert_eq!(value.to_string(), "12");
            }
        }
    };
}

impl<T: ToString> Serialize for NiceSerializer<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
    {
        serializer.serialize_str(&self.0.to_string())
    }
}

impl<'de, T: FromStrRadix + TryFrom<u64>> Deserialize<'de> for NiceSerializer<T>
    where
        <T as TryFrom<u64>>::Error: Display,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
    {
        struct NiceSerializerVisitor<T>(PhantomData<T>);

        impl<T: FromStrRadix + TryFrom<u64>> Visitor<'_> for NiceSerializerVisitor<T>
            where
                <T as TryFrom<u64>>::Error: Display,
        {
            type Value = NiceSerializer<T>;

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter.write_str("Hex-string or dec string or number")
            }

            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
                where
                    E: serde::de::Error,
            {
                let value = if v.starts_with("0x") && v.len() > 2 {
                    T::from_str_radix(&v[2..], 16).map_err(serde::de::Error::custom)?
                } else {
                    T::from_str_radix(v, 10).map_err(serde::de::Error::custom)?
                };
                Ok(NiceSerializer(value))
            }

            fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
                where
                    E: serde::de::Error,
            {
                T::try_from(v).map_err(serde::de::Error::custom).map(NiceSerializer)
            }
        }

        deserializer.deserialize_any(NiceSerializerVisitor(PhantomData {}))
    }
}

impl<'de, T: FromStrRadix + TryFrom<u64>> DeserializeAs<'de, T> for NiceSerializer<T> where T::Error: Display{
    fn deserialize_as<D>(deserializer: D) -> Result<T, D::Error> where D: Deserializer<'de> {
        let NiceSerializer(value) = NiceSerializer::deserialize(deserializer)?;
        Ok(value)
    }
}

impl<T> SerializeAs<T> for NiceSerializer<T>
where
    T: Display,
{
    fn serialize_as<S>(source: &T, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.collect_str(source)
    }
}


generate_from_str_impl!(U256, alloy_primitives::ruint::ParseError);
generate_from_str_impl!(i128, ParseIntError);
generate_from_str_impl!(u128, ParseIntError);
generate_from_str_impl!(i64, ParseIntError);
generate_from_str_impl!(u64, ParseIntError);
// TODO: pass anything less than u64 as numbers since it's safe to do in JS.
// But removing following implementation breaks test assets though so need to
// consolidate them beforehand
generate_from_str_impl!(i32, ParseIntError);
generate_from_str_impl!(i16, ParseIntError);
generate_from_str_impl!(u32, ParseIntError);

#[derive(Debug, Deserialize, Serialize, Default, Clone)]
#[serde(deny_unknown_fields)]
pub struct Batched<T, U> {
    pub items: Vec<T>,
    pub meta: U,
}


#[derive(Debug)]
pub enum ParseUnitsError {
    ParseFloat(core::num::ParseFloatError, u8, String),
    FromDecStr(alloy_primitives::ruint::ParseError, u8, String),
    PrecisionLoss(String)
}

pub fn parse_units(value: &str, decimals: u8) -> Result<SafeU256, ParseUnitsError> {
    use std::ops::Mul;

    // special case if value is written in scientific notation
    if value.contains('e') || value.contains('E') {
        let float: f64 = value.parse().map_err(|e| ParseUnitsError::ParseFloat(e, decimals, value.to_string()))?;
        let float = float * 10f64.powi(decimals as i32);
        Ok(U256::from(float as u128).into())
    } else {
        let dot_index = value.find('.');
        let Some(dot_index) = dot_index else {
            return Ok(value.parse::<U256>().map_err(|e| ParseUnitsError::FromDecStr(e, decimals, value.to_string()))?.mul(SafeU256::exp10(decimals).0).into());
        };
        let (integer, fractional) = value.split_at(dot_index);
        let integer = integer.parse::<U256>().map_err(|e| ParseUnitsError::FromDecStr(e, decimals, value.to_string()))?.mul(SafeU256::exp10(decimals).0);
        let fractional = &fractional[1..];
        let mut fract = fractional.parse::<U256>().map_err(|e| ParseUnitsError::FromDecStr(e, decimals, value.to_string()))?;
        if fractional.len() < decimals as usize {
            fract *= SafeU256::exp10(decimals - fractional.len() as u8).0;
        } else {
            let diff = fractional.len() - decimals as usize;
            // 10**75 is the max, so leave 25 for the integer part, that gives us 50 digits of precision
            if diff > 50 {
                return Err(ParseUnitsError::PrecisionLoss(value.to_string()));
            }
            fract /= SafeU256::exp10(diff).0;
        }

        Ok((integer + fract).into())
    }
}

pub mod arrays {
    use std::{convert::TryInto, marker::PhantomData};

    use serde::{
        de::{SeqAccess, Visitor},
        ser::SerializeTuple,
        Deserialize, Deserializer, Serialize, Serializer,
    };
    pub fn serialize<S: Serializer, T: Serialize, const N: usize>(
        data: &[T; N],
        ser: S,
    ) -> Result<S::Ok, S::Error> {
        let mut s = ser.serialize_tuple(N)?;
        for item in data {
            s.serialize_element(item)?;
        }
        s.end()
    }

    struct ArrayVisitor<T, const N: usize>(PhantomData<T>);

    impl<'de, T, const N: usize> Visitor<'de> for ArrayVisitor<T, N>
    where
        T: Deserialize<'de>,
    {
        type Value = [T; N];

        fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
            formatter.write_str(&format!("an array of length {}", N))
        }

        #[inline]
        fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            // can be optimized using MaybeUninit
            let mut data = Vec::with_capacity(N);
            for _ in 0..N {
                match (seq.next_element())? {
                    Some(val) => data.push(val),
                    None => return Err(serde::de::Error::invalid_length(N, &self)),
                }
            }
            match data.try_into() {
                Ok(arr) => Ok(arr),
                Err(_) => unreachable!(),
            }
        }
    }
    pub fn deserialize<'de, D, T, const N: usize>(deserializer: D) -> Result<[T; N], D::Error>
    where
        D: Deserializer<'de>,
        T: Deserialize<'de>,
    {
        deserializer.deserialize_tuple(N, ArrayVisitor::<T, N>(PhantomData))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_units_works() {
        assert_eq!(parse_units("1", 18).unwrap(), 1000000000000000000_u64.into());
        assert_eq!(parse_units("1.0", 18).unwrap(), 1000000000000000000_u64.into());
        assert_eq!(parse_units("1.123", 4).unwrap(), 11230_u64.into());
        assert_eq!(parse_units("1.123456", 4).unwrap(), 11234_u64.into());
        assert_eq!(parse_units("0.12345", 4).unwrap(), 1234_u64.into());
        assert_eq!(parse_units("0.123", 4).unwrap(), 1230_u64.into());
        assert_eq!(parse_units("1e-8", 18).unwrap(), 10000000000_u64.into());
    }

    #[test]
    fn test_checksum() {
        assert_eq!(address!("0xe0fc04fa2d34a66b779fd5cee748268032a146c0").to_checksum(None), "0xe0FC04FA2d34a66B779fd5CEe748268032a146c0");
        assert_eq!(address!("0x98a7F18d4E56Cfe84E3D081B40001B3d5bD3eB8B").to_checksum(None), "0x98a7F18d4E56Cfe84E3D081B40001B3d5bD3eB8B");
    }
}

#[derive(Debug, derive_more::From)]
pub struct StatusCode(pub reqwest::StatusCode);

impl Display for StatusCode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl Serialize for StatusCode {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer {
        serializer.serialize_u16(self.0.as_u16())
    }
}

#[derive(Debug, thiserror::Error, Serialize)]
pub enum JsonLegitError {
    #[error("Unexpected reqwest error on url `{url}`: {error:?}")]
    Reqwest {
        url: String,
        error: SerializeableError<reqwest::Error>,
    },
    #[error("Json is not legit on url `{url}`: {serde_error:?} (status = {status_code}, response = \"{response}\"")]
    Json {
        url: String,
        serde_error: SerdeError<SerializeableError<serde_json::Error>>,
        status_code: StatusCode,
        response: DisplayPrint<String>,
    },
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Default, PartialOrd, Ord, derive_more::From)]
pub struct DisplayPrint<T>(pub T);

impl<T: Display> Display for DisplayPrint<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: Error> Error for DisplayPrint<T> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.0.source()
    }
}

impl<T: Display> Debug for DisplayPrint<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<T: Display> Serialize for DisplayPrint<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer {
        serializer.collect_str(&self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, PartialOrd, Ord, derive_more::From)]
pub struct SerializeableError<T>(pub T);

impl<T: Debug> Serialize for SerializeableError<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer {
        serializer.collect_str(
            &format!("{:?}", self.0)
        )
    }
}


pub trait JsonLegit {
    type Future<T: for<'a> Deserialize<'a>>: std::future::Future<Output = Result<T, JsonLegitError>>;

    fn json_legit<T: for<'a> Deserialize<'a>>(self) -> Self::Future<T>;
}

impl JsonLegit for reqwest::Response {
    type Future<T: for<'a> Deserialize<'a>> = impl std::future::Future<Output = Result<T, JsonLegitError>>;

    fn json_legit<T: for<'a> Deserialize<'a>>(self) -> Self::Future<T> {
        let status_code = self.status();
        let url = self.url().to_string();
        async move {
            let response = match self.text().await {
                Ok(x) => x,
                Err(e) => {
                    return Err(JsonLegitError::Reqwest { url, error: SerializeableError(e) })
                }
            };

            deserialize_item(&response)
                .map_err(|serde_error| JsonLegitError::Json {
                    url,
                    serde_error: SerdeError {
                        path: serde_error.path,
                        original: SerializeableError(serde_error.original),
                    },
                    status_code: StatusCode(status_code),
                    response: DisplayPrint(response),
                })
        }
    }
}

#[derive(Debug, Serialize, Deserialize, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum ExecutorType {
    SwapExecutor,
    Cow,
}

impl From<ExecutorType> for u8 {
    fn from(e: ExecutorType) -> u8 {
        e as u8
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct SerdeError<E> {
    pub path: String,
    pub original: E,
}

pub fn deserialize_item<'a, T>(value: &'a str) -> Result<T, SerdeError<serde_json::Error>>
where
    T: serde::de::Deserialize<'a> {
    let mut track = serde_path_to_error::Track::new();
    let mut deserializer = serde_json::Deserializer::from_str(value);
    match T::deserialize(serde_path_to_error::Deserializer::new(&mut deserializer, &mut track)) {
        Ok(t) => Ok(t),
        Err(err) => Err(SerdeError {
            path: format_path(track.path()),
            original: err,
        }),
    }
}

fn format_path(path: serde_path_to_error::Path) -> String {
    use std::fmt::Write;

    let mut result = String::from("ROOT");
    for segment in path.iter() {
        match segment {
            serde_path_to_error::Segment::Seq { index } => {
                write!(result, "[{}]", index).unwrap();
            }
            serde_path_to_error::Segment::Map { key } => {
                write!(result, ".{}", key).unwrap();
            }
            serde_path_to_error::Segment::Enum { variant } => {
                write!(result, ".{}", variant).unwrap();
            }
            serde_path_to_error::Segment::Unknown => {
                write!(result, ".UNKNOWN").unwrap();
            }
        }
    }
    result
}

#[derive(Debug, Deserialize, Serialize, Default, Clone, Eq)]
#[serde(deny_unknown_fields)]
pub struct NonKeyMeta<T>(pub T);

impl<T> Hash for NonKeyMeta<T> {
    fn hash<H: Hasher>(&self, _: &mut H) {}
}

impl<T> PartialEq for NonKeyMeta<T> {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl<T, U: SerializeAs<T>> SerializeAs<NonKeyMeta<T>> for NonKeyMeta<U> {
    fn serialize_as<S: Serializer>(source: &NonKeyMeta<T>, serializer: S) -> Result<S::Ok, S::Error> {
        SerializeAsWrap::<T, U>::new(&source.0).serialize(serializer)
    }
}

impl<'de, T, U: DeserializeAs<'de, T>> DeserializeAs<'de, NonKeyMeta<T>> for NonKeyMeta<U> {
    fn deserialize_as<D: Deserializer<'de>>(deserializer: D) -> Result<NonKeyMeta<T>, D::Error> {
        Ok(NonKeyMeta(DeserializeAsWrap::<T, U>::deserialize(deserializer)?.into_inner()))
    }
}

pub trait Swap {
    type Error: Debug;
    fn swap(&self, amount: SafeU256) -> safe_math::MathResult<SafeU256, Self::Error>;
}