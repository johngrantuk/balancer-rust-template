use std::error::Error;
use std::fmt::{Display, Formatter};
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::num::ParseIntError;
use std::str::FromStr;
use arrayvec::ArrayString;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use serde::de::Visitor;
use serde_with::de::DeserializeAsWrap;
use serde_with::ser::SerializeAsWrap;
use serde_with::{serde_as, DeserializeAs, SerializeAs};
use primitive_types::{H160, U256, U512};
use std::fmt::Debug;
use std::hash::{Hash, Hasher};

use ethcontract::common::abi::Token;
use ethcontract::tokens::Tokenize;

use super::i256::{pow10_i128, I256};
use crate::barter_lib::safe_math::SafeMath;
use crate::barter_lib::u256::{parse_h256_hex, pow10_u256, u256_from_u128, ParseU256Error};
use crate::barter_lib::{safe_math, unwrap_const};
use crate::i256const;

pub const SU256_ZERO: SafeU256 = u256_from_u128(0);
pub const SU256_ONE: SafeU256 = u256_from_u128(1);
pub const SU256_TEN: SafeU256 = u256_from_u128(10);
pub const SU256_E18: SafeU256 = pow10_u256(18);
pub const U256_ZERO: primitive_types::U256 = SU256_ZERO.0;
pub const U256_ONE: primitive_types::U256 = SU256_ONE.0;
pub const U256_TEN: primitive_types::U256 = SU256_TEN.0;
pub const U256_E18: primitive_types::U256 = SU256_E18.0;
pub const I256_E18: I256 = i256const!(pow10_i128(18));

#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Default, PartialOrd, Ord, derive_more::From, derive_more::Into, derive_more::Deref)]
pub struct ChecksumAddress(pub H160);

impl std::fmt::Debug for ChecksumAddress {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\"{:?}\"", self.0)
    }
}

impl Display for ChecksumAddress {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl ChecksumAddress {
    pub const fn zero() -> Self {
        Self(H160::zero())
    }

    pub const EEE: Self = Self::from_const("0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee");

    pub fn is_eth(&self) -> bool {
        self.0 == const { Self::zero().0 } || self.0 == Self::EEE.0
    }

    pub const fn parse_const(s: &str) -> Result<Self, ParseU256Error> {
        match parse_h256_hex(s) {
            Ok(h) => {
                let bytes32 = h.0;
                if     bytes32[0] != 0
                    || bytes32[1] != 0
                    || bytes32[2] != 0
                    || bytes32[3] != 0
                    || bytes32[4] != 0
                    || bytes32[5] != 0
                    || bytes32[6] != 0
                    || bytes32[7] != 0
                    || bytes32[8] != 0
                    || bytes32[9] != 0
                    || bytes32[10] != 0
                    || bytes32[11] != 0 {
                    panic!("Address is too big to fit into 160 bits")
                }

                Ok(Self(H160([
                    bytes32[12], bytes32[13], bytes32[14], bytes32[15], bytes32[16], bytes32[17],
                    bytes32[18], bytes32[19], bytes32[20], bytes32[21], bytes32[22], bytes32[23],
                    bytes32[24], bytes32[25], bytes32[26], bytes32[27], bytes32[28], bytes32[29],
                    bytes32[30], bytes32[31],
                ])))
            },
            Err(e) => Err(e),
        }
    }

    pub const fn from_const(s: &str) -> Self {
        unwrap_const(Self::parse_const(s))
    }
}

impl std::str::FromStr for ChecksumAddress {
    type Err = rustc_hex::FromHexError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        H160::from_str(s).map(Self)
    }
}

impl TryFrom<&str> for ChecksumAddress {
    type Error = rustc_hex::FromHexError;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        s.parse()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ChecksumError<'a> {
    TooShort(&'a str, usize),
    TooLong(&'a str, usize),
    IsNotAscii(&'a str),
    DoesNotStartWith0x(&'a str),
}

#[repr(transparent)]
#[serde_as]
#[derive(
    Serialize, Deserialize, Clone, Copy, PartialEq, Eq, Hash, Default, PartialOrd, Ord,
    derive_more::From, derive_more::Into, derive_more::Shl, derive_more::Shr, derive_more::ShlAssign, derive_more::ShrAssign,
    derive_more::Rem, derive_more::RemAssign,
    derive_more::BitAnd, derive_more::BitAndAssign, derive_more::BitOr, derive_more::BitOrAssign, derive_more::BitXor, derive_more::BitXorAssign, derive_more::Not,
    derive_more::Display
)]
pub struct SafeU256(#[serde_as(as = "crate::barter_lib::common::NiceSerializer<primitive_types::U256>")] pub primitive_types::U256);

impl Tokenize for SafeU256 {
    fn from_token(token: Token) -> Result<Self, ethcontract::tokens::Error>
    where
        Self: Sized {
        primitive_types::U256::from_token(token).map(Self)
    }

    fn into_token(self) -> Token {
        self.0.into_token()
    }
}

impl SafeU256 {
    pub const MAX: Self = Self(primitive_types::U256::MAX);

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

    // TODO: Make pow now panic on overflow
    pub fn pow(self, exp: impl Into<primitive_types::U256>) -> Self {
        Self(self.0.pow(exp.into()))
    }

    pub const fn zero() -> Self {
        Self(primitive_types::U256::zero())
    }

    pub const fn is_zero(&self) -> bool {
        self.0.is_zero()
    }

    pub fn exp10(n: usize) -> Self {
        primitive_types::U256::exp10(n).into()
    }

    pub fn from_dec_str(s: &str) -> Result<Self, uint::FromDecStrErr> {
        primitive_types::U256::from_dec_str(s).map(Self)
    }

    pub const fn one() -> Self {
        Self(primitive_types::U256::one())
    }

    pub fn as_u32(&self) -> u32 {
        self.0.as_u32()
    }

    pub fn as_u64(&self) -> u64 {
        self.0.as_u64()
    }

    pub fn as_u128(&self) -> u128 {
        self.0.as_u128()
    }

    pub const fn bit(&self, index: usize) -> bool {
        self.0.bit(index)
    }

    pub const fn low_u128(&self) -> u128 {
        self.0.low_u128()
    }

    pub fn as_usize(&self) -> usize {
        self.0.as_usize()
    }

    pub fn from_big_endian(bytes: &[u8]) -> Self {
        primitive_types::U256::from_big_endian(bytes).into()
    }
}

impl From<&SafeU256> for primitive_types::U256 {
    fn from(v: &SafeU256) -> Self {
        v.0
    }
}

impl From<SafeU256> for U512 {
    fn from(v: SafeU256) -> Self {
        v.0.into()
    }
}

impl TryFrom<U512> for SafeU256 {
    type Error = <primitive_types::U256 as TryFrom<U512>>::Error;

    fn try_from(value: U512) -> Result<Self, Self::Error> {
        Ok(Self(primitive_types::U256::try_from(value)?))
    }
}

macro_rules! declare_conv {
    // () => {
    //     impl From<u64> for SafeU256 {
    //         fn from(v: u64) -> Self {
    //             Self(primitive_types::U256::from(v))
    //         }
    //     }
    // };

    ($($t:ty),*) => {
        $(
            impl From<$t> for SafeU256 {
                fn from(v: $t) -> Self {
                    Self(primitive_types::U256::from(v))
                }
            }

            impl TryInto<$t> for SafeU256 {
                type Error = <primitive_types::U256 as TryInto<$t>>::Error;

                fn try_into(self) -> Result<$t, Self::Error> {
                    self.0.try_into()
                }
            }
        )*
    };
}

declare_conv!(u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, usize, isize);

// impl SafeMath for $name {
impl<T: Into<primitive_types::U256>> std::ops::Add<T> for SafeU256 {
    type Output = safe_math::SafeMathResult<Self>;

    fn add(self, rhs: T) -> Self::Output {
        safe_math::MathResult(Ok(Self(self.0.sm_add(rhs.into())?)))
    }
}

impl<T: Into<primitive_types::U256>> std::ops::Sub<T> for SafeU256 {
    type Output = safe_math::SafeMathResult<Self>;

    fn sub(self, rhs: T) -> Self::Output {
        safe_math::MathResult(Ok(Self(self.0.sm_sub(rhs.into())?)))
    }
}

impl<T: Into<primitive_types::U256>> std::ops::Mul<T> for SafeU256 {
    type Output = safe_math::SafeMathResult<Self>;

    fn mul(self, rhs: T) -> Self::Output {
        safe_math::MathResult(Ok(Self(self.0.sm_mul(rhs.into())?)))
    }
}

impl<T: Into<primitive_types::U256>> std::ops::Div<T> for SafeU256 {
    type Output = safe_math::SafeMathResult<Self>;

    fn div(self, rhs: T) -> Self::Output {
        safe_math::MathResult(Ok(Self(self.0.sm_div(rhs.into())?)))
    }
}

// impl SafeMath<SafeMathResult<$name>> for $name {
impl<T: Into<primitive_types::U256>> std::ops::Add<safe_math::SafeMathResult<T>> for SafeU256 {
    type Output = safe_math::SafeMathResult<Self>;

    fn add(self, rhs: safe_math::SafeMathResult<T>) -> Self::Output {
        safe_math::MathResult(Ok((self + rhs?)?))
    }
}

impl<T: Into<primitive_types::U256>> std::ops::Sub<safe_math::SafeMathResult<T>> for SafeU256 {
    type Output = safe_math::SafeMathResult<Self>;

    fn sub(self, rhs: safe_math::SafeMathResult<T>) -> Self::Output {
        safe_math::MathResult(Ok((self - rhs?)?))
    }
}

impl<T: Into<primitive_types::U256>> std::ops::Mul<safe_math::SafeMathResult<T>> for SafeU256 {
    type Output = safe_math::SafeMathResult<Self>;

    fn mul(self, rhs: safe_math::SafeMathResult<T>) -> Self::Output {
        safe_math::MathResult(Ok((self * rhs?)?))
    }
}

impl<T: Into<primitive_types::U256>> std::ops::Div<safe_math::SafeMathResult<T>> for SafeU256 {
    type Output = safe_math::SafeMathResult<Self>;

    fn div(self, rhs: safe_math::SafeMathResult<T>) -> Self::Output {
        safe_math::MathResult(Ok((self / rhs?)?))
    }
}

// impl SafeMath<$name> for SafeMathResult<$name> {

impl<T: Into<primitive_types::U256>> std::ops::Add<T> for safe_math::SafeMathResult<SafeU256> {
    type Output = safe_math::SafeMathResult<SafeU256>;

    fn add(self, rhs: T) -> Self::Output {
        safe_math::MathResult(Ok((self? + rhs.into())?))
    }
}

impl<T: Into<primitive_types::U256>> std::ops::Sub<T> for safe_math::SafeMathResult<SafeU256> {
    type Output = safe_math::SafeMathResult<SafeU256>;

    fn sub(self, rhs: T) -> Self::Output {
        safe_math::MathResult(Ok((self? - rhs.into())?))
    }
}

impl<T: Into<primitive_types::U256>> std::ops::Mul<T> for safe_math::SafeMathResult<SafeU256> {
    type Output = safe_math::SafeMathResult<SafeU256>;

    fn mul(self, rhs: T) -> Self::Output {
        safe_math::MathResult(Ok((self? * rhs.into())?))
    }
}

impl<T: Into<primitive_types::U256>> std::ops::Div<T> for safe_math::SafeMathResult<SafeU256> {
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
enum CollectArrayError {
    TooFewElements,
    TooManyElements,
}

trait CollectArray<T, const N: usize> {
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

pub fn get_checksumed_address(address: &str) -> Result<ArrayString<42>, ChecksumError<'_>> {
    const LENGTH: usize = 40;

    use sha3::{
        Digest,
        Keccak256,
    };

    if !address.starts_with("0x") {
        return Err(ChecksumError::DoesNotStartWith0x(address));
    }

    if !address.is_ascii() {
        return Err(ChecksumError::IsNotAscii(address));
    }

    let address: [u8; 40] = address[2..]
        .chars()
        .map(|c| c.to_ascii_lowercase() as u8)
        .try_collect()
        .map_err(|e| match e {
            CollectArrayError::TooFewElements => ChecksumError::TooShort(address, LENGTH),
            CollectArrayError::TooManyElements => ChecksumError::TooLong(address, LENGTH),
        })?;
    let address = unsafe {
        // SAFETY: we know that the address is valid because we checked the length and
        // the ascii
        ArrayString::from_byte_string(&address).unwrap_unchecked()
    };

    let address_hash = {
        let mut hasher = Keccak256::new();
        hasher.update(address.as_bytes());
        hasher.finalize()
    };

    let address_hash = &address_hash[..];

    let mut result = ArrayString::new();
    result.push_str("0x");
    for (index, address_char) in address.char_indices() {
        let n = address_hash[index / 2];
        let n = if index % 2 == 0 { n >> 4 } else { n & 0x0f };

        if n > 7 {
            // make char uppercase if ith character is 9..f
            result.push(address_char.to_ascii_uppercase())
        } else {
            // already lowercased
            result.push(address_char)
        }
    }

    Ok(result)
}

impl Serialize for ChecksumAddress {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
    {
        serializer.serialize_str(&get_checksumed_address(&format!("{:?}", self.0)).unwrap())
    }
}

impl<'de> Deserialize<'de> for ChecksumAddress {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
    {
        let string = <std::borrow::Cow<str>>::deserialize(deserializer)?;
        let address = H160::from_str(&string)
            .map_err(|e| {
                serde::de::Error::custom(format!("Failed to parse string '{}' as address: {}", string, e))
            })?;
        Ok(ChecksumAddress(address))
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
                <$selfty>::from_str_radix(str, radix)
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


generate_from_str_impl!(U256, uint::FromStrRadixErr);
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

#[derive(Debug)]
pub enum ParseUnitsError {
    ParseFloat(core::num::ParseFloatError, u8, String),
    FromDecStr(uint::FromDecStrErr, u8, String),
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
            return Ok(U256::from_dec_str(value).map_err(|e| ParseUnitsError::FromDecStr(e, decimals, value.to_string()))?.mul(U256::exp10(decimals.into())).into());
        };
        let (integer, fractional) = value.split_at(dot_index);
        let integer = U256::from_dec_str(integer).map_err(|e| ParseUnitsError::FromDecStr(e, decimals, value.to_string()))?.mul(U256::exp10(decimals.into()));
        let fractional = &fractional[1..];
        let mut fract = U256::from_dec_str(fractional).map_err(|e| ParseUnitsError::FromDecStr(e, decimals, value.to_string()))?;
        if fractional.len() < decimals as usize {
            fract *= U256::exp10((decimals - fractional.len() as u8).into());
        } else {
            fract /= U256::exp10(fractional.len() - decimals as usize);
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
        let addr_lowercase = "0xe0fc04fa2d34a66b779fd5cee748268032a146c0";
        let checksummed = get_checksumed_address(addr_lowercase).unwrap();
        assert_eq!(checksummed.as_str(), "0xe0FC04FA2d34a66B779fd5CEe748268032a146c0");

        let addr_uppercase = "0xE0FC04FA2D34A66B779FD5CEE748268032A146C0";
        let checksummed = get_checksumed_address(addr_uppercase).unwrap();
        assert_eq!(checksummed.as_str(), "0xe0FC04FA2d34a66B779fd5CEe748268032a146c0");
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

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct Erc4626Token {
    pub rate: SafeU256,
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