use std::num::IntErrorKind;

use primitive_types::{U256, H256, U512};

use crate::barter_lib::common::SafeU256;

#[macro_export]
macro_rules! su256const {
    ($val:expr) => {
        const { $crate::barter_lib::u256::u256_from_u128($val) }
    };
}

#[macro_export]
macro_rules! u256const {
    ($val:expr) => {
        const { $crate::barter_lib::u256::u256_from_u128($val) }.0
    };
}


#[macro_export]
macro_rules! su256const_str {
    ($val:expr) => {
        const { $crate::barter_lib::unwrap_const($crate::barter_lib::u256::parse_u256_hex($val)) }
    };
}

#[macro_export]
macro_rules! e {
    ($val:literal) => {
        const { $crate::barter_lib::u256::pow10_u256($val) }
    };
}

pub const fn u256_from_u128(val: u128) -> SafeU256 {
    let lo = val & u64::MAX as u128;
    let hi = val >> 64;
    SafeU256(U256([lo as u64, hi as u64, 0, 0]))
}

#[derive(Debug)]
pub struct ParseU256Error {
    pub kind: IntErrorKind,
}

pub const fn pow10(val: u32) -> u128 {
    10_u128.pow(val)
}

pub const fn pow10_u256(mut exp: u32) -> SafeU256 {
    let mut lower = 1u128;
    let mut upper = 0u128;

    while exp > 0 {
        let mut carry = 0;
        (lower, carry) = lower.carrying_mul(10, carry);
        (upper, _) = upper.carrying_mul(10, carry);

        exp -= 1;
    }

    let parts = [lower as u64, (lower >> 64) as u64, upper as u64, (upper >> 64) as u64];

    SafeU256(U256(parts))
}

pub const fn pow2_u256(mut exp: u32) -> SafeU256 {
    let mut lower = 1u128;
    let mut upper = 0u128;

    while exp > 0 {
        let mut carry = 0;
        (lower, carry) = lower.carrying_mul(2, carry);
        (upper, _) = upper.carrying_mul(2, carry);

        exp -= 1;
    }

    let parts = [lower as u64, (lower >> 64) as u64, upper as u64, (upper >> 64) as u64];

    SafeU256(U256(parts))
}


const fn validate_u256(input: &str) -> Result<&[u8], ParseU256Error> {
    let mut bytes = input.as_bytes();
    if bytes.is_empty() {
        return Err(ParseU256Error {
            kind: IntErrorKind::Empty,
        });
    }
    while let Some((b'0', rest)) = bytes.split_first() {
        if bytes.len() == 1 {
            break;
        }
        bytes = rest;
    }
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] > b'9' || bytes[i] < b'0' {
            return Err(ParseU256Error {
                kind: IntErrorKind::InvalidDigit,
            });
        }
        i += 1;
    }
    if bytes.len() > 78 {
        return Err(ParseU256Error {
            kind: IntErrorKind::PosOverflow,
        });
    }
    Ok(bytes)
}

const fn carrying_mul(a: u64, b: u64, carry: u64) -> (u64, u64) {
    let result = a as u128 * b as u128 + carry as u128;
    (result as u64, (result >> 64) as u64)
}

const fn carrying_add(a: u64, b: u64) -> (u64, u64) {
    let result = a as u128 + b as u128;
    (result as u64, (result >> 64) as u64)
}

fn try_as_u128(x: U256) -> Option<u128> {
    if x < const { u256_from_u128(u128::MAX).0 } {
        Some(x.as_u128())
    } else {
        None
    }
}

#[derive(Debug, Eq, PartialEq)]
pub struct U256ToF64Error(U256);

#[derive(Debug)]
pub struct F64ToU256Error(f64);

impl PartialEq for F64ToU256Error {
    fn eq(&self, other: &Self) -> bool {
        self.0.to_bits() == other.0.to_bits()
    }
}

impl Eq for F64ToU256Error {}

pub fn convert_direct_u256_to_f64(amount: U256) -> Result<f64, U256ToF64Error> {
    match try_as_u128(amount) {
        Some(x) => Ok(x as f64),
        None => Err(U256ToF64Error(amount)),
    }
}
pub fn convert_u256_to_f64(precision: U256, amount: U256) -> Option<f64> {
    let amount_value_int = try_as_u128(amount / precision)? as f64;
    let amount_value_mod = (try_as_u128(amount % precision)? as f64) / (try_as_u128(precision)? as f64);
    Some(amount_value_int + amount_value_mod)
}

#[allow(unused)]
pub fn convert_direct_f64_to_u256(amount: f64) -> Result<U256, F64ToU256Error> {
    if amount.fract().abs() > f64::EPSILON {
        return Err(F64ToU256Error(amount));
    }
    Ok(u256_from_u128(amount as u128).0)
}

pub fn convert_f64_to_u256(precision: impl Into<primitive_types::U256>, amount: f64) -> U256 {
    let precision = precision.into();
    let int_part_of_the_amount = U256::from(amount.floor() as u64) * precision;
    let mod_part_of_the_amount = U256::from(
        ((amount - amount.floor()) * (precision.as_u128() as f64)).round() as u64,
    );

    int_part_of_the_amount + mod_part_of_the_amount
}

pub const fn parse_u256(input: &str) -> Result<SafeU256, ParseU256Error> {
    let mut bytes = match validate_u256(input) {
        Ok(bytes) => bytes,
        Err(e) => return Err(e),
    };
    let [mut x0, mut x1, mut x2, mut x3] = [0; 4];
    let (mut mul_carry, mut add_carry) = (0, 0);
    while let Some((&d, rest)) = bytes.split_first() {
        bytes = rest;

        let mut carry = 0;
        (x0, carry) = carrying_mul(x0, 10, carry);
        (x1, carry) = carrying_mul(x1, 10, carry);
        (x2, carry) = carrying_mul(x2, 10, carry);
        (x3, mul_carry) = carrying_mul(x3, 10, carry);

        carry = (d - b'0') as u64;
        (x0, carry) = carrying_add(x0, carry);
        (x1, carry) = carrying_add(x1, carry);
        (x2, carry) = carrying_add(x2, carry);
        (x3, add_carry) = carrying_add(x3, carry);
    }
    if mul_carry > 0 || add_carry > 0 {
        return Err(ParseU256Error {
            kind: IntErrorKind::PosOverflow,
        });
    }
    Ok(SafeU256(U256([x0, x1, x2, x3])))
}

const fn ascii_hex_digit_to_digit(hexd: u8) -> Option<u8> {
    let digit = hexd.wrapping_sub(b'0');
    if digit < 10 {
        return Some(digit);
    }
    let digit = (hexd | 0b10_0000).wrapping_sub(b'a');
    if digit < 6 {
        return Some(10 + digit);
    }
    None
}

pub const fn parse_u256_hex(input: &str) -> Result<SafeU256, ParseU256Error> {
    let mut bytes = input.as_bytes();
    if bytes.is_empty() {
        return Err(ParseU256Error {
            kind: IntErrorKind::Empty,
        });
    }
    if bytes[0] == b'0' && bytes[1] == b'x' {
        bytes = bytes.split_at(2).1;
    }
    while let Some((b'0', rest)) = bytes.split_first() {
        if bytes.len() == 1 {
            break;
        }
        bytes = rest;
    }
    let mut ret = [0; 4];
    let mut i = 0;
    while let Some((&hexd, rest)) = bytes.split_last() {
        let digit;
        (digit, bytes) = match ascii_hex_digit_to_digit(hexd) {
            Some(d) => (d, rest),
            _ => {
                return Err(ParseU256Error {
                    kind: IntErrorKind::InvalidDigit,
                })
            }
        };
        if i < 64 {
            ret[i / 16] |= (digit as u64) << (4 * (i % 16));
        }
        i += 1;
    }
    if i > 64 {
        return Err(ParseU256Error {
            kind: IntErrorKind::PosOverflow,
        });
    }
    Ok(SafeU256(U256(ret)))
}

pub const fn parse_h256_hex(input: &str) -> Result<primitive_types::H256, ParseU256Error> {
   match parse_u256_hex(input) {
        Ok(x) =>  {
            let bytes: [u64; 4] = x.0.0;
            let byte0 = bytes[0].to_be_bytes();
            let byte1 = bytes[1].to_be_bytes();
            let byte2 = bytes[2].to_be_bytes();
            let byte3 = bytes[3].to_be_bytes();
            let ret   = [
                byte3[0], byte3[1], byte3[2], byte3[3], byte3[4], byte3[5], byte3[6], byte3[7],
                byte2[0], byte2[1], byte2[2], byte2[3], byte2[4], byte2[5], byte2[6], byte2[7],
                byte1[0], byte1[1], byte1[2], byte1[3], byte1[4], byte1[5], byte1[6], byte1[7],
                byte0[0], byte0[1], byte0[2], byte0[3], byte0[4], byte0[5], byte0[6], byte0[7],
            ];
            Ok(H256(ret))
        },
        Err(e) => Err(e),
    }
}

/// Returns a tuple of the conversion along with a boolean indicating whether an arithmetic overflow would
/// occur. If an overflow would have occurred then the wrapped value is returned.
pub const fn u512_to_u256(x: U512) -> (U256, bool) {
    let bytes = x.0;
    let value = U256([bytes[0], bytes[1], bytes[2], bytes[3]]);
    let overflown = bytes[4] != 0 || bytes[5] != 0 || bytes[6] != 0 || bytes[7] != 0;
    (value, overflown)
}

#[cfg(test)]
pub mod tests {
    use crate::barter_lib::{common::SU256_E18};

    use super::*;

    #[test]
    fn check_const_conversion() {
        for i in 2..127 {
            let val = 2_u128.pow(i);
            assert_eq!(U256::from(val), u256_from_u128(val).0);
            assert_eq!(U256::from(val - 1), u256_from_u128(val - 1).0);
            assert_eq!(U256::from(val + 1), u256_from_u128(val + 1).0);
        }
    }

    #[test]
    fn check_parsing() {
        for i in 2..127 {
            for j in 0..2 {
                let val = (2_u128.pow(i) + j - 1).to_string();
                assert_eq!(U256::from_dec_str(&val).unwrap(), parse_u256(&val).unwrap().0, "{}", val);
            }
        }
    }

    #[test]
    fn check_h256_parsing() {
        let tst = |x: &str| {
            assert_eq!(format!("{:?}", parse_h256_hex(x).unwrap()), x.to_ascii_lowercase());
        };

        tst("0x000000000000000000000000000000000000000000000000000000000000ABCD");
        tst("0x00000000000000000000000021410232B484136404911780bC32756D5d1a9Fa9");
        tst("0x0000000000000000000000003211C6cBeF1429da3D0d58494938299C92Ad5860");
        tst("0x00000000000000000000000050f3752289e1456BfA505afd37B241bca23e685d");
        tst("0x0000000000000000000000006ec38b3228251a0C5D491Faf66858e2E23d7728B");
        tst("0x0000000000000000000000008301AE4fc9c624d1D396cbDAa1ed877821D7C511");
        tst("0x0000000000000000000000008b0aFa4b63a3581b731dA9D79774a3eaE63B5ABD");
        tst("0x000000000000000000000000941Eb6F616114e4Ecaa85377945EA306002612FE");
        tst("0x000000000000000000000000B576491F1E6e5E62f1d8F26062Ee822B40B0E0d4");
        tst("0x000000000000000000000000C26b89A667578ec7b3f11b2F98d6Fd15C07C54ba");
        tst("0x000000000000000000000000D51a44d3FaE010294C616388b506AcdA1bfAAE46");
        tst("0x000000000000000000000000F43b15Ab692fDe1F9c24a9FCE700AdCC809D5391");
        tst("0x000000000000000000000000f861483fa7E511fbc37487D91B6FAa803aF5d37c");
        tst("0x000000000000000000000000fB8814D005C5f32874391e888da6eB2fE7a27902");
        tst("0x0000000000000000000000009838eCcC42659FA8AA7daF2aD134b53984c9427b");
        tst("0x00000000000000000000000098a7F18d4E56Cfe84E3D081B40001B3d5bD3eB8B");
    }

    #[test]
    fn u512_to_u256_works() {
        assert_eq!(u512_to_u256(U512::from(0)), (U256::from(0), false));
        assert_eq!(u512_to_u256(U512::from(U256::MAX)), (U256::MAX, false));
        assert_eq!(u512_to_u256(U512::from(U256::MAX) + U256::from(1)), (U256::from(0), true));
        assert_eq!(u512_to_u256(U512::from(100).pow(39.into())), (U256::from_dec_str("73663286101470436611432119930496737173840122674875487684339327936694962880512").unwrap(), true));
    }

    #[test]
    fn check_f64_to_u256() {
        assert_eq!(convert_f64_to_u256(SU256_E18, 0.000001119837169054), U256::from_dec_str("1119837169054").unwrap());
        assert_eq!(convert_f64_to_u256(SU256_E18, 0.000000000117107063), U256::from_dec_str("117107063").unwrap());
    }

    #[test]
    fn pow10_u256_works() {
        assert_eq!(pow10_u256(0), U256::exp10(0).into());
        assert_eq!(pow10_u256(3), U256::exp10(3).into());
        assert_eq!(pow10_u256(10), U256::exp10(10).into());
        assert_eq!(pow10_u256(27), U256::exp10(27).into());
        assert_eq!(pow10_u256(50), U256::exp10(50).into());
        assert_eq!(pow10_u256(70), U256::exp10(70).into());
        assert_eq!(pow10_u256(75), U256::exp10(75).into());
    }
}
