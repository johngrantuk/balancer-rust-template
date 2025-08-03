#![allow(clippy::too_many_arguments)]
#![allow(unused)]
use std::{collections::HashMap, sync::Arc};

pub use common::SafeU256;
pub use primitive_types;
use serde_with::serde_as;
use serde::{Serialize, Deserialize};
use smol_str::SmolStr;

pub mod async_utils;
pub mod common;
pub mod i256;
pub mod u256;
pub mod safe_math;
pub mod amm_lib;

pub type U256 = primitive_types::U256;
pub type U512 = primitive_types::U512;
pub type H256 = primitive_types::H256;
pub type Bytes32 = primitive_types::H256;
pub use u256::parse_u256;

pub type UnderlyingError = primitive_types::Error;

pub const fn unwrap_const<T, E>(result: Result<T, E>) -> T {
    match result {
        Ok(ret) => ret,
        Err(_e) => panic!("called `unwrap()` on an `Err` value"),
    }
}

pub trait ResultExt<T> {
    fn unwrap_whatever(self) -> T;
}

impl<T> ResultExt<T> for Result<T, T> {
    fn unwrap_whatever(self) -> T {
        match self {
            Ok(x) => x,
            Err(x) => x,
        }
    }
}

pub trait IterHelper<T> {
    fn index_of(&self, val: &T) -> Option<usize>;
}

impl<T, U> IterHelper<T> for U
where
    T: PartialEq,
    U: AsRef<[T]>,
{
    fn index_of(&self, val: &T) -> Option<usize> {
        self.as_ref().iter().position(|x| x == val)
    }
}
