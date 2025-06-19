use serde::{Deserialize, Serialize};
use serde_with::serde_as;
use serde_repr::Serialize_repr;
use serde_repr::Deserialize_repr;
use num_derive::FromPrimitive;

use crate::barter_lib::ChecksumAddress;
use crate::barter_lib::SafeU256;

pub mod dodo_v1 {
    use super::*;

    #[serde_as]
    #[derive(Debug, Deserialize, Serialize, Clone, Eq, PartialEq)]
    #[serde(rename_all = "camelCase")]
    pub struct PoolInfo {
        pub address: ChecksumAddress,
        pub base_token: ChecksumAddress,
        pub quote_token: ChecksumAddress,
    }

    #[derive(Serialize_repr, Deserialize_repr, Eq, PartialEq, Debug, Clone, FromPrimitive)]
    #[repr(u8)]
    pub enum RStatus {
        One = 0,
        AboveOne = 1,
        BelowOne = 2,
    }

    #[serde_as]
    #[derive(Debug, Deserialize, Serialize, Clone, Eq, PartialEq)]
    #[serde(rename_all = "camelCase")]
    pub struct FlowerData {
        pub pool_info: PoolInfo,
        pub k: SafeU256,
        pub base_balance: SafeU256,
        pub quote_balance: SafeU256,
        pub oracle_price: SafeU256,
        pub target_base_token_amount: SafeU256,
        pub target_quote_token_amount: SafeU256,
        pub r_status: RStatus,
        pub mt_fee_rate: SafeU256,
        pub lp_fee_rate: SafeU256,
    }
}