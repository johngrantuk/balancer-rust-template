use serde::{Deserialize, Serialize};
use serde_with::serde_as;
use serde_repr::Serialize_repr;
use serde_repr::Deserialize_repr;
use num_derive::FromPrimitive;

use crate::barter_lib::SafeU256;

pub mod dodo_v1 {
    use alloy_primitives::Address;

    use super::*;

    #[serde_as]
    #[derive(Debug, Deserialize, Serialize, Clone, Eq, PartialEq)]
    #[serde(rename_all = "camelCase")]
    pub struct PoolInfo {
        pub address: Address,
        pub base_token: Address,
        pub quote_token: Address,
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

pub mod fluid_dex_lite {
    use alloy_primitives::Address;
    use crate::barter_lib::BlockMeta;

    use super::*;

    /// DexKey structure representing a unique pool identifier
    #[serde_as]
    #[derive(Debug, Deserialize, Serialize, Clone, Eq, PartialEq, Hash)]
    #[serde(rename_all = "camelCase")]
    pub struct DexKey {
        pub token0: Address,
        pub token1: Address,
        pub salt: SafeU256, // bytes32 in Solidity
    }

    /// Basic pool information that never changes
    #[serde_as]
    #[derive(Debug, Deserialize, Serialize, Clone, Eq, PartialEq)]
    #[serde(rename_all = "camelCase")]
    pub struct PoolInfo {
        pub dex_lite_address: Address, // FluidDexLite contract address
        pub dex_key: DexKey,
        pub dex_id: SafeU256, // bytes8 as SafeU256
    }

    /// Complete pool state data required for both simulation and execution
    #[serde_as]
    #[derive(Debug, Deserialize, Serialize, Clone, Eq, PartialEq)]
    #[serde(rename_all = "camelCase")]
    pub struct FlowerData {
        pub pool_info: PoolInfo,
        // Packed dex variables containing all state
        pub dex_variables: SafeU256,
        // Center price shift variables
        pub center_price_shift: SafeU256,
        // Range shift variables
        pub range_shift: SafeU256,
        // Threshold shift variables
        pub threshold_shift: SafeU256,
        // Block metadata for timestamp simulation
        pub block_meta: BlockMeta,
    }

    /// Unpacked dex variables for easier access during calculations
    #[allow(unused)]
    #[derive(Debug, Clone)]
    pub struct UnpackedDexVariables {
        pub fee: SafeU256,
        pub revenue_cut: SafeU256,
        pub rebalancing_status: SafeU256,
        pub center_price_shift_active: bool,
        pub center_price: SafeU256,
        pub center_price_contract_address: SafeU256,
        pub range_percent_shift_active: bool,
        pub upper_percent: SafeU256,
        pub lower_percent: SafeU256,
        pub threshold_percent_shift_active: bool,
        pub upper_shift_threshold_percent: SafeU256,
        pub lower_shift_threshold_percent: SafeU256,
        pub token0_decimals: SafeU256,
        pub token1_decimals: SafeU256,
        pub token0_total_supply_adjusted: SafeU256,
        pub token1_total_supply_adjusted: SafeU256,
    }

    /// Result of pricing calculations
    #[allow(unused)]
    #[derive(Debug, Clone)]
    pub struct PricingResult {
        pub center_price: SafeU256,
        pub upper_range_price: SafeU256,
        pub lower_range_price: SafeU256,
        pub token0_imaginary_reserves: SafeU256,
        pub token1_imaginary_reserves: SafeU256,
    }

    // Constants for bit manipulation (from DexLiteSlotsLink and constantVariables)
    pub const BITS_DEX_LITE_DEX_VARIABLES_FEE: u32 = 0;
    pub const BITS_DEX_LITE_DEX_VARIABLES_REVENUE_CUT: u32 = 13;
    pub const BITS_DEX_LITE_DEX_VARIABLES_REBALANCING_STATUS: u32 = 20;
    pub const BITS_DEX_LITE_DEX_VARIABLES_CENTER_PRICE_SHIFT_ACTIVE: u32 = 22;
    pub const BITS_DEX_LITE_DEX_VARIABLES_CENTER_PRICE: u32 = 23;
    pub const BITS_DEX_LITE_DEX_VARIABLES_CENTER_PRICE_CONTRACT_ADDRESS: u32 = 63;
    pub const BITS_DEX_LITE_DEX_VARIABLES_RANGE_PERCENT_SHIFT_ACTIVE: u32 = 82;
    pub const BITS_DEX_LITE_DEX_VARIABLES_UPPER_PERCENT: u32 = 83;
    pub const BITS_DEX_LITE_DEX_VARIABLES_LOWER_PERCENT: u32 = 97;
    pub const BITS_DEX_LITE_DEX_VARIABLES_THRESHOLD_PERCENT_SHIFT_ACTIVE: u32 = 111;
    pub const BITS_DEX_LITE_DEX_VARIABLES_UPPER_SHIFT_THRESHOLD_PERCENT: u32 = 112;
    pub const BITS_DEX_LITE_DEX_VARIABLES_LOWER_SHIFT_THRESHOLD_PERCENT: u32 = 119;
    pub const BITS_DEX_LITE_DEX_VARIABLES_TOKEN_0_DECIMALS: u32 = 126;
    pub const BITS_DEX_LITE_DEX_VARIABLES_TOKEN_1_DECIMALS: u32 = 131;
    pub const BITS_DEX_LITE_DEX_VARIABLES_TOKEN_0_TOTAL_SUPPLY_ADJUSTED: u32 = 136;
    pub const BITS_DEX_LITE_DEX_VARIABLES_TOKEN_1_TOTAL_SUPPLY_ADJUSTED: u32 = 196;

    // Bit masks (from constantVariables.sol)
    pub const X1: SafeU256 = SafeU256(alloy_primitives::U256::from_limbs([0x1, 0, 0, 0]));
    pub const X2: SafeU256 = SafeU256(alloy_primitives::U256::from_limbs([0x3, 0, 0, 0]));
    pub const X5: SafeU256 = SafeU256(alloy_primitives::U256::from_limbs([0x1f, 0, 0, 0]));
    pub const X7: SafeU256 = SafeU256(alloy_primitives::U256::from_limbs([0x7f, 0, 0, 0]));
    pub const X13: SafeU256 = SafeU256(alloy_primitives::U256::from_limbs([0x1fff, 0, 0, 0]));
    pub const X14: SafeU256 = SafeU256(alloy_primitives::U256::from_limbs([0x3fff, 0, 0, 0]));
    pub const X19: SafeU256 = SafeU256(alloy_primitives::U256::from_limbs([0x7ffff, 0, 0, 0]));
    pub const X20: SafeU256 = SafeU256(alloy_primitives::U256::from_limbs([0xfffff, 0, 0, 0]));
    pub const X24: SafeU256 = SafeU256(alloy_primitives::U256::from_limbs([0xffffff, 0, 0, 0]));
    pub const X28: SafeU256 = SafeU256(alloy_primitives::U256::from_limbs([0xfffffff, 0, 0, 0]));
    pub const X33: SafeU256 = SafeU256(alloy_primitives::U256::from_limbs([0x1ffffffff, 0, 0, 0]));
    pub const X40: SafeU256 = SafeU256(alloy_primitives::U256::from_limbs([0xffffffffff, 0, 0, 0]));
    pub const X60: SafeU256 = SafeU256(alloy_primitives::U256::from_limbs([0xfffffffffffffff, 0, 0, 0]));

    // CenterPriceShift bit positions
    pub const BITS_DEX_LITE_CENTER_PRICE_SHIFT_SHIFTING_TIME: u32 = 33;
    pub const BITS_DEX_LITE_CENTER_PRICE_SHIFT_MAX_CENTER_PRICE: u32 = 57;
    pub const BITS_DEX_LITE_CENTER_PRICE_SHIFT_MIN_CENTER_PRICE: u32 = 85;

    // RangeShift bit positions
    pub const BITS_DEX_LITE_RANGE_SHIFT_OLD_UPPER_RANGE_PERCENT: u32 = 0;
    pub const BITS_DEX_LITE_RANGE_SHIFT_OLD_LOWER_RANGE_PERCENT: u32 = 14;
    pub const BITS_DEX_LITE_RANGE_SHIFT_TIME_TO_SHIFT: u32 = 28;
    pub const BITS_DEX_LITE_RANGE_SHIFT_TIMESTAMP: u32 = 48;

    // Other constants  
    pub const FOUR_DECIMALS: SafeU256 = SafeU256(alloy_primitives::U256::from_limbs([10000, 0, 0, 0]));
    pub const SIX_DECIMALS: SafeU256 = SafeU256(alloy_primitives::U256::from_limbs([1000000, 0, 0, 0]));
    pub const PRICE_PRECISION: SafeU256 = SafeU256(alloy_primitives::U256::from_limbs([11515845259552620544, 54210108, 0, 0])); // 10^27 split into limbs correctly
    pub const TOKENS_DECIMALS_PRECISION: SafeU256 = SafeU256(alloy_primitives::U256::from_limbs([9, 0, 0, 0]));
    pub const MINIMUM_LIQUIDITY_SWAP: SafeU256 = SafeU256(alloy_primitives::U256::from_limbs([10000, 0, 0, 0]));
    pub const DEFAULT_EXPONENT_SIZE: SafeU256 = SafeU256(alloy_primitives::U256::from_limbs([8, 0, 0, 0]));
    pub const DEFAULT_EXPONENT_MASK: SafeU256 = SafeU256(alloy_primitives::U256::from_limbs([0xff, 0, 0, 0]));

    // FluidDexLite specific error types matching contract reverts
    #[derive(Debug, Clone, PartialEq)]
    pub enum FluidDexLiteError {
        // Math errors
        MathError(crate::barter_lib::safe_math::SafeMathError),
        // Contract-specific errors (matching Solidity error names)
        DexNotInitialized,
        InvalidSwapAmounts,
        ExcessiveSwapAmount,
        TokenReservesTooLow,
        TokenReservesRatioTooHigh,

    }

    impl From<crate::barter_lib::safe_math::SafeMathError> for FluidDexLiteError {
        fn from(err: crate::barter_lib::safe_math::SafeMathError) -> Self {
            FluidDexLiteError::MathError(err)
        }
    }
}

pub mod balancer_v3_stable_surge {
    use alloy_primitives::Address;

    use super::*;

    #[serde_as]
    #[derive(Debug, Deserialize, Serialize, Clone, Eq, PartialEq)]
    #[serde(rename_all = "camelCase")]
    pub struct PoolInfo {
        pub address: Address,
        pub tokens: Vec<Address>,  // Multi-token support
        pub decimal_scaling_factors: Vec<SafeU256>,
        pub supports_unbalanced_liquidity: bool,
        pub hook_type: String,
    }

    #[serde_as]
    #[derive(Debug, Deserialize, Serialize, Clone, Eq, PartialEq)]
    #[serde(rename_all = "camelCase")]
    pub struct FlowerData {
        pub pool_info: PoolInfo,
        pub token_rates: Vec<SafeU256>,
        pub balances_live_scaled_18: Vec<SafeU256>,
        pub swap_fee: SafeU256,
        pub aggregate_swap_fee: SafeU256,
        pub total_supply: SafeU256,
        pub amp: SafeU256,
        pub max_surge_fee_percentage: SafeU256,
        pub surge_threshold_percentage: SafeU256,
    }
}

pub mod balancer_v3_reclamm {
    use alloy_primitives::Address;

    use super::*;

    #[serde_as]
    #[derive(Debug, Deserialize, Serialize, Clone, Eq, PartialEq)]
    #[serde(rename_all = "camelCase")]
    pub struct PoolInfo {
        pub address: Address,
        pub tokens: Vec<Address>,  // Multi-token support
        pub decimal_scaling_factors: Vec<SafeU256>,
        pub supports_unbalanced_liquidity: bool,
    }

    #[serde_as]
    #[derive(Debug, Deserialize, Serialize, Clone, Eq, PartialEq)]
    #[serde(rename_all = "camelCase")]
    pub struct FlowerData {
        pub pool_info: PoolInfo,
        pub token_rates: Vec<SafeU256>,
        pub balances_live_scaled_18: Vec<SafeU256>,
        pub swap_fee: SafeU256,
        pub aggregate_swap_fee: SafeU256,
        pub total_supply: SafeU256,
        pub last_virtual_balances: Vec<SafeU256>,
        pub daily_price_shift_base: SafeU256,
        pub last_timestamp: SafeU256,
        pub current_timestamp: SafeU256,
        pub centeredness_margin: SafeU256,
        pub start_fourth_root_price_ratio: SafeU256,
        pub end_fourth_root_price_ratio: SafeU256,
        pub price_ratio_update_start_time: SafeU256,
        pub price_ratio_update_end_time: SafeU256,
    }
}

pub mod balancer_v3_quantamm {
    use alloy_primitives::{Address, I256};

    use super::*;

    #[serde_as]
    #[derive(Debug, Deserialize, Serialize, Clone, Eq, PartialEq)]
    #[serde(rename_all = "camelCase")]
    pub struct PoolInfo {
        pub address: Address,
        pub tokens: Vec<Address>,  // Multi-token support
        pub decimal_scaling_factors: Vec<SafeU256>,
        pub supports_unbalanced_liquidity: bool,
        pub max_trade_size_ratio: SafeU256
    }

    #[serde_as]
    #[derive(Debug, Deserialize, Serialize, Clone, Eq, PartialEq)]
    #[serde(rename_all = "camelCase")]
    pub struct FlowerData {
        pub pool_info: PoolInfo,
        pub token_rates: Vec<SafeU256>,
        pub balances_live_scaled_18: Vec<SafeU256>,
        pub swap_fee: SafeU256,
        pub aggregate_swap_fee: SafeU256,
        pub total_supply: SafeU256,
        pub first_four_weights_and_multipliers: Vec<I256>,
        pub second_four_weights_and_multipliers: Vec<I256>,
        pub last_update_time: SafeU256,
        pub last_interop_time: SafeU256,
        pub current_timestamp: SafeU256,
    }
}