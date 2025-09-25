use alloy_primitives::{Address, Bytes};
use crate::barter_lib::SafeU256;

pub mod dodo_v1 {

    use crate::contracts::DODO_V1_POOL;

    use super::*;

    pub fn encode(
        amount_in: SafeU256,
        min_amount_out: SafeU256,
        meta: &crate::model::dodo_v1::DodoV1Meta
    ) -> EncodeResult{
        if meta.is_sell_base {
            let calldata = DODO_V1_POOL.sellBaseToken(
                amount_in.into(),
                min_amount_out.into(),
                Default::default()
            ).calldata().clone();
            return EncodeResult {
                calldata,
                target: meta.pool_address.into(),
                source_interaction: SourceInteraction::Approve
            };
        }

        panic!(
            "Sell quote requires a helper contract deployed to handle the swap in one transaction, and we don't want to deploy it.
            A correct implementation should not panic"
        );
    }
}

pub mod fluid_dex_lite {
    use crate::contracts::{FLUID_DEX_LITE, FluidDexLiteContract};
    use crate::model::fluid_dex_lite::FluidDexLiteMeta;

    use super::*;

    pub fn encode(
        amount_in: SafeU256,
        min_amount_out: SafeU256,
        meta: &FluidDexLiteMeta
    ) -> EncodeResult {
        // Prepare DexKey struct for the swapSingle call
        let dex_key = FluidDexLiteContract::DexKey {
            token0: meta.dex_key.token0,
            token1: meta.dex_key.token1,
            salt: meta.dex_key.salt.0.into(), // Convert SafeU256 to U256
        };

        // Determine swap amount and limits based on the swap direction
        let amount_specified = if meta.swap0_to1 {
            // Exact input swap: positive amount means selling the input token
            alloy_primitives::I256::from_raw(amount_in.0)
        } else {
            // Exact input swap: positive amount means selling the input token  
            alloy_primitives::I256::from_raw(amount_in.0)
        };

        // For exact input swaps, amountLimit is the minimum output amount
        let amount_limit = min_amount_out.0;

        // Encode swapSingle function call
        let calldata = FLUID_DEX_LITE.swapSingle(
            dex_key,
            meta.swap0_to1,
            amount_specified,
            amount_limit,
            Address::ZERO, // to_ parameter - will be set by the executor
            false, // isCallback_ (set to false for simple swaps)
            alloy_primitives::Bytes::new(), // callbackData_ (empty)
            alloy_primitives::Bytes::new(), // extraData_ (empty)
        ).calldata().clone();

        EncodeResult {
            calldata,
            target: meta.dex_lite_address,
            source_interaction: SourceInteraction::Approve, // Need to approve tokens to FluidDexLite contract
        }
    }
}

pub mod balancer_v3_stable_surge {

    use crate::contracts::BALANCER_V3_ROUTER;
    use alloy_primitives::{address};

    use super::*;

    pub fn encode(
        amount_in: SafeU256,
        min_amount_out: SafeU256,
        meta: &crate::model::balancer_v3_stable_surge::BalancerV3Meta
    ) -> EncodeResult{
        let calldata = BALANCER_V3_ROUTER.swapSingleTokenExactIn(
            meta.pool_address.into(),
            meta.source_token.into(),
            meta.target_token.into(),
            amount_in.into(),
            min_amount_out.into(),
            Default::default(),
            false,
            "0x".into()
        ).calldata().clone();

        return EncodeResult {
            calldata,
            target: address!("0xAE563E3f8219521950555F5962419C8919758Ea2"),
            source_interaction: SourceInteraction::Approve // Note - Permit2 is used for approvals
        };
    }
}

#[derive(Debug)]
#[allow(unused)]
pub struct EncodeResult {
    pub calldata: Bytes,
    pub target: Address,
    pub source_interaction: SourceInteraction
}

#[derive(Debug)]
#[allow(unused)]
pub enum SourceInteraction {
    Approve,
    Transfer,
    None, // callback
}