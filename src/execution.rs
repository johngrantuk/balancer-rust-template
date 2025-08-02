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