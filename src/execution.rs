use web3::types::Bytes;

pub mod dodo_v1 {
    use crate::{barter_lib::{dummy::dummy_web3, SafeU256}, contracts::DodoV1PoolPrototype};
    use super::*;

    pub fn encode(
        amount_in: SafeU256,
        min_amount_out: SafeU256,
        meta: &crate::model::dodo_v1::DodoV1Meta
    ) -> EncodeResult{
        let pool_interface = DodoV1PoolPrototype::at(&dummy_web3(), Default::default());

        if meta.is_sell_base {
            let calldata = pool_interface.sell_base_token(
                amount_in.into(),
                min_amount_out.into(),
                Default::default()
            ).tx.data.unwrap();
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
    pub target: ethcontract::Address,
    pub source_interaction: SourceInteraction
}

#[derive(Debug)]
#[allow(unused)]
pub enum SourceInteraction {
    Approve,
    Transfer,
    None, // callback
}