use crate::barter_lib::async_utils::AwaitableTuple;
use alloy::network::Network;
use alloy::providers::Provider;

pub mod dodo_v1 {
    use num::FromPrimitive;

    use super::*;
    use crate::{contracts::DodoV1PoolContract, types::dodo_v1::{FlowerData, PoolInfo}};

    pub async fn get_flower_data<P: Provider<N> + Clone, N: Network>(provider: P, pool: PoolInfo, block_number: u64) -> FlowerData {
        let contract = DodoV1PoolContract::new(pool.address.into(), provider);

        let state = (
            contract._K_().block(block_number.into()).call(),
            contract._BASE_BALANCE_().block(block_number.into()).call(),
            contract._QUOTE_BALANCE_().block(block_number.into()).call(),
            contract.getOraclePrice().block(block_number.into()).call(),
            contract._TARGET_BASE_TOKEN_AMOUNT_().block(block_number.into()).call(),
            contract._TARGET_QUOTE_TOKEN_AMOUNT_().block(block_number.into()).call(),
            contract._R_STATUS_().block(block_number.into()).call(),
            contract._MT_FEE_RATE_().block(block_number.into()).call(),
            contract._LP_FEE_RATE_().block(block_number.into()).call(),
        ).awaitable().await;

        FlowerData {
            pool_info: pool,
            k: state.0.unwrap().into(),
            base_balance: state.1.unwrap().into(),
            quote_balance: state.2.unwrap().into(),
            oracle_price: state.3.unwrap().into(),
            target_base_token_amount: state.4.unwrap().into(),
            target_quote_token_amount: state.5.unwrap().into(),
            r_status: FromPrimitive::from_u8(state.6.unwrap()).unwrap(),
            mt_fee_rate: state.7.unwrap().into(),
            lp_fee_rate: state.8.unwrap().into(),
        }
    }
}