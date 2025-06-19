use web3::{transports::Http, Web3};
use crate::barter_lib::async_utils::AwaitableTuple;

pub mod dodo_v1 {
    use ethcontract::BlockId;
    use num::FromPrimitive;

    use super::*;
    use crate::{contracts::DodoV1PoolPrototype, types::dodo_v1::{FlowerData, PoolInfo}};

    pub async fn get_flower_data(web3: &Web3<Http>, pool: PoolInfo, block_id: BlockId) -> FlowerData {
        let contract = DodoV1PoolPrototype::at(web3, pool.address.0);

        let state = (
            contract.k().block(block_id).call(),
            contract.base_balance().block(block_id).call(),
            contract.quote_balance().block(block_id).call(),
            contract.get_oracle_price().block(block_id).call(),
            contract.target_base_token_amount().block(block_id).call(),
            contract.target_quote_token_amount().block(block_id).call(),
            contract.r_status().block(block_id).call(),
            contract.mt_fee_rate().block(block_id).call(),
            contract.lp_fee_rate().block(block_id).call(),
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