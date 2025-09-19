use crate::barter_lib::async_utils::AwaitableTuple;
use alloy::network::Network;
use alloy::providers::Provider;

pub mod dodo_v1 {
    use num::FromPrimitive;

    use super::*;
    use crate::{barter_lib::BlockMeta, contracts::DodoV1PoolContract, types::dodo_v1::{FlowerData, PoolInfo}};

    pub async fn get_flower_data<P: Provider<N> + Clone, N: Network>(provider: P, pool: PoolInfo, block_meta: &BlockMeta) -> FlowerData {
        let contract = DodoV1PoolContract::new(pool.address.into(), provider);

        let state = (
            contract._K_().block(block_meta.number.into()).call(),
            contract._BASE_BALANCE_().block(block_meta.number.into()).call(),
            contract._QUOTE_BALANCE_().block(block_meta.number.into()).call(),
            contract.getOraclePrice().block(block_meta.number.into()).call(),
            contract._TARGET_BASE_TOKEN_AMOUNT_().block(block_meta.number.into()).call(),
            contract._TARGET_QUOTE_TOKEN_AMOUNT_().block(block_meta.number.into()).call(),
            contract._R_STATUS_().block(block_meta.number.into()).call(),
            contract._MT_FEE_RATE_().block(block_meta.number.into()).call(),
            contract._LP_FEE_RATE_().block(block_meta.number.into()).call(),
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

pub mod fluid_dex_lite {
    use alloy_primitives::{keccak256, U256};
    use alloy::rpc::types::BlockNumberOrTag;
    use crate::barter_lib::{BlockMeta, SafeU256};

    use super::*;
    use crate::{contracts::FluidDexLiteContract, types::fluid_dex_lite::{FlowerData, PoolInfo}};

    pub async fn get_flower_data<P: Provider<N> + Clone, N: Network>(
        provider: P, 
        pool: PoolInfo, 
        block_meta: &BlockMeta
    ) -> FlowerData {
        let dex_lite = FluidDexLiteContract::new(pool.dex_lite_address, &provider);
        
        // Storage slot constants from DexLiteSlotsLink
        const DEX_LITE_DEX_VARIABLES_SLOT: u64 = 2;
        const DEX_LITE_CENTER_PRICE_SHIFT_SLOT: u64 = 3;
        const DEX_LITE_RANGE_SHIFT_SLOT: u64 = 4;
        const DEX_LITE_THRESHOLD_SHIFT_SLOT: u64 = 5;
        
        // Calculate storage slots for mappings using the dexId
        let dex_id_bytes = pool.dex_id.0.to_be_bytes::<32>();

        dbg!(dex_id_bytes);
        
        let dex_variables_slot = calculate_mapping_storage_slot(DEX_LITE_DEX_VARIABLES_SLOT, &dex_id_bytes);
        let center_price_shift_slot = calculate_mapping_storage_slot(DEX_LITE_CENTER_PRICE_SHIFT_SLOT, &dex_id_bytes);
        let range_shift_slot = calculate_mapping_storage_slot(DEX_LITE_RANGE_SHIFT_SLOT, &dex_id_bytes);
        let threshold_shift_slot = calculate_mapping_storage_slot(DEX_LITE_THRESHOLD_SHIFT_SLOT, &dex_id_bytes);
        
        let block_tag = BlockNumberOrTag::Number(block_meta.number);
        
        // Fetch all storage values in parallel using the AwaitableTuple pattern
        let state = (
            dex_lite.readFromStorage(dex_variables_slot.into()).block(block_tag.into()).call(),
            dex_lite.readFromStorage(center_price_shift_slot.into()).block(block_tag.into()).call(),
            dex_lite.readFromStorage(range_shift_slot.into()).block(block_tag.into()).call(),
            dex_lite.readFromStorage(threshold_shift_slot.into()).block(block_tag.into()).call(),
        ).awaitable().await;

        let dex_variables = SafeU256::from(state.0.unwrap());
        let center_price_shift = SafeU256::from(state.1.unwrap());
        let range_shift = SafeU256::from(state.2.unwrap());
        let threshold_shift = SafeU256::from(state.3.unwrap());

        FlowerData {
            pool_info: pool,
            dex_variables,
            center_price_shift,
            range_shift,
            threshold_shift,
            block_meta: block_meta.clone(),
        }
    }
    
    // Helper function to calculate mapping storage slot
    fn calculate_mapping_storage_slot(slot: u64, key: &[u8; 32]) -> U256 {
        // CRITICAL FIX: For bytes8 keys in Solidity mappings, we need to pad to bytes32
        // The dexId is bytes8 but storage slot calculation expects bytes32
        // KyberSwap puts the 8 bytes at the START of the 32-byte array, not the end
        let mut padded_key = [0u8; 32];
        padded_key[0..8].copy_from_slice(&key[24..32]); // Take the last 8 bytes (dexId) and put at start
        

        
        // Solidity mapping storage slot calculation: keccak256(abi.encode(key, slot))
        // Format: key (32 bytes) + slot (32 bytes)
        let mut encoded = Vec::new();
        encoded.extend_from_slice(&padded_key);  // key first
        
        let mut slot_bytes = [0u8; 32];
        slot_bytes[24..32].copy_from_slice(&slot.to_be_bytes()); // slot as 32 bytes, big-endian
        encoded.extend_from_slice(&slot_bytes);
        
        let hash = keccak256(&encoded);
        U256::from_be_slice(hash.as_slice())
    }
}