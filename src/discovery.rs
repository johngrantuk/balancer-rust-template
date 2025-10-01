use alloy::network::Network;
use alloy::providers::Provider;

pub mod dodo_v1 {
    use alloy_primitives::{address, Address};

    use super::*;
    use crate::{contracts::{DodoV1PoolContract, DodoV1RegistryContract}, types::dodo_v1::PoolInfo};

    pub async fn get_all_pools<P: Provider<N> + Clone, N: Network>(provider: P) -> Vec<PoolInfo> {
        const REGISTRY: Address = address!("0x3a97247df274a17c59a3bd12735ea3fcdfb49950"); // mainnet

        let zoo = DodoV1RegistryContract::new(REGISTRY.into(), provider.clone());
        let pools = zoo.getDODOs().call().await.unwrap();
        let futures = pools.into_iter().map(|x| {
            let provider = provider.clone();
            async move {
                let dodo = DodoV1PoolContract::new(x.into(), provider);
                PoolInfo {
                    address: x,
                    base_token: dodo._BASE_TOKEN_().call().await.unwrap(),
                    quote_token: dodo._QUOTE_TOKEN_().call().await.unwrap(),
                }
            }
        });

        let mut pools = futures::future::join_all(futures).await;
        pools.sort_by_key(|x| x.address);
        pools
    }
}

pub mod fluid_dex_lite {
    use alloy_primitives::{address, Address, keccak256, U256};
    use alloy::rpc::types::BlockNumberOrTag;
    use crate::barter_lib::SafeU256;

    use super::*;
    use crate::{contracts::FluidDexLiteContract, types::fluid_dex_lite::{PoolInfo, DexKey}};

    pub async fn get_all_pools<P: Provider<N> + Clone, N: Network>(provider: P) -> Vec<PoolInfo> {
        // FluidDexLite contract address on mainnet
        const DEX_LITE_ADDRESS: Address = address!("0xBbcb91440523216e2b87052A99F69c604A7b6e00");
        
        let dex_lite = FluidDexLiteContract::new(DEX_LITE_ADDRESS, provider.clone());
        
        // Storage slot constants
        const DEX_LITE_DEXES_LIST_SLOT: u64 = 1;
        
        // First, read the array length from the storage slot
        let length_slot = format!("0x{:064x}", DEX_LITE_DEXES_LIST_SLOT);
        let length_result = dex_lite
            .readFromStorage(length_slot.parse().unwrap())
            .block(BlockNumberOrTag::Latest.into())
            .call()
            .await
            .unwrap();
        
        let array_length = length_result.to::<usize>();
        if array_length == 0 {
            return Vec::new();
        }
        
        // Calculate base slot for array data: keccak256(abi.encode(slot))
        // This matches Solidity's array storage layout calculation
        let mut slot_bytes = [0u8; 32];
        slot_bytes[31] = DEX_LITE_DEXES_LIST_SLOT as u8; // Store slot number in last byte, big-endian
        let array_base_slot_hash = keccak256(&slot_bytes);
        let array_base_slot = U256::from_be_slice(array_base_slot_hash.as_slice());
        
        let mut pools = Vec::new();
        
        for i in 0..array_length {
            let base_index = array_base_slot + U256::from(i * 3); // Each DexKey struct takes 3 slots
            
            // Read token0, token1, and salt from consecutive storage slots
            let token0_slot = format!("0x{:064x}", base_index);
            let token1_slot = format!("0x{:064x}", base_index + U256::from(1));
            let salt_slot = format!("0x{:064x}", base_index + U256::from(2));
            
            let token0_result = dex_lite
                .readFromStorage(token0_slot.parse().unwrap())
                .block(BlockNumberOrTag::Latest.into())
                .call()
                .await;
            
            let token1_result = dex_lite
                .readFromStorage(token1_slot.parse().unwrap())
                .block(BlockNumberOrTag::Latest.into())
                .call()
                .await;
            
            let salt_result = dex_lite
                .readFromStorage(salt_slot.parse().unwrap())
                .block(BlockNumberOrTag::Latest.into())
                .call()
                .await;
            
            if let (Ok(token0), Ok(token1), Ok(salt)) = (token0_result, token1_result, salt_result) {
                // Skip if tokens are zero
                if token0.is_zero() || token1.is_zero() {
                    continue;
                }
                
                // Convert to addresses with proper validation
                let token0_addr = Address::from_slice(&token0.to_be_bytes::<32>()[12..]);
                let token1_addr = Address::from_slice(&token1.to_be_bytes::<32>()[12..]);
                
                let dex_key = DexKey {
                    token0: token0_addr,
                    token1: token1_addr,
                    salt: SafeU256::from(salt),
                };
                
                // Calculate dexId like in Solidity: bytes8(keccak256(abi.encode(dexKey)))
                let dex_id = calculate_dex_id(&dex_key);
                
                pools.push(PoolInfo {
                    dex_lite_address: DEX_LITE_ADDRESS,
                    dex_key,
                    dex_id,
                });
            }
        }
        
        // Sort pools by token0, then token1, then salt for deterministic ordering
        pools.sort_by(|a, b| {
            a.dex_key.token0.cmp(&b.dex_key.token0)
                .then_with(|| a.dex_key.token1.cmp(&b.dex_key.token1))
                .then_with(|| a.dex_key.salt.cmp(&b.dex_key.salt))
        });
        
        pools
    }
    
    // Helper function to calculate dexId like in Solidity: bytes8(keccak256(abi.encode(dexKey)))
    fn calculate_dex_id(dex_key: &DexKey) -> SafeU256 {
        // Encode the dex key components as they would be in Solidity abi.encode
        let mut encoded = Vec::new();
        
        // address token0 (32 bytes, left-padded)
        encoded.extend_from_slice(&[0u8; 12]);
        encoded.extend_from_slice(dex_key.token0.as_slice());
        
        // address token1 (32 bytes, left-padded)
        encoded.extend_from_slice(&[0u8; 12]);
        encoded.extend_from_slice(dex_key.token1.as_slice());
        
        // bytes32 salt (32 bytes)
        encoded.extend_from_slice(&dex_key.salt.0.to_be_bytes::<32>());
        
        let hash = keccak256(&encoded);
        
        // Take first 8 bytes as SafeU256
        let mut bytes = [0u8; 32];
        bytes[24..32].copy_from_slice(&hash[0..8]);
        SafeU256::from_big_endian(&bytes)
    }
}

pub mod balancer_v3_stable_surge {
    use alloy_primitives::{address, Address};
    use crate::barter_lib::SafeU256;

    use super::*;
    use crate::{contracts::{BalancerV3StablePoolContract, BalancerV3StableSurgeFactoryContract}, types::balancer_v3_stable_surge::PoolInfo};

    pub async fn get_all_pools<P: Provider<N> + Clone, N: Network>(provider: P) -> Vec<PoolInfo> {
        const FACTORY: Address = address!("0x355bD33F0033066BB3DE396a6d069be57353AD95"); // mainnet
    
        let factory = BalancerV3StableSurgeFactoryContract::new(FACTORY.into(), provider.clone());
        let pools = factory.getPools().call().await.unwrap();
        let futures = pools.into_iter().map(|x| {
            let provider = provider.clone();
            async move {
                let pool_contract = BalancerV3StablePoolContract::new(x.into(), provider);
                let immutable_data = pool_contract.getStablePoolImmutableData().call().await.unwrap();
                
                PoolInfo {
                    address: x,
                    tokens: immutable_data.tokens,
                    decimal_scaling_factors: immutable_data.decimalScalingFactors.into_iter().map(SafeU256::from).collect(),
                    supports_unbalanced_liquidity: false,
                    hook_type: "StableSurge".to_string(),
                }
            }
        });

        let mut pools = futures::future::join_all(futures).await;
        pools.sort_by_key(|x| x.address);
        pools
    }
}