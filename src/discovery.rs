use alloy::network::Network;
use alloy::providers::Provider;
use crate::barter_lib::ChecksumAddress;

pub mod dodo_v1 {
    use super::*;
    use crate::{contracts::{DodoV1PoolContract, DodoV1RegistryContract}, types::dodo_v1::PoolInfo};

    pub async fn get_all_pools<P: Provider<N> + Clone, N: Network>(provider: P) -> Vec<PoolInfo> {
        const REGISTRY: ChecksumAddress = ChecksumAddress::from_const("0x3a97247df274a17c59a3bd12735ea3fcdfb49950"); // mainnet

        let zoo = DodoV1RegistryContract::new(REGISTRY.into(), provider.clone());
        let pools = zoo.getDODOs().call().await.unwrap();
        let futures = pools.into_iter().map(|x| {
            let provider = provider.clone();
            async move {
                let dodo = DodoV1PoolContract::new(x.into(), provider);
                PoolInfo {
                    address: x.into(),
                    base_token: dodo._BASE_TOKEN_().call().await.unwrap().into(),
                    quote_token: dodo._QUOTE_TOKEN_().call().await.unwrap().into(),
                }
            }
        });

        let mut pools = futures::future::join_all(futures).await;
        pools.sort_by_key(|x| x.address);
        pools
    }
}