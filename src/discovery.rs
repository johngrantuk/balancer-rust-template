use web3::{transports::Http, Web3};

pub mod dodo_v1 {
    use web3::futures::future::join_all;

    use super::*;
    use crate::{barter_lib::ChecksumAddress, contracts::{DodoV1PoolPrototype, DodoV1Registry}, types::dodo_v1::PoolInfo};

    pub async fn get_all_pools(web3: &Web3<Http>) -> Vec<PoolInfo> {
        const REGISTRY: ChecksumAddress = ChecksumAddress::from_const("0x3a97247df274a17c59a3bd12735ea3fcdfb49950"); // mainnet

        let zoo = DodoV1Registry::at(&web3, REGISTRY.0);
        let pools = zoo.get_dod_os().call().await.unwrap();
        let futures = pools.into_iter().map(|x| {
            let web3 = web3;
            async move {
                let dodo = DodoV1PoolPrototype::at(&web3, x);
                PoolInfo {
                    address: x.into(),
                    base_token: dodo.base_token().call().await.unwrap().into(),
                    quote_token: dodo.quote_token().call().await.unwrap().into(),
                }
            }
        });

        let mut pools = join_all(futures).await;
        pools.sort_by_key(|x| x.address);
        pools
    }
}