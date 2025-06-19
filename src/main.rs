#![feature(unboxed_closures)]
#![feature(tuple_trait)]
#![feature(iter_array_chunks)]
#![feature(future_join)]
#![feature(let_chains)]
#![feature(iterator_try_collect)]
#![feature(associated_type_defaults)]
#![feature(array_windows)]
#![feature(adt_const_params)]
#![feature(type_changing_struct_update)]
#![feature(stmt_expr_attributes)]
#![feature(generic_arg_infer)]
#![feature(cmp_minmax)]
#![feature(try_blocks)]
#![feature(maybe_uninit_array_assume_init)]
#![feature(const_trait_impl)]
#![feature(impl_trait_in_assoc_type)]
#![feature(macro_metavar_expr)]
#![feature(const_precise_live_drops)]
#![feature(bigint_helper_methods)]
#![feature(try_trait_v2)]
#![feature(try_trait_v2_yeet)]
#![feature(try_trait_v2_residual)]

// Compiled on rustc 1.89.0-nightly (6ccd44760 2025-06-08)

use crate::{barter_lib::{amm_lib::ToExchanges, common::Swap, ChecksumAddress}, model::dodo_v1::SwapDirection};

mod barter_lib; // utility crate, do not modify

mod model;
mod types;
mod discovery;
mod polling;
mod execution;
mod contracts;

#[derive(serde::Deserialize, Debug, Clone)]
pub struct EnvConfig {
    pub mainnet_rpc_url: String,
}

#[tokio::main]
async fn main() {
    dotenvy::dotenv_override().unwrap();
    let env_config: EnvConfig = envy::from_env().unwrap();
    let web3 = web3::Web3::new(web3::transports::Http::new(&env_config.mainnet_rpc_url).unwrap());
    
    let dodos = discovery::dodo_v1::get_all_pools(&web3).await;

    // use tx 0x0fe505f086ecd54ae3490dc0fd99de363ad635d53583bf7750ef30ad66f5a27f as reference
    let tx_block_number = 22637111;
    let input = su256const!(1000000000000000);
    let output =  su256const!(26092);
    let pool = ChecksumAddress::from_const("0x75c23271661d9d143dcb617222bc4bec783eff34");

    let dodo = dodos.iter().find(|x| x.address == pool).unwrap();
    let block = ethcontract::BlockId::Number(ethcontract::BlockNumber::Number((tx_block_number - 1).into())); // tx in block N generally happens on a blockchain state of block N-1
    let flower_data = polling::dodo_v1::get_flower_data(&web3, dodo.clone(), block).await;
    let exchange = flower_data.to_exchanges(&mut barter_lib::amm_lib::EmptyExchangeContext)
        .filter(|x| x.request.direction == SwapDirection::BaseToQuote)
        .next()
        .unwrap();

    let result = exchange.swap(input).unwrap();

    assert_eq!(result, output); // https://www.tdly.co/shared/simulation/7966736a-db6e-4701-b5b5-13a31a6c8a5a

    let encoded_calldata = execution::dodo_v1::encode(input, 1.into(), &exchange.meta);

    println!("Encoded calldata: {:#?}", encoded_calldata);
}
