#![allow(unused)]

#[derive(Debug, Clone, Copy)]
pub struct DummyProvider;

impl alloy::providers::Provider for DummyProvider {
    fn root(&self) ->  &alloy::providers::RootProvider  {
        unimplemented!("DummyProvider should only be used for encoding and decoding, not for actual network calls.")
    }
}


macro_rules! declare_sol_contract_impl {
    ($name: ident, $const_name: ident, $mod_name: ident, $contract: ident, $instance: ty) => {
        pub mod $mod_name {
            alloy::sol!(
                #[sol(rpc)]
                $contract,
                concat!("abis/", stringify!($name), ".json")
            );
        }

        pub use $mod_name::$contract;

        pub const $const_name: $instance = $contract::new(alloy::primitives::Address::ZERO, DummyProvider);
    };
}

macro_rules! declare_sol_contract{
    ($name: ident) => {
        paste::paste! {
            declare_sol_contract_impl!([<$name:camel>], $name, [<$name:lower _mod>], [<$name:camel Contract>], [<$name:camel Contract>]::[<$name:camel Contract Instance>]<DummyProvider>);
        }
    }
}

// USER CODE BELOW
declare_sol_contract!(DODO_V1_POOL);
declare_sol_contract!(DODO_V1_REGISTRY);
declare_sol_contract!(FLUID_DEX_LITE);
declare_sol_contract!(BALANCER_V3_STABLE_POOL);
declare_sol_contract!(BALANCER_V3_STABLE_SURGE_FACTORY);
declare_sol_contract!(BALANCER_V3_STABLE_SURGE_HOOK);
declare_sol_contract!(BALANCER_V3_ROUTER);
declare_sol_contract!(BALANCER_V3_RECLAMM_FACTORY);
declare_sol_contract!(BALANCER_V3_RECLAMM_POOL);
