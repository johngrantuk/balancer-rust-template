#![allow(unused)]
use serde::{Deserialize, Serialize};

use crate::barter_lib::{common::Swap};

pub type Address = alloy_primitives::Address;

pub type TokenAddress<'a> = &'a Address;
pub type ExchangeAddress<'a> = &'a Address;

type Meta = ();

pub trait ExchangeContext {
    fn get_token_id(&mut self, token: TokenAddress) -> Option<TokenId>;
    fn get_exchange_id(&mut self, exchange: ExchangeAddress) -> ExchangeId;
}

#[derive(Debug, Clone)]
pub struct EmptyExchangeContext;

impl ExchangeContext for EmptyExchangeContext {
    fn get_token_id(&mut self, _: TokenAddress) -> Option<TokenId> {
        Some(TokenId(0))
    }

    fn get_exchange_id(&mut self, _: ExchangeAddress) -> ExchangeId {
        ExchangeId(0)
    }
}

pub trait ToExchanges {
    type Ex: Swap;
    type ExIter<'a, T: ExchangeContext + 'a>: Iterator<Item = Self::Ex> + 'a;

    fn to_exchanges<'a, T: ExchangeContext + 'a>(
        self,
        exchange_context: &'a mut T,
    ) -> Self::ExIter<'a, T>;
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub struct ExchangeId(pub u16);

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
pub struct TokenId(pub u16);

#[derive(Debug, Clone)]
pub struct ExchangeInfo {
    pub source: TokenId,
    pub target: TokenId,
    pub exchange_id: ExchangeId
}

impl ExchangeInfo {
    pub fn new(source: TokenId, target: TokenId, exchange_id: ExchangeId) -> Self {
        Self {
            source,
            target,
            exchange_id,
        }
    }
}

pub const ZERO_ADDRESS: Address = Address::ZERO;

pub trait SwapGas {
    type Methods;

    fn swap_gas(&self, gas_storage: &impl GasStorage<Self::Methods>) -> Gas;
}

pub trait GasStorage<T>: Sized {
    fn get_transfer_price(&self, token: TokenId) -> Gas;
    fn get_method_price(&self, method: T) -> Option<Gas>;
    fn get_avg_gas(&self) -> Option<Gas>;
    fn approve_gas(&self, token: TokenId) -> Gas;
}

pub type Gas = u32;


// mostly for debugging purposes
pub trait GetAddress {
    fn get_address(&self) -> Address;
}

#[derive(Debug, Clone)]
pub struct PoolRequestMeta<P, R, M> {
    pub pool_info: P,
    pub request: R,
    #[allow(unused)]
    pub meta: M,
}