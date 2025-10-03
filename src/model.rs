pub mod dodo_v1 {
    use std::sync::Arc;
    use crate::barter_lib::amm_lib::*;

    use crate::barter_lib::common::Swap;
    use crate::types::dodo_v1::RStatus;
    use crate::{
        barter_lib::{amm_lib::ExchangeInfo, safe_math::{MathResult, SafeMathError}, SafeU256}, model::dodo_v1::pricing::{
                get_expected_target,
                rabove_sell_base_token,
                rabove_sell_quote_token,
                rbelow_sell_base_token,
                rbelow_sell_quote_token,
                rone_sell_base_token,
                rone_sell_quote_token,
            }, types::dodo_v1::FlowerData
    };

    pub type DodoV1Error = SafeMathError;
    // in case of more complex erors, use enum with derive_more as following
    // #[derive(Debug, derive_more::From)]
    // pub enum DodoV1Error {
    //     SafeMathError(SafeMathError),
    //     // any other variants go in here
    // }

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    #[repr(u8)]
    pub enum DodoV1Methods {
        SellBaseToken = 0,
        BuyBaseToken = 1,
    }

    #[derive(Debug, PartialEq, Clone)]
    pub enum SwapDirection {
        BaseToQuote,
        QuoteToBase,
    }

    #[derive(Debug, Clone)]
    pub struct DodoV1ExchangeRequest {
        pub direction: SwapDirection,
        pub exchange_info: ExchangeInfo,
    }

    #[derive(Debug, serde::Serialize, serde::Deserialize, Hash, Eq, PartialEq, Clone)]
    #[serde(rename_all = "camelCase")]
    #[serde(deny_unknown_fields)]
    pub struct DodoV1Meta {
        pub pool_address: Address,
        pub is_sell_base: bool,
    }

    #[allow(unused)]
    impl GetAddress for DodoV1Meta {
        fn get_address(&self) -> Address {
            self.pool_address
        }
    }
    #[allow(unused)]
    impl ToExchanges for FlowerData {
        type Ex = DodoV1Exchange;
        type ExIter<'a, T: ExchangeContext + 'a> =
            impl Iterator<Item = Self::Ex> + 'a;

        fn to_exchanges<
            'a,
            T: ExchangeContext + 'a,
        >(
            self,
            context: &'a mut T,
        ) -> Self::ExIter<'a, T> {
            let pool_address = self.pool_info.address;
            let request: Option<_> = try {
                let p = Arc::new(self);
                let fw = DodoV1Exchange {
                    pool_info: Arc::clone(&p),
                    request: DodoV1ExchangeRequest {
                        direction: SwapDirection::BaseToQuote,
                        exchange_info: ExchangeInfo {
                            exchange_id: context.get_exchange_id(&p.pool_info.address),
                            source: context.get_token_id(&p.pool_info.base_token)?,
                            target: context.get_token_id(&p.pool_info.quote_token)?,
                        },
                    },
                    meta: Arc::new(DodoV1Meta {
                        pool_address,
                        is_sell_base: true,
                    }),
                };

                let bw = DodoV1Exchange {
                    pool_info: Arc::clone(&p),
                    request: DodoV1ExchangeRequest {
                        direction: SwapDirection::QuoteToBase,
                        exchange_info: ExchangeInfo {
                            exchange_id: context.get_exchange_id(&p.pool_info.address),
                            source: context.get_token_id(&p.pool_info.quote_token)?,
                            target: context.get_token_id(&p.pool_info.base_token)?,
                        },
                    },
                    meta: Arc::new(DodoV1Meta {
                        pool_address,
                        is_sell_base: false,
                    }),
                };

                [fw, bw].into_iter()
            };

            request.into_iter().flatten()
        }
    }
    
    #[allow(unused)]
    impl Swap for DodoV1Exchange {
        type Error = DodoV1Error;

        #[inline(never)]
        fn swap(&self, amount: SafeU256) -> MathResult<SafeU256, Self::Error> {
            match self.request.direction {
                SwapDirection::BaseToQuote => query_sell_base_token(&self.pool_info, amount),
                SwapDirection::QuoteToBase => query_sell_quote_token(&self.pool_info, amount),
            }
        }
    }

    #[allow(unused)]
    impl SwapGas for DodoV1Exchange {
        type Methods = DodoV1Methods;
        fn swap_gas(&self, gas_storage: &impl GasStorage<Self::Methods>) -> Gas {
            const QUERY_SELL_QUOTE_TOKEN_GAS: Gas = 56713;
            let swap_cost = match self.request.direction {
                SwapDirection::BaseToQuote => gas_storage.get_method_price(DodoV1Methods::SellBaseToken).unwrap_or(142000),
                SwapDirection::QuoteToBase => {
                    gas_storage.get_method_price(DodoV1Methods::BuyBaseToken).unwrap_or(176000) + QUERY_SELL_QUOTE_TOKEN_GAS
                }
            };
            swap_cost + gas_storage.approve_gas(self.request.exchange_info.source)
        }
    }

    /// =========== IMPLEMENTATION DETAILS BELOW ==============

    pub type DodoV1Exchange = PoolRequestMeta<Arc<FlowerData>, DodoV1ExchangeRequest, Arc<DodoV1Meta>>;

    mod dodo_math {
        use crate::{barter_lib::{safe_math::MathResult, SafeU256}, model::dodo_v1::DodoV1Error, u256const};
        use super::decimal_math;
        use crate::barter_lib::safe_math::SafeMathU256Result;

        pub fn general_integrate(v0: impl Into<SafeMathU256Result>, v1: impl Into<SafeMathU256Result>, v2: impl Into<SafeMathU256Result>, i: impl Into<SafeMathU256Result>, k: impl Into<SafeMathU256Result>) -> SafeMathU256Result {
            let v0 = v0.into();
            let v1 = v1.into();
            let v2 = v2.into();
            let i = i.into();
            let k = k.into();

            let fair_amount = decimal_math::mul(i, v1 - v2); // i*delta
            let v0v0v1v2 = decimal_math::div_ceil((v0 * v0) / v1, v2);
            let penalty = decimal_math::mul(k, v0v0v1v2); // k(v0^2/v1/v2)

            decimal_math::mul(fair_amount, (decimal_math::ONE - k) + penalty)
        }

        pub fn solve_quadratic_function_for_trade(
            q0: impl Into<SafeMathU256Result>,
            q1: impl Into<SafeMathU256Result>,
            idelta_b: impl Into<SafeMathU256Result>,
            delta_bsig: bool,
            k: impl Into<SafeMathU256Result>,
        ) -> MathResult<SafeU256, DodoV1Error> {
            let q0 = q0.into();
            let q1 = q1.into();
            let idelta_b = idelta_b.into();
            let k = k.into();

            // calculate -b value and sig
            // -b = (1-k)q1-kQ0^2/q1+i*deltaB
            let mut k_q02q1 = (decimal_math::mul(k, q0) * q0)/(q1); // kQ0^2/q1
            let mut b = decimal_math::mul(decimal_math::ONE - k, q1); // (1-k)q1
            let minusb_sig;
            if delta_bsig {
                b += idelta_b; // (1-k)q1+i*deltaB
            } else {
                k_q02q1 += idelta_b; // i*deltaB+kQ0^2/q1
            }
            if b? >= k_q02q1? {
                b -= k_q02q1;
                minusb_sig = true;
            } else {
                b = k_q02q1 - b;
                minusb_sig = false;
            }

            // calculate sqrt
            let mut square_root = decimal_math::mul(
                (decimal_math::ONE - k)*({ u256const!(4) }),
                decimal_math::mul(k, q0)*(q0)?,
            ); // 4(1-k)kQ0^2
            square_root = decimal_math::sqrt(b*b + (square_root)); // sqrt(b*b+4(1-k)kQ0*q0)

            // final res
            let denominator = (decimal_math::ONE - k) * { u256const!(2) }; // 2(1-k)
            let numerator;
            if minusb_sig {
                numerator = b + square_root;
            } else {
                numerator = square_root - b;
            }

            let result = if delta_bsig {
                decimal_math::div_floor(numerator, denominator)
            } else {
                decimal_math::div_ceil(numerator, denominator)
            };
            (result).cast_err()
        }

        pub fn solve_quadratic_function_for_target(v1: impl Into<SafeMathU256Result>, k: impl Into<SafeMathU256Result>, fair_amount: impl Into<SafeMathU256Result>) -> SafeMathU256Result {
            let v1 = v1.into();
            let k = k.into();
            let fair_amount = fair_amount.into();

            // V0 = v1+v1*(sqrt-1)/2k
            let mut sqrt = decimal_math::div_ceil(decimal_math::mul(k, fair_amount) * { u256const!(4) }, v1);
            sqrt = decimal_math::sqrt((sqrt + decimal_math::ONE) * decimal_math::ONE);
            let premium = decimal_math::div_ceil(sqrt - decimal_math::ONE, k * { u256const!(2) });
            // V0 is greater than or equal to v1 according to the solution
            decimal_math::mul(v1, decimal_math::ONE + premium)
        }

        #[cfg(test)]
        mod tests {
            use crate::{barter_lib::SafeU256, model::dodo_v1::dodo_math::{
                general_integrate,
                solve_quadratic_function_for_target,
            }};

            #[test]
            fn solve_quadratic_function_for_target_test() {
                let r = solve_quadratic_function_for_target(
                    SafeU256::from_dec_str("4177042671075").unwrap(),
                    SafeU256::from_dec_str("800000000000000000").unwrap(),
                    SafeU256::from_dec_str("3410767068").unwrap(),
                ).unwrap();

                assert_eq!(r, SafeU256::from_dec_str("4180451212997").unwrap())
            }

            #[test]
            fn solve_quadratic_function_for_target_test2() {
                let r = solve_quadratic_function_for_target(
                    SafeU256::from_dec_str("3677079410519").unwrap(),
                    SafeU256::from_dec_str("800000000000000000").unwrap(),
                    SafeU256::from_dec_str("3410767068").unwrap(),
                ).unwrap();

                assert_eq!(r, SafeU256::from_dec_str("3680487650341").unwrap())
            }

            #[test]
            fn solve_quadratic_function_for_target_test3() {
                let r = solve_quadratic_function_for_target(
                    SafeU256::from_dec_str("3677587210960").unwrap(),
                    SafeU256::from_dec_str("800000000000000000").unwrap(),
                    SafeU256::from_dec_str("3209299626").unwrap(),
                ).unwrap();

                assert_eq!(r, SafeU256::from_dec_str("3680794273194").unwrap())
            }

            #[test]
            fn general_integrate_test() {
                let r = general_integrate(
                    SafeU256::from_dec_str("2303120503343015860893").unwrap(),
                    SafeU256::from_dec_str("2302846430369179065157").unwrap(),
                    SafeU256::from_dec_str("2294641430369179065157").unwrap(),
                    SafeU256::from_dec_str("3062834672").unwrap(),
                    SafeU256::from_dec_str("800000000000000000").unwrap(),
                ).unwrap();

                assert_eq!(r, SafeU256::from_dec_str("25207249250").unwrap())
            }
        }
    }

    mod decimal_math {
        use crate::{barter_lib::{common::{SU256_ONE, SU256_ZERO}, safe_math::{MathResult, SafeMathU256Result}, u256::{
            pow10_u256,
        }, SafeU256}, u256const};

        pub const ONE: SafeU256 = pow10_u256(18); // 10**18;

        pub fn mul(target: impl Into<SafeMathU256Result>, d: impl Into<SafeMathU256Result>) -> SafeMathU256Result {
            (target.into() * d.into()) / ONE
        }

        pub fn div_floor(target: impl Into<SafeMathU256Result>, d: impl Into<SafeMathU256Result>) -> SafeMathU256Result {
            (target.into() * ONE) / d.into()
        }

        pub fn div_ceil(target: impl Into<SafeMathU256Result>, d: impl Into<SafeMathU256Result>) -> SafeMathU256Result {
            div_ceil_(target.into() * ONE, d.into())
        }

        fn div_ceil_(a: impl Into<SafeMathU256Result>, b: impl Into<SafeMathU256Result>) -> SafeMathU256Result {
            let a = a.into();
            let b = b.into();
            let quotient = a / b;
            let remainder = (a - quotient * b)?;
            if remainder > SU256_ZERO {
                quotient + 1
            } else {
                quotient
            }
        }

        pub fn sqrt(x: impl Into<SafeMathU256Result>) -> SafeMathU256Result {
            let x = x.into()?;
            let mut z = ((x / { u256const!(2) }) + SU256_ONE)?;
            let mut y = x;
            while z < y {
                y = z;
                z = ((x / z + z) / 2)?;
            }
            MathResult::ok(y)
        }
    }

    mod pricing {
        use crate::{barter_lib::{safe_math::{MathResult, SafeMathResult, SafeMathU256Result}, SafeU256}, model::dodo_v1::DodoV1Error, types::dodo_v1::RStatus};

        use super::{
            decimal_math,
            dodo_math,
            FlowerData,
        };
        use crate::model::{
            dodo_v1::{
                decimal_math::{
                    div_floor,
                    ONE,
                },
                dodo_math::general_integrate,
            },
        };

        pub fn rone_sell_base_token(state: &FlowerData, amount: impl Into<SafeMathU256Result>, target_quote_token_amount: impl Into<SafeMathU256Result>) -> MathResult<SafeU256, DodoV1Error> {
            let amount = amount.into();
            let target_quote_token_amount = target_quote_token_amount.into();

            let i = state.oracle_price;
            let q2 = dodo_math::solve_quadratic_function_for_trade(
                target_quote_token_amount,
                target_quote_token_amount,
                decimal_math::mul(i, amount)?,
                false,
                state.k,
            )?;
            (target_quote_token_amount - q2).cast_err()
        }

        pub fn rone_sell_quote_token(
            amount: SafeU256,
            oracle_price: SafeU256,
            base_target: SafeU256,
            _quote_target: SafeU256,
            k: SafeU256,
        ) -> MathResult<SafeU256, DodoV1Error> {
            let i = decimal_math::div_floor(decimal_math::ONE, oracle_price);
            let b2 = dodo_math::solve_quadratic_function_for_trade(
                base_target,
                base_target,
                decimal_math::mul(i, amount)?,
                false,
                k,
            )?;
            base_target - (b2)
        }

        pub fn rbelow_sell_base_token(
            state: &FlowerData,
            amount: SafeU256,
            quote_balance: SafeU256,
            target_quote_amount: SafeU256,
        ) -> MathResult<SafeU256, DodoV1Error> {
            let i = state.oracle_price;
            let q2 = dodo_math::solve_quadratic_function_for_trade(
                target_quote_amount,
                quote_balance,
                decimal_math::mul(i, amount),
                false,
                state.k,
            )?;
            quote_balance - (q2)
        }

        pub fn rbelow_sell_quote_token(
            amount: SafeU256,
            quote_balance: SafeU256,
            quote_target: SafeU256,
            oracle_price: SafeU256,
            k: SafeU256,
        ) -> MathResult<SafeU256, DodoV1Error> {
            let q1 = quote_balance + (amount);
            let i = div_floor(ONE, oracle_price);
            general_integrate(quote_target, q1, quote_balance, i, k)
        }

        fn rbelow_back_to_one(state: &FlowerData) -> SafeMathU256Result {
            let spare_base = state.base_balance - state.target_base_token_amount;
            let price = state.oracle_price;
            let fair_amount = decimal_math::mul(spare_base, price);
            let new_target_quote =
                dodo_math::solve_quadratic_function_for_target(state.quote_balance, state.k, fair_amount);
            new_target_quote - state.quote_balance
        }

        pub fn rabove_sell_quote_token(
            amount: SafeU256,
            oracle_price: SafeU256,
            base_target: SafeU256,
            _quote_target: SafeU256,
            k: SafeU256,
            base_balance: SafeU256,
        ) -> MathResult<SafeU256, DodoV1Error> {
            let i = decimal_math::div_floor(decimal_math::ONE, oracle_price);
            let b2 = dodo_math::solve_quadratic_function_for_trade(
                base_target,
                base_balance,
                decimal_math::mul(i, amount),
                false,
                k,
            )?;
            base_balance - (b2)
        }

        pub fn rabove_sell_base_token(
            state: &FlowerData,
            amount: impl Into<SafeMathU256Result>,
            base_balance: impl Into<SafeMathU256Result>,
            target_base_amount: impl Into<SafeMathU256Result>,
        ) -> SafeMathU256Result {
            let amount = amount.into();
            let base_balance = base_balance.into();
            let target_base_amount = target_base_amount.into();

            let b1 = base_balance + amount;
            rabove_integrate(state, target_base_amount, b1, base_balance)
        }

        fn rabove_back_to_one(state: &FlowerData) -> SafeMathU256Result {
            let spare_quote = state.quote_balance - state.target_quote_token_amount;
            let price = state.oracle_price;
            let fair_amount = decimal_math::div_floor(spare_quote, price);
            let new_target_base = dodo_math::solve_quadratic_function_for_target(state.base_balance, state.k, fair_amount);
            new_target_base - state.base_balance
        }

        pub fn get_expected_target(state: &FlowerData) -> SafeMathResult<(SafeU256, SafeU256)> {
            let q = state.quote_balance;
            let b = state.base_balance;

            SafeMathResult::ok(match state.r_status {
                RStatus::One => (state.target_base_token_amount, state.target_quote_token_amount),
                RStatus::AboveOne => {
                    let pay_base_token = rabove_back_to_one(state);
                    ((b + pay_base_token)?, state.target_quote_token_amount)
                }
                RStatus::BelowOne => {
                    let pay_quote_token = rbelow_back_to_one(state);
                    (state.target_base_token_amount, (q + pay_quote_token)?)
                }
            })
        }

        fn rabove_integrate(state: &FlowerData, b0: impl Into<SafeMathU256Result>, b1: impl Into<SafeMathU256Result>, b2: impl Into<SafeMathU256Result>) -> SafeMathU256Result {
            let i = state.oracle_price;
            dodo_math::general_integrate(b0, b1, b2, i, state.k)
        }

        #[cfg(test)]
        mod tests {
            use std::sync::Arc;

            use alloy_primitives::address;

            use crate::{
                barter_lib::{common::Swap, safe_math::SafeMathError, SafeU256}, model::dodo_v1::{
                        pricing::{
                            get_expected_target,
                            rbelow_back_to_one,
                            rbelow_sell_base_token,
                        }, DodoV1ExchangeRequest, DodoV1Meta, FlowerData, PoolRequestMeta, SwapDirection
                    }, su256const, types::dodo_v1::RStatus
            };

            use crate::barter_lib::amm_lib::{Address, ExchangeId, ExchangeInfo, TokenId};

            use crate::types::dodo_v1::PoolInfo as DodoV1PoolInfo;

            #[test]
            fn rbelow_sell_base_token_test() {
                let state = FlowerData {
                    pool_info: DodoV1PoolInfo {
                        base_token: Address::ZERO,
                        quote_token: Address::ZERO,
                        address: Address::ZERO,
                    },
                    k: SafeU256::from_dec_str("800000000000000000").unwrap(),
                    base_balance: SafeU256::from_dec_str("2314909308192411380470").unwrap(),
                    quote_balance: SafeU256::from_dec_str("3677587210960").unwrap(),
                    oracle_price: SafeU256::from_dec_str("3125108935").unwrap(),
                    target_base_token_amount: SafeU256::from_dec_str("2313882368110303957460").unwrap(),
                    target_quote_token_amount: SafeU256::from_dec_str("3680794606274").unwrap(),
                    r_status: RStatus::BelowOne, 
                    mt_fee_rate: SafeU256::from_dec_str("1000000000000000").unwrap(),
                    lp_fee_rate: SafeU256::from_dec_str("4000000000000000").unwrap(),
                };

                let r = rbelow_sell_base_token(
                    &state,
                    SafeU256::from_dec_str("8205000000000000000").unwrap(),
                    SafeU256::from_dec_str("3677587210960").unwrap(),
                    SafeU256::from_dec_str("3680794273194").unwrap(),
                )
                .unwrap();

                assert_eq!(r, SafeU256::from_dec_str("25463693890").unwrap())
            }

            #[test]
            fn rbelow_back_to_one_test() {
                let state = FlowerData {
                    pool_info: DodoV1PoolInfo {
                        base_token: Address::ZERO,
                        quote_token: Address::ZERO,
                        address: Address::ZERO,
                    },
                    k: SafeU256::from_dec_str("800000000000000000").unwrap(),
                    base_balance: SafeU256::from_dec_str("2314909308192411380470").unwrap(),
                    quote_balance: SafeU256::from_dec_str("3677587210960").unwrap(),
                    oracle_price: SafeU256::from_dec_str("3125108935").unwrap(),
                    target_base_token_amount: SafeU256::from_dec_str("2313882368110303957460").unwrap(),
                    target_quote_token_amount: SafeU256::from_dec_str("3680794606274").unwrap(),
                    r_status: RStatus::BelowOne,
                    mt_fee_rate: SafeU256::from_dec_str("1000000000000000").unwrap(),
                    lp_fee_rate: SafeU256::from_dec_str("4000000000000000").unwrap(),
                };

                let r = rbelow_back_to_one(&state).unwrap();

                assert_eq!(r, SafeU256::from_dec_str("3207062234").unwrap())
            }

            #[test]
            fn get_expected_target_test() {
                let state = FlowerData {
                    pool_info: DodoV1PoolInfo {
                        base_token: Address::ZERO,
                        quote_token: Address::ZERO,
                        address: Address::ZERO,
                    },
                    k: SafeU256::from_dec_str("800000000000000000").unwrap(),
                    base_balance: SafeU256::from_dec_str("2314909308192411380470").unwrap(),
                    quote_balance: SafeU256::from_dec_str("3677587210960").unwrap(),
                    oracle_price: SafeU256::from_dec_str("3125108935").unwrap(),
                    target_base_token_amount: SafeU256::from_dec_str("2313882368110303957460").unwrap(),
                    target_quote_token_amount: SafeU256::from_dec_str("3680794606274").unwrap(),
                    r_status: RStatus::BelowOne,
                    mt_fee_rate: SafeU256::from_dec_str("1000000000000000").unwrap(),
                    lp_fee_rate: SafeU256::from_dec_str("4000000000000000").unwrap(),
                };

                let (r1, r2) = get_expected_target(&state).unwrap();

                assert_eq!(r1, SafeU256::from_dec_str("2313882368110303957460").unwrap());
                assert_eq!(r2, SafeU256::from_dec_str("3680794273194").unwrap());
            }

            #[test]
            fn get_expected_target_test2() {
                let state = FlowerData {
                    pool_info: DodoV1PoolInfo {
                        base_token: Address::ZERO,
                        quote_token: Address::ZERO,
                        address: Address::ZERO,
                    },
                    k: SafeU256::from_dec_str("800000000000000000").unwrap(), //
                    base_balance: SafeU256::from_dec_str("2302846430369179065157").unwrap(), //
                    quote_balance: SafeU256::from_dec_str("4081547189062").unwrap(), //
                    oracle_price: SafeU256::from_dec_str("3024983253").unwrap(), //
                    target_base_token_amount: SafeU256::from_dec_str("2313882368110303957460").unwrap(),
                    target_quote_token_amount: SafeU256::from_dec_str("4080707668929").unwrap(), //
                    r_status: RStatus::AboveOne,                                             //
                    mt_fee_rate: SafeU256::from_dec_str("1000000000000000").unwrap(),            //
                    lp_fee_rate: SafeU256::from_dec_str("4000000000000000").unwrap(),            //
                };

                let (r1, r2) = get_expected_target(&state).unwrap();

                assert_eq!(r1, SafeU256::from_dec_str("2303123932470247648079").unwrap());
                assert_eq!(r2, SafeU256::from_dec_str("4080707668929").unwrap());
            }

            #[test]
            fn query_sell_base_token() {
                let ex = PoolRequestMeta {
                    pool_info: Arc::new(FlowerData {
                        pool_info: DodoV1PoolInfo {
                            base_token: address!("0x4691937a7508860F876c9c0a2a617E7d9E945D4B"),
                            quote_token: address!("0xdAC17F958D2ee523a2206206994597C13D831ec7"),
                            address: address!("0x181D93EA28023bf40C8bB94796c55138719803B4"),
                        },
                        oracle_price: su256const!(30000),
                        k: su256const!(350000000000000000),
                        base_balance: su256const!(0),
                        quote_balance: su256const!(103695978797),
                        target_base_token_amount: su256const!(0),
                        target_quote_token_amount: su256const!(1696933535),
                        r_status: RStatus::One,
                        lp_fee_rate: su256const!(2000000000000000),
                        mt_fee_rate: su256const!(0),
                    }),
                    request: DodoV1ExchangeRequest {
                        direction: SwapDirection::BaseToQuote,
                        exchange_info: ExchangeInfo {
                            source: TokenId(144),
                            target: TokenId(29),
                            exchange_id: ExchangeId(748),
                        },
                    },
                    meta: Arc::new(DodoV1Meta {
                        pool_address: address!("0x181D93EA28023bf40C8bB94796c55138719803B4"),
                        is_sell_base: false,
                    }),
                };

                let result = ex.swap(su256const!(1000000000000000000)).unwrap();
                assert_eq!(result,su256const!(29941));
            }

            #[test]
            fn query_sell_quote_token() {
                let ex = PoolRequestMeta {
                    pool_info: Arc::new(FlowerData {
                        pool_info: DodoV1PoolInfo {
                            base_token: address!("0x4691937a7508860F876c9c0a2a617E7d9E945D4B"),
                            quote_token: address!("0xdAC17F958D2ee523a2206206994597C13D831ec7"),
                            address: address!("0x181D93EA28023bf40C8bB94796c55138719803B4"),
                        },
                        oracle_price: su256const!(30000),
                        k: su256const!(350000000000000000),
                        base_balance: su256const!(0),
                        quote_balance: su256const!(103695978797),
                        target_base_token_amount: su256const!(0),
                        target_quote_token_amount: su256const!(1696933535),
                        r_status: RStatus::One,
                        lp_fee_rate: su256const!(2000000000000000),
                        mt_fee_rate: su256const!(0),
                    }),
                    request: DodoV1ExchangeRequest {
                        direction: SwapDirection::QuoteToBase,
                        exchange_info: ExchangeInfo {
                            source: TokenId(29),
                            target: TokenId(144),
                            exchange_id: ExchangeId(749),
                        },
                    },
                    meta: Arc::new(DodoV1Meta {
                        pool_address: address!("0x181D93EA28023bf40C8bB94796c55138719803B4"),
                        is_sell_base: false,
                    }),
                };

                let result = ex.swap(su256const!(1000000000000000000)).unwrap_err();
                assert_eq!(result, SafeMathError::Div);
            }
        }
    }

    // Note that this code is based on DODOSellHelper at
    // 0x533dA777aeDCE766CEAe696bf90f8541A4bA80Eb DODO pool implementation is
    // equivalent but we're not interested in it
    fn query_sell_base_token(state: &FlowerData, amount: SafeU256) -> MathResult<SafeU256, DodoV1Error> {
        let mut receive_quote;

        let new_rstatus;

        let (new_base_target, new_quote_target) = get_expected_target(state)?;
        let sell_base_amount = amount;

        match state.r_status {
            RStatus::One => {
                receive_quote = rone_sell_base_token(state, sell_base_amount, new_quote_target)?;
                new_rstatus = RStatus::BelowOne;
            }
            RStatus::AboveOne => {
                let back_to_one_pay_base = (new_base_target - state.base_balance)?;
                let back_to_one_receive_quote = (state.quote_balance - new_quote_target)?;
                if sell_base_amount < back_to_one_pay_base {
                    receive_quote = rabove_sell_base_token(state, sell_base_amount, state.base_balance, new_base_target)?;
                    new_rstatus = RStatus::AboveOne;
                    if receive_quote > back_to_one_receive_quote {
                        receive_quote = back_to_one_receive_quote;
                    }
                } else if sell_base_amount == back_to_one_pay_base {
                    receive_quote = back_to_one_receive_quote;
                    new_rstatus = RStatus::One;
                } else {
                    receive_quote = (back_to_one_receive_quote
                        + rone_sell_base_token(state, sell_base_amount - back_to_one_pay_base, new_quote_target)?)?;
                    new_rstatus = RStatus::BelowOne;
                }
            }
            RStatus::BelowOne => {
                receive_quote = rbelow_sell_base_token(state, sell_base_amount, state.quote_balance, new_quote_target)?;
                new_rstatus = RStatus::BelowOne;
            }
        }

        let lp_fee_quote = decimal_math::mul(receive_quote, state.lp_fee_rate);
        let mt_fee_quote = decimal_math::mul(receive_quote, state.mt_fee_rate);
        receive_quote = ((receive_quote - lp_fee_quote) - mt_fee_quote)?;

        let _unused = (
            receive_quote,
            lp_fee_quote,
            mt_fee_quote,
            new_rstatus,
            new_quote_target,
            new_base_target,
        );
        MathResult::ok(receive_quote)
    }

    // Note that this code is based on DODOSellHelper at
    // 0x533dA777aeDCE766CEAe696bf90f8541A4bA80Eb DODO pool implementation isn't
    // suitable for us
    fn query_sell_quote_token(state: &FlowerData, amount: SafeU256) -> MathResult<SafeU256, DodoV1Error> {
        let (base_target, quote_target) = get_expected_target(state)?;
        let bought_amount = match state.r_status {
            RStatus::One => rone_sell_quote_token(amount, state.oracle_price, base_target, quote_target, state.k)?,
            RStatus::AboveOne => rabove_sell_quote_token(
                amount,
                state.oracle_price,
                base_target,
                quote_target,
                state.k,
                state.base_balance,
            )?,
            RStatus::BelowOne => {
                let back_one_base = state.base_balance -(base_target);
                let back_one_quote = (quote_target - state.quote_balance)?;
                if amount <= back_one_quote {
                    rbelow_sell_quote_token(amount, state.quote_balance, quote_target, state.oracle_price, state.k)?
                } else {
                    (back_one_base
                        + rone_sell_quote_token(
                            (amount - back_one_quote)?,
                            state.oracle_price,
                            base_target,
                            quote_target,
                            state.k,
                        )?)?
                }
            }
        };
        decimal_math::div_floor(
            bought_amount,
            decimal_math::ONE + state.mt_fee_rate + state.lp_fee_rate,
        ).cast_err()
    }

    #[cfg(test)]
    mod tests {
        use alloy_primitives::address;

        use crate::{su256const, types::dodo_v1::{PoolInfo, RStatus}};

        use super::*;

        #[test]
        fn test_complete() {
            let pool: FlowerData = FlowerData {
                pool_info: PoolInfo {
                    address: address!("0x75c23271661d9d143dcb617222bc4bec783eff34"),
                    base_token: address!("0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2"),
                    quote_token: address!("0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48"),
                },
                k: su256const!(800000000000000000),
                base_balance: su256const!(167593430029662844614),
                quote_balance: su256const!(42821007566),
                oracle_price: su256const!(2689951003),
                target_base_token_amount: su256const!(167620016773240185694),
                target_quote_token_amount: su256const!(42744296332),
                r_status: RStatus::AboveOne,
                mt_fee_rate: su256const!(0),
                lp_fee_rate: su256const!(990000000000000000),
            };

            let pool_request_meta: Vec<_> = pool.to_exchanges(&mut EmptyExchangeContext {}).collect();
            let pool_request_meta = pool_request_meta.into_iter().find(|x| x.request.direction == SwapDirection::QuoteToBase).unwrap();
            let result_ok = pool_request_meta.swap(su256const!(100000000000000000));
            let result_err = pool_request_meta.swap(su256const!(29863105395735596688882276529210));
            assert_eq!(result_ok.unwrap(), su256const!(84217500197173276779));
            assert_eq!(SafeMathError::Mul, result_err.unwrap_err());
        }
    }
}

pub mod fluid_dex_lite {
    use std::sync::Arc;
    use crate::barter_lib::amm_lib::*;
    use crate::barter_lib::common::Swap;
    use crate::barter_lib::{
        amm_lib::ExchangeInfo, 
        safe_math::{MathResult, SafeMathError}, 
        SafeU256
    };
    use crate::types::fluid_dex_lite::{
        FlowerData, 
        UnpackedDexVariables, 
        PricingResult, 

        BITS_DEX_LITE_DEX_VARIABLES_FEE,
        BITS_DEX_LITE_DEX_VARIABLES_REVENUE_CUT,
        BITS_DEX_LITE_DEX_VARIABLES_REBALANCING_STATUS,
        BITS_DEX_LITE_DEX_VARIABLES_CENTER_PRICE_SHIFT_ACTIVE,
        BITS_DEX_LITE_DEX_VARIABLES_CENTER_PRICE,
        BITS_DEX_LITE_DEX_VARIABLES_CENTER_PRICE_CONTRACT_ADDRESS,
        BITS_DEX_LITE_DEX_VARIABLES_RANGE_PERCENT_SHIFT_ACTIVE,
        BITS_DEX_LITE_DEX_VARIABLES_UPPER_PERCENT,
        BITS_DEX_LITE_DEX_VARIABLES_LOWER_PERCENT,
        BITS_DEX_LITE_DEX_VARIABLES_THRESHOLD_PERCENT_SHIFT_ACTIVE,
        BITS_DEX_LITE_DEX_VARIABLES_UPPER_SHIFT_THRESHOLD_PERCENT,
        BITS_DEX_LITE_DEX_VARIABLES_LOWER_SHIFT_THRESHOLD_PERCENT,
        BITS_DEX_LITE_DEX_VARIABLES_TOKEN_0_DECIMALS,
        BITS_DEX_LITE_DEX_VARIABLES_TOKEN_1_DECIMALS,
        BITS_DEX_LITE_DEX_VARIABLES_TOKEN_0_TOTAL_SUPPLY_ADJUSTED,
        BITS_DEX_LITE_DEX_VARIABLES_TOKEN_1_TOTAL_SUPPLY_ADJUSTED,
        BITS_DEX_LITE_CENTER_PRICE_SHIFT_SHIFTING_TIME,
        BITS_DEX_LITE_CENTER_PRICE_SHIFT_MAX_CENTER_PRICE,
        BITS_DEX_LITE_CENTER_PRICE_SHIFT_MIN_CENTER_PRICE,
        BITS_DEX_LITE_RANGE_SHIFT_OLD_UPPER_RANGE_PERCENT,
        BITS_DEX_LITE_RANGE_SHIFT_OLD_LOWER_RANGE_PERCENT,
        BITS_DEX_LITE_RANGE_SHIFT_TIME_TO_SHIFT,
        BITS_DEX_LITE_RANGE_SHIFT_TIMESTAMP,

        X1, X2, X5, X7, X13, X14, X19, X20, X24, X28, X33, X40, X60,
        FOUR_DECIMALS, SIX_DECIMALS, PRICE_PRECISION, TOKENS_DECIMALS_PRECISION,
        DEFAULT_EXPONENT_SIZE, DEFAULT_EXPONENT_MASK, MINIMUM_LIQUIDITY_SWAP,
    };

    pub use crate::types::fluid_dex_lite::FluidDexLiteError;

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    #[repr(u8)]
    pub enum FluidDexLiteMethods {
        #[allow(dead_code)] // Used in gas calculations (line 149), but compiler doesn't detect it
        SwapSingle = 0,
    }

    #[derive(Debug, PartialEq, Clone)]
    pub enum SwapDirection {
        Token0ToToken1,
        Token1ToToken0,
    }

    #[derive(Debug, Clone)]
    pub struct FluidDexLiteExchangeRequest {
        pub direction: SwapDirection,
        #[allow(dead_code)] // Used in gas calculations (line 150), but compiler doesn't detect it
        pub exchange_info: ExchangeInfo,
    }

    #[derive(Debug, serde::Serialize, serde::Deserialize, Hash, Eq, PartialEq, Clone)]
    #[serde(rename_all = "camelCase")]
    #[serde(deny_unknown_fields)]
    pub struct FluidDexLiteMeta {
        pub dex_lite_address: Address,
        pub dex_key: crate::types::fluid_dex_lite::DexKey,
        pub swap0_to1: bool,
    }

    impl GetAddress for FluidDexLiteMeta {
        fn get_address(&self) -> Address {
            self.dex_lite_address
        }
    }

    impl ToExchanges for FlowerData {
        type Ex = FluidDexLiteExchange;
        type ExIter<'a, T: ExchangeContext + 'a> = impl Iterator<Item = Self::Ex> + 'a;

        fn to_exchanges<'a, T: ExchangeContext + 'a>(
            self,
            context: &'a mut T,
        ) -> Self::ExIter<'a, T> {
            let dex_lite_address = self.pool_info.dex_lite_address;
            let dex_key = self.pool_info.dex_key.clone();
            
            let request: Option<_> = try {
                let p = Arc::new(self);
                
                let fw = FluidDexLiteExchange {
                    pool_info: Arc::clone(&p),
                    request: FluidDexLiteExchangeRequest {
                        direction: SwapDirection::Token0ToToken1,
                        exchange_info: ExchangeInfo {
                            exchange_id: context.get_exchange_id(&dex_lite_address),
                            source: context.get_token_id(&p.pool_info.dex_key.token0)?,
                            target: context.get_token_id(&p.pool_info.dex_key.token1)?,
                        },
                    },
                    meta: Arc::new(FluidDexLiteMeta {
                        dex_lite_address,
                        dex_key: dex_key.clone(),
                        swap0_to1: true,
                    }),
                };

                let bw = FluidDexLiteExchange {
                    pool_info: Arc::clone(&p),
                    request: FluidDexLiteExchangeRequest {
                        direction: SwapDirection::Token1ToToken0,
                        exchange_info: ExchangeInfo {
                            exchange_id: context.get_exchange_id(&dex_lite_address),
                            source: context.get_token_id(&p.pool_info.dex_key.token1)?,
                            target: context.get_token_id(&p.pool_info.dex_key.token0)?,
                        },
                    },
                    meta: Arc::new(FluidDexLiteMeta {
                        dex_lite_address,
                        dex_key,
                        swap0_to1: false,
                    }),
                };

                [fw, bw].into_iter()
            };

            request.into_iter().flatten()
        }
    }
    
    impl Swap for FluidDexLiteExchange {
        type Error = FluidDexLiteError;

        #[inline(never)]
        fn swap(&self, amount: SafeU256) -> MathResult<SafeU256, Self::Error> {
            match self.request.direction {
                SwapDirection::Token0ToToken1 => calculate_swap_0_to_1(&self.pool_info, amount),
                SwapDirection::Token1ToToken0 => calculate_swap_1_to_0(&self.pool_info, amount),
            }
        }
    }

    impl SwapGas for FluidDexLiteExchange {
        type Methods = FluidDexLiteMethods;
        fn swap_gas(&self, gas_storage: &impl GasStorage<Self::Methods>) -> Gas {
            const SWAP_SINGLE_GAS: Gas = 10000; // FluidDexLite swap gas cost
            gas_storage.get_method_price(FluidDexLiteMethods::SwapSingle).unwrap_or(SWAP_SINGLE_GAS) + 
            gas_storage.approve_gas(self.request.exchange_info.source)
        }
    }

    /// =========== IMPLEMENTATION DETAILS BELOW ==============

    pub type FluidDexLiteExchange = PoolRequestMeta<Arc<FlowerData>, FluidDexLiteExchangeRequest, Arc<FluidDexLiteMeta>>;

    // Math functions for FluidDexLite calculations
    mod fluid_math {
        use super::*;




        // Square root implementation for SafeU256
        pub fn sqrt(value: SafeU256) -> MathResult<SafeU256, FluidDexLiteError> {
            if value < SafeU256::from(2u64) {
                return MathResult::ok(value);
            }

            let mut x = value;
            let mut result = value;

            // Newton's method
            while x > SafeU256::zero() {
                x = ((result + (value / result)?)? / SafeU256::from(2u64))?;
                if x >= result {
                    break;
                }
                result = x;
            }

            MathResult::ok(result)
        }

        // Expand center price from compressed format
        pub fn expand_center_price(center_price: SafeU256) -> MathResult<SafeU256, FluidDexLiteError> {
            let mantissa = center_price >> DEFAULT_EXPONENT_SIZE;
            let exponent = center_price & DEFAULT_EXPONENT_MASK;
            let result = mantissa << exponent;
            MathResult::ok(result)
        }

        // Helper function for linear interpolation during shifting
        pub fn calc_shifting_done(
            current: SafeU256,
            old: SafeU256,
            time_passed: SafeU256,
            shift_duration: SafeU256,
        ) -> MathResult<SafeU256, FluidDexLiteError> {
            if current > old {
                let diff = (current - old)?;
                let adjustment = ((diff * time_passed)? / shift_duration)?;
                (old + adjustment).cast_err()
            } else {
                let diff = (old - current)?;
                let adjustment = ((diff * time_passed)? / shift_duration)?;
                (old - adjustment).cast_err()
            }
        }

        // Calculate reserves outside range
        pub fn calculate_reserves_outside_range(
            geometric_mean: SafeU256,
            pa: SafeU256,
            rx: SafeU256,
            ry: SafeU256,
        ) -> MathResult<(SafeU256, SafeU256), FluidDexLiteError> {
            let p1 = (pa - geometric_mean)?;
            
            let numerator = ((geometric_mean * rx)? + (ry * PRICE_PRECISION)?)?;
            let p2 = (numerator / ((SafeU256::from(2u64) * p1)?))?;
            
            let term1 = ((rx * ry)? * PRICE_PRECISION)?;
            let discriminant = ((term1 / p1)? + (p2 * p2)?)?;
            
            let sqrt_discriminant = sqrt(discriminant)?;
            let xa = (p2 + sqrt_discriminant)?;
            let yb = ((xa * geometric_mean)? / PRICE_PRECISION)?;
            
            MathResult::ok((xa, yb))
        }
    }

    // Unpack dex variables from the packed uint256
    pub fn unpack_dex_variables(dex_variables: SafeU256) -> UnpackedDexVariables {
        UnpackedDexVariables {
            fee: (dex_variables >> SafeU256::from(BITS_DEX_LITE_DEX_VARIABLES_FEE)) & X13,
            revenue_cut: (dex_variables >> SafeU256::from(BITS_DEX_LITE_DEX_VARIABLES_REVENUE_CUT)) & X7,
            rebalancing_status: (dex_variables >> SafeU256::from(BITS_DEX_LITE_DEX_VARIABLES_REBALANCING_STATUS)) & X2,
            center_price_shift_active: ((dex_variables >> SafeU256::from(BITS_DEX_LITE_DEX_VARIABLES_CENTER_PRICE_SHIFT_ACTIVE)) & X1) == SafeU256::one(),
            center_price: (dex_variables >> SafeU256::from(BITS_DEX_LITE_DEX_VARIABLES_CENTER_PRICE)) & X40,
            center_price_contract_address: (dex_variables >> SafeU256::from(BITS_DEX_LITE_DEX_VARIABLES_CENTER_PRICE_CONTRACT_ADDRESS)) & X19,
            range_percent_shift_active: ((dex_variables >> SafeU256::from(BITS_DEX_LITE_DEX_VARIABLES_RANGE_PERCENT_SHIFT_ACTIVE)) & X1) == SafeU256::one(),
            upper_percent: (dex_variables >> SafeU256::from(BITS_DEX_LITE_DEX_VARIABLES_UPPER_PERCENT)) & X14,
            lower_percent: (dex_variables >> SafeU256::from(BITS_DEX_LITE_DEX_VARIABLES_LOWER_PERCENT)) & X14,
            threshold_percent_shift_active: ((dex_variables >> SafeU256::from(BITS_DEX_LITE_DEX_VARIABLES_THRESHOLD_PERCENT_SHIFT_ACTIVE)) & X1) == SafeU256::one(),
            upper_shift_threshold_percent: (dex_variables >> SafeU256::from(BITS_DEX_LITE_DEX_VARIABLES_UPPER_SHIFT_THRESHOLD_PERCENT)) & X7,
            lower_shift_threshold_percent: (dex_variables >> SafeU256::from(BITS_DEX_LITE_DEX_VARIABLES_LOWER_SHIFT_THRESHOLD_PERCENT)) & X7,
            token0_decimals: (dex_variables >> SafeU256::from(BITS_DEX_LITE_DEX_VARIABLES_TOKEN_0_DECIMALS)) & X5,
            token1_decimals: (dex_variables >> SafeU256::from(BITS_DEX_LITE_DEX_VARIABLES_TOKEN_1_DECIMALS)) & X5,
            token0_total_supply_adjusted: (dex_variables >> SafeU256::from(BITS_DEX_LITE_DEX_VARIABLES_TOKEN_0_TOTAL_SUPPLY_ADJUSTED)) & X60,
            token1_total_supply_adjusted: (dex_variables >> SafeU256::from(BITS_DEX_LITE_DEX_VARIABLES_TOKEN_1_TOTAL_SUPPLY_ADJUSTED)) & X60,
        }
    }

    // Calculate current range percents (equivalent to _calcRangeShifting)
    fn calc_range_shifting(
        upper_range: SafeU256,
        lower_range: SafeU256,
        range_shift: SafeU256,
        simulation_timestamp: SafeU256,
    ) -> MathResult<(SafeU256, SafeU256), FluidDexLiteError> {
        let shift_duration = (range_shift >> SafeU256::from(BITS_DEX_LITE_RANGE_SHIFT_TIME_TO_SHIFT)) & X20;
        let start_timestamp = (range_shift >> SafeU256::from(BITS_DEX_LITE_RANGE_SHIFT_TIMESTAMP)) & X33;

        if (start_timestamp + shift_duration)? < simulation_timestamp {
            // shifting fully done
            return MathResult::ok((upper_range, lower_range));
        }

        let time_passed = (simulation_timestamp - start_timestamp)?;
        let old_upper_range = (range_shift >> SafeU256::from(BITS_DEX_LITE_RANGE_SHIFT_OLD_UPPER_RANGE_PERCENT)) & X14;
        let old_lower_range = (range_shift >> SafeU256::from(BITS_DEX_LITE_RANGE_SHIFT_OLD_LOWER_RANGE_PERCENT)) & X14;

        let new_upper = fluid_math::calc_shifting_done(upper_range, old_upper_range, time_passed, shift_duration)?;
        let new_lower = fluid_math::calc_shifting_done(lower_range, old_lower_range, time_passed, shift_duration)?;

        MathResult::ok((new_upper, new_lower))
    }



    // Full pricing calculation (equivalent to _getPricesAndReserves)
    pub fn get_prices_and_reserves(
        state: &FlowerData,
    ) -> MathResult<PricingResult, FluidDexLiteError> {
        // Calculate simulation timestamp using BlockMeta (Barter team guidance)
        // "timestamp + avg_block_interval to get the correct prediction"
        let next_block_timestamp_ms = state.block_meta.timestamp * 1000 + state.block_meta.avg_block_interval_ms;
        let simulation_timestamp = SafeU256::from(next_block_timestamp_ms / 1000);

        let unpacked_vars = unpack_dex_variables(state.dex_variables);

        // Calculate center price
        let mut center_price: SafeU256;

        // Revert if external price contract is configured
        if unpacked_vars.center_price_contract_address != SafeU256::zero() {
            return MathResult::err(FluidDexLiteError::MathError(SafeMathError::Div)); // External price contracts not supported
        }

        // Revert if center price shifting is active  
        if unpacked_vars.center_price_shift_active {
            return MathResult::err(FluidDexLiteError::MathError(SafeMathError::Div)); // Center price shifting not supported
        }

        // Use stored center price
        center_price = fluid_math::expand_center_price(unpacked_vars.center_price)?;

        // Calculate range percents
        let mut upper_range_percent = unpacked_vars.upper_percent;
        let mut lower_range_percent = unpacked_vars.lower_percent;

        if unpacked_vars.range_percent_shift_active {
            let (new_upper, new_lower) = calc_range_shifting(
                upper_range_percent,
                lower_range_percent,
                state.range_shift,
                simulation_timestamp,
            )?;
            upper_range_percent = new_upper;
            lower_range_percent = new_lower;
        }

        // Calculate range prices
        let mut upper_range_price = ((center_price * FOUR_DECIMALS)? / (FOUR_DECIMALS - upper_range_percent)?)?;
        let mut lower_range_price = ((center_price * (FOUR_DECIMALS - lower_range_percent)?)? / FOUR_DECIMALS)?;

        // Handle rebalancing logic
        let rebalancing_status = unpacked_vars.rebalancing_status;

        if rebalancing_status > SafeU256::one() {
            let mut center_price_shift_data = SafeU256::zero();

            if rebalancing_status == SafeU256::from(2u64) {
                // Price shifting towards upper range
                center_price_shift_data = state.center_price_shift;
                let shifting_time = (center_price_shift_data >> SafeU256::from(BITS_DEX_LITE_CENTER_PRICE_SHIFT_SHIFTING_TIME)) & X24;
                let last_interaction_timestamp = center_price_shift_data & X33; // BITS_DEX_LITE_CENTER_PRICE_SHIFT_LAST_INTERACTION_TIMESTAMP = 0
                let time_elapsed = (simulation_timestamp - last_interaction_timestamp)?;

                if time_elapsed < shifting_time {
                    let price_diff = (upper_range_price - center_price)?;
                    let adjustment = (price_diff * time_elapsed)? / shifting_time;
                    center_price = (center_price + adjustment)?;
                } else {
                    // 100% price shifted
                    center_price = upper_range_price;
                }
            } else if rebalancing_status == SafeU256::from(3u64) {
                // Price shifting towards lower range
                center_price_shift_data = state.center_price_shift;
                let shifting_time = (center_price_shift_data >> SafeU256::from(BITS_DEX_LITE_CENTER_PRICE_SHIFT_SHIFTING_TIME)) & X24;
                // CRITICAL FIX: Extract timestamp from centerPriceShift, not from separate field
                let last_interaction_timestamp = center_price_shift_data & X33; // BITS_DEX_LITE_CENTER_PRICE_SHIFT_LAST_INTERACTION_TIMESTAMP = 0
                let time_elapsed = (simulation_timestamp - last_interaction_timestamp)?;

                if time_elapsed < shifting_time {
                    let price_diff = (center_price - lower_range_price)?;
                    let adjustment = (price_diff * time_elapsed)? / shifting_time;
                    center_price = (center_price - adjustment)?;
            } else {
                    // 100% price shifted
                    center_price = lower_range_price;
                }
            }

            // Apply min/max bounds if rebalancing happened
            if center_price_shift_data > SafeU256::zero() {
                // Check max center price
                let mut max_center_price = (center_price_shift_data >> SafeU256::from(BITS_DEX_LITE_CENTER_PRICE_SHIFT_MAX_CENTER_PRICE)) & X28;
                max_center_price = fluid_math::expand_center_price(max_center_price)?;

                if center_price > max_center_price {
                    center_price = max_center_price;
                } else {
                    // Check min center price
                    let mut min_center_price = (center_price_shift_data >> SafeU256::from(BITS_DEX_LITE_CENTER_PRICE_SHIFT_MIN_CENTER_PRICE)) & X28;
                    min_center_price = fluid_math::expand_center_price(min_center_price)?;

                    if center_price < min_center_price {
                        center_price = min_center_price;
                    }
                }

                // Update range prices as center price moved
                upper_range_price = ((center_price * FOUR_DECIMALS)? / (FOUR_DECIMALS - upper_range_percent)?)?;
                lower_range_price = ((center_price * (FOUR_DECIMALS - lower_range_percent)?)? / FOUR_DECIMALS)?;
            }
        }

        // Calculate geometric mean
        let geometric_mean: SafeU256;

        let very_large_threshold = SafeU256::exp10(SafeU256::from(38u64));
        if upper_range_price < very_large_threshold {
            // Normal case
            geometric_mean = fluid_math::sqrt((upper_range_price * lower_range_price)?)?;
        } else {
            // Handle very large prices
            let scale = SafeU256::exp10(SafeU256::from(18u64));
            let scaled_upper = (upper_range_price / scale)?;
            let scaled_lower = (lower_range_price / scale)?;
            geometric_mean = (fluid_math::sqrt((scaled_upper * scaled_lower)?)? * scale)?;
        }
        
        // Calculate imaginary reserves
        let mut token0_imaginary_reserves: SafeU256;
        let mut token1_imaginary_reserves: SafeU256;
        
        // Use the raw total supply adjusted values directly - they are already in 9-decimal precision
        let token0_supply = unpacked_vars.token0_total_supply_adjusted;
        let token1_supply = unpacked_vars.token1_total_supply_adjusted;

        if geometric_mean < PRICE_PRECISION {
            let (xa, yb) = fluid_math::calculate_reserves_outside_range(
                geometric_mean,
                upper_range_price,
                token0_supply,
                token1_supply,
            )?;
            token0_imaginary_reserves = xa;
            token1_imaginary_reserves = yb;
        } else {
            let inverse_geometric_mean = (SafeU256::exp10(SafeU256::from(54u64)) / geometric_mean)?;
            let inverse_lower_price = (SafeU256::exp10(SafeU256::from(54u64)) / lower_range_price)?;
            
            let (xa, yb) = fluid_math::calculate_reserves_outside_range(
                inverse_geometric_mean,
                inverse_lower_price,
                token1_supply,
                token0_supply,
            )?;
            // CRITICAL FIX: Swapped assignment to match Solidity line 493
            token1_imaginary_reserves = xa;  // First return value goes to token1
            token0_imaginary_reserves = yb;  // Second return value goes to token0
        }

        // Add actual supplies to imaginary reserves
        token0_imaginary_reserves = (token0_imaginary_reserves + token0_supply)?;
        token1_imaginary_reserves = (token1_imaginary_reserves + token1_supply)?;

        MathResult::ok(PricingResult {
            center_price,
            upper_range_price,
            lower_range_price,
            token0_imaginary_reserves,
            token1_imaginary_reserves,
        })
    }

    // Calculate swap for exact input (Token0 to Token1)
    fn calculate_swap_0_to_1(
        state: &FlowerData,
        amount_in: SafeU256,
    ) -> MathResult<SafeU256, FluidDexLiteError> {
        let unpacked_vars = unpack_dex_variables(state.dex_variables);

        // CRITICAL: Check if dex is initialized (contract line 15-17)
        if state.dex_variables == SafeU256::zero() {
            return MathResult::err(FluidDexLiteError::DexNotInitialized);
        }

        // Get current pricing with all shifting logic
        let pricing = get_prices_and_reserves(state)?;

        let mut adjusted_amount_in = amount_in;

        // Apply decimal adjustments for token0 (contract lines 26-31)
        let token0_decimals = unpacked_vars.token0_decimals;
        
        if token0_decimals > TOKENS_DECIMALS_PRECISION {
            let power = (token0_decimals - TOKENS_DECIMALS_PRECISION)?;
            let divisor = SafeU256::exp10(power);
            adjusted_amount_in = (adjusted_amount_in / divisor)?;
        } else {
            let power = (TOKENS_DECIMALS_PRECISION - token0_decimals)?;
            let multiplier = SafeU256::exp10(power);
            adjusted_amount_in = (adjusted_amount_in * multiplier)?;
        }

        // CRITICAL: Validate amount (contract lines 33-34)
        if adjusted_amount_in < FOUR_DECIMALS || adjusted_amount_in > X60 {
            return MathResult::err(FluidDexLiteError::InvalidSwapAmounts);
        }

        // CRITICAL: Check against half of reserves (contract lines 36-38)
        if adjusted_amount_in > (pricing.token0_imaginary_reserves / SafeU256::from(2u64))? {
            return MathResult::err(FluidDexLiteError::ExcessiveSwapAmount);
        }

        let fee = ((adjusted_amount_in * unpacked_vars.fee)? / SIX_DECIMALS)?;
        let amount_in_after_fee = (adjusted_amount_in - fee)?;

        // Constant product formula (contract line 42)
        let numerator = (amount_in_after_fee * pricing.token1_imaginary_reserves)?;
        let denominator = (pricing.token0_imaginary_reserves + amount_in_after_fee)?;
        let mut amount_out = (numerator / denominator)?;

        // CRITICAL: Check token reserves (contract lines 45-47)
        if unpacked_vars.token1_total_supply_adjusted < amount_out {
            return MathResult::err(FluidDexLiteError::TokenReservesTooLow);
        }

        // Calculate updated supplies for reserve ratio check
        let revenue_cut_fee = ((fee * unpacked_vars.revenue_cut)? / SafeU256::from(100u64))?;
        let new_token0_supply = (unpacked_vars.token0_total_supply_adjusted + adjusted_amount_in - revenue_cut_fee)?;
        let new_token1_supply = (unpacked_vars.token1_total_supply_adjusted - amount_out)?;

        // CRITICAL: Check reserve ratio (contract lines 50-52)
        let min_token1_supply = ((new_token0_supply * pricing.center_price)? / (PRICE_PRECISION * MINIMUM_LIQUIDITY_SWAP))?;
        if new_token1_supply < min_token1_supply {
            return MathResult::err(FluidDexLiteError::TokenReservesRatioTooHigh);
        }

        // Apply decimal adjustments to output for token1 (reverse of input adjustment)
        let token1_decimals = unpacked_vars.token1_decimals;
        if token1_decimals > TOKENS_DECIMALS_PRECISION {
            let power = (token1_decimals - TOKENS_DECIMALS_PRECISION)?;
            let multiplier = SafeU256::exp10(power);
            amount_out = (amount_out * multiplier)?;
        } else {
            let power = (TOKENS_DECIMALS_PRECISION - token1_decimals)?;
            let divisor = SafeU256::exp10(power);
            amount_out = (amount_out / divisor)?;
        }

        MathResult::ok(amount_out)
    }

    // Calculate swap for exact input (Token1 to Token0)
    fn calculate_swap_1_to_0(
        state: &FlowerData,
        amount_in: SafeU256,
    ) -> MathResult<SafeU256, FluidDexLiteError> {
        let unpacked_vars = unpack_dex_variables(state.dex_variables);

        // CRITICAL: Check if dex is initialized (contract line 15-17)
        if state.dex_variables == SafeU256::zero() {
            return MathResult::err(FluidDexLiteError::DexNotInitialized);
        }

        // Get current pricing with all shifting logic
        let pricing = get_prices_and_reserves(state)?;

        let mut adjusted_amount_in = amount_in;

        // Apply decimal adjustments for token1 (contract lines 54-59)
        let token1_decimals = unpacked_vars.token1_decimals;
        if token1_decimals > TOKENS_DECIMALS_PRECISION {
            let power = (token1_decimals - TOKENS_DECIMALS_PRECISION)?;
            let divisor = SafeU256::exp10(power);
            adjusted_amount_in = (adjusted_amount_in / divisor)?;
        } else {
            let power = (TOKENS_DECIMALS_PRECISION - token1_decimals)?;
            let multiplier = SafeU256::exp10(power);
            adjusted_amount_in = (adjusted_amount_in * multiplier)?;
        }

        // CRITICAL: Validate amount (contract lines 61-62)
        if adjusted_amount_in < FOUR_DECIMALS || adjusted_amount_in > X60 {
            return MathResult::err(FluidDexLiteError::InvalidSwapAmounts);
        }

        // CRITICAL: Check against half of reserves (contract lines 64-66)
        if adjusted_amount_in > (pricing.token1_imaginary_reserves / SafeU256::from(2u64))? {
            return MathResult::err(FluidDexLiteError::ExcessiveSwapAmount);
        }

        let fee = ((adjusted_amount_in * unpacked_vars.fee)? / SIX_DECIMALS)?;
        let amount_in_after_fee = (adjusted_amount_in - fee)?;

        // Constant product formula (contract line 70)
        let numerator = (amount_in_after_fee * pricing.token0_imaginary_reserves)?;
        let denominator = (pricing.token1_imaginary_reserves + amount_in_after_fee)?;
        let mut amount_out = (numerator / denominator)?;

        // CRITICAL: Check token reserves (contract lines 73-75)
        if unpacked_vars.token0_total_supply_adjusted < amount_out {
            return MathResult::err(FluidDexLiteError::TokenReservesTooLow);
        }

        // Calculate updated supplies for reserve ratio check
        let revenue_cut_fee = ((fee * unpacked_vars.revenue_cut)? / SafeU256::from(100u64))?;
        let new_token1_supply = (unpacked_vars.token1_total_supply_adjusted + adjusted_amount_in - revenue_cut_fee)?;
        let new_token0_supply = (unpacked_vars.token0_total_supply_adjusted - amount_out)?;

        // CRITICAL: Check reserve ratio (contract lines 78-80)
        let min_token0_supply = ((new_token1_supply * PRICE_PRECISION)? / (pricing.center_price * MINIMUM_LIQUIDITY_SWAP))?;
        if new_token0_supply < min_token0_supply {
            return MathResult::err(FluidDexLiteError::TokenReservesRatioTooHigh);
        }

        // Apply decimal adjustments to output for token0
        let token0_decimals = unpacked_vars.token0_decimals;
        if token0_decimals > TOKENS_DECIMALS_PRECISION {
            let power = (token0_decimals - TOKENS_DECIMALS_PRECISION)?;
            let multiplier = SafeU256::exp10(power);
            amount_out = (amount_out * multiplier)?;
                } else {
            let power = (TOKENS_DECIMALS_PRECISION - token0_decimals)?;
            let divisor = SafeU256::exp10(power);
            amount_out = (amount_out / divisor)?;
        }

        MathResult::ok(amount_out)
    }
}

pub mod balancer_v3_stable_surge {
    use std::sync::Arc;
    use crate::barter_lib::amm_lib::*;

    use crate::barter_lib::common::Swap;
    use crate::{
        barter_lib::{amm_lib::ExchangeInfo, safe_math::{MathResult, SafeMathError}, SafeU256}, types::balancer_v3_stable_surge::FlowerData
    };
    use balancer_maths_rust::vault::Vault; 
    use balancer_maths_rust::common::types::{SwapInput, SwapKind, PoolStateOrBuffer};
    use balancer_maths_rust::pools::stable::{StableState, StableMutable};
    use balancer_maths_rust::common::types::BasePoolState;
    use balancer_maths_rust::hooks::stable_surge::StableSurgeHookState;
    use balancer_maths_rust::hooks::types::HookState;

    pub type BalancerV3StableSurgeError = SafeMathError;
    #[derive(Debug, Clone)]
    pub struct BalancerV3ExchangeRequest {
        pub source_token: Address,
        pub target_token: Address,
        pub exchange_info: ExchangeInfo,
    }

    #[derive(Debug, serde::Serialize, serde::Deserialize, Hash, Eq, PartialEq, Clone)]
    #[serde(rename_all = "camelCase")]
    #[serde(deny_unknown_fields)]
    pub struct BalancerV3Meta {
        pub pool_address: Address,
        pub source_token: Address,
        pub target_token: Address,
    }

    #[allow(unused)]
    impl GetAddress for BalancerV3Meta {
        fn get_address(&self) -> Address {
            self.pool_address
        }
    }
    #[allow(unused)]
    impl ToExchanges for FlowerData {
        type Ex = BalancerV3StableSurgeExchange;
        type ExIter<'a, T: ExchangeContext + 'a> =
            impl Iterator<Item = Self::Ex> + 'a;

        fn to_exchanges<
            'a,
            T: ExchangeContext + 'a,
        >(
            self,
            context: &'a mut T,
        ) -> Self::ExIter<'a, T> {
            let pool_address = self.pool_info.address;
            let tokens = self.pool_info.tokens.clone();
            let p = Arc::new(self);
            
            // Generate exchanges for all token pairs
            let mut exchanges = Vec::new();
            for (i, &token_a) in tokens.iter().enumerate() {
                for (j, &token_b) in tokens.iter().enumerate() {
                    // Skip same token pairs
                    if i == j {
                        continue;
                    }
                    
                    // Get token IDs, skip if any token is not found
                    if let (Some(source_id), Some(target_id)) = (
                        context.get_token_id(&token_a),
                        context.get_token_id(&token_b)
                    ) {
                        exchanges.push(BalancerV3StableSurgeExchange {
                            pool_info: Arc::clone(&p),
                            request: BalancerV3ExchangeRequest {
                                source_token: token_a,
                                target_token: token_b,
                                exchange_info: ExchangeInfo {
                                    exchange_id: context.get_exchange_id(&p.pool_info.address),
                                    source: source_id,
                                    target: target_id,
                                },
                            },
                            meta: Arc::new(BalancerV3Meta {
                                pool_address,
                                source_token: token_a,
                                target_token: token_b,
                            }),
                        });
                    }
                }
            }

            exchanges.into_iter()
        }
    }
    
    #[allow(unused)]
    impl Swap for BalancerV3StableSurgeExchange {
        type Error = BalancerV3StableSurgeError;

        #[inline(never)]
        fn swap(&self, amount: SafeU256) -> MathResult<SafeU256, Self::Error> {
            let vault = Vault::new();

            let swap_input = SwapInput {
                swap_kind: SwapKind::GivenIn,
                amount_raw: amount.to_big_int(),
                token_in: self.request.source_token.to_string(),
                token_out: self.request.target_token.to_string(),
            };

            let pool_state = create_stable_state_from_pool_info(&self.pool_info);
            let hook_state = create_hook_state(&self.pool_info);

            let output_amount = vault.swap(
                &swap_input,
                &PoolStateOrBuffer::Pool(Box::new(pool_state.into())),
                Some(&HookState::StableSurge(hook_state)),
            );

            match output_amount {
                Ok(big_int) => {
                    let result = SafeU256::from_dec_str(&big_int.to_string()).unwrap_or(SafeU256::zero());
                    MathResult::ok(result)
                },
                Err(_) => MathResult::err(SafeMathError::Div),
            }
        }
    }

    #[allow(unused)]
    impl SwapGas for BalancerV3StableSurgeExchange {
        type Methods = ();
        fn swap_gas(&self, gas_storage: &impl GasStorage<Self::Methods>) -> Gas {
            // https://github.com/balancer/balancer-v3-monorepo/blob/main/pkg/pool-hooks/test/gas/.hardhat-snapshots/%5BStableSurgePool%20-%20WithRate%5D%20swap%20single%20token%20exact%20in%20with%20fees%20-%20cold%20slots
            return 239900;
        }
    }

    /// =========== IMPLEMENTATION DETAILS BELOW ==============

    pub type BalancerV3StableSurgeExchange = PoolRequestMeta<Arc<FlowerData>, BalancerV3ExchangeRequest, Arc<BalancerV3Meta>>;

    /// Creates a StableState for use in balancer-maths-rust from pool_info (FlowerData)
    fn create_stable_state_from_pool_info(pool_info: &FlowerData) -> StableState {
        let base_pool_state = BasePoolState {
            pool_address: pool_info.pool_info.address.to_string(),
            pool_type: "STABLE".to_string(),
            tokens: pool_info.pool_info.tokens.iter().map(|addr| addr.to_string()).collect(),
            scaling_factors: pool_info.pool_info.decimal_scaling_factors.iter().map(|sf| sf.to_big_int()).collect(),
            token_rates: pool_info.token_rates.iter().map(|rate| rate.to_big_int()).collect(),
            balances_live_scaled_18: pool_info.balances_live_scaled_18.iter().map(|balance| balance.to_big_int()).collect(),
            swap_fee: pool_info.swap_fee.to_big_int(),
            aggregate_swap_fee: pool_info.aggregate_swap_fee.to_big_int(),
            total_supply: pool_info.total_supply.to_big_int(),
            supports_unbalanced_liquidity: pool_info.pool_info.supports_unbalanced_liquidity,
            hook_type: Some(pool_info.pool_info.hook_type.clone()),
        };

        let stable_mutable = StableMutable {
            amp: pool_info.amp.to_big_int(),
        };

        StableState {
            base: base_pool_state,
            mutable: stable_mutable,
        }
    }

    /// Creates a StableSurgeHookState for use in balancer-maths-rust from pool_info (FlowerData)
    fn create_hook_state(pool_info: &FlowerData) -> StableSurgeHookState {
        StableSurgeHookState {
            hook_type: "StableSurge".to_string(),
            amp: pool_info.amp.to_big_int(),
            surge_threshold_percentage: pool_info.surge_threshold_percentage.to_big_int(),
            max_surge_fee_percentage: pool_info.max_surge_fee_percentage.to_big_int(),
        }
    }

    #[cfg(test)]
    mod tests {
        use alloy_primitives::address;

        use crate::{su256const, types::balancer_v3_stable_surge::{PoolInfo}};

        use super::*;

        fn create_test_pool() -> FlowerData {
            FlowerData {
                pool_info: PoolInfo {
                    address: address!("0x75c23271661d9d143dcb617222bc4bec783eff34"),
                    tokens: vec![
                        address!("0x7b79995e5f793a07bc00c21412e50ecae098e7f9"),
                        address!("0xb19382073c7a0addbb56ac6af1808fa49e377b75"),
                    ],
                    decimal_scaling_factors: vec![su256const!(1), su256const!(1)],
                    supports_unbalanced_liquidity: false,
                    hook_type: "StableSurge".to_string(),
                },
                token_rates: vec![
                    su256const!(1000000000000000000),
                    su256const!(1000000000000000000),
                ],
                balances_live_scaled_18: vec![
                    su256const!(10000000000000000),
                    su256const!(10000000000000000000),
                ],
                swap_fee: su256const!(10000000000000000),
                aggregate_swap_fee: su256const!(10000000000000000),
                total_supply: su256const!(9079062661965173292),
                amp: su256const!(1000000),
                max_surge_fee_percentage: su256const!(950000000000000000),
                surge_threshold_percentage: su256const!(300000000000000000),
            }
        }

        #[test]
        fn test_complete_stable_surge_below_threshold_1() {
            // Replicating: < surgeThresholdPercentage, should use staticSwapFee
            // https://www.tdly.co/shared/simulation/e50584b3-d8ed-4633-b261-47401482c7b7
            let pool = create_test_pool();

            let pool_request_meta: Vec<_> = pool.to_exchanges(&mut EmptyExchangeContext {}).collect();
            let pool_request_meta = pool_request_meta.into_iter().find(|x| x.request.source_token == address!("0x7b79995e5f793a07bc00c21412e50ecae098e7f9") &&
                x.request.target_token == address!("0xb19382073c7a0addbb56ac6af1808fa49e377b75")).unwrap();
            let result_ok = pool_request_meta.swap(su256const!(1000000000000000));
            assert_eq!(result_ok.unwrap(), su256const!(78522716365403684));
        }
        
        #[test]
        fn test_complete_stable_surge_below_threshold_2() {
            // Replicating: < surgeThresholdPercentage, should use staticSwapFee
            // https://www.tdly.co/shared/simulation/1220e0ec-1d3d-4f2a-8eb0-850fed8d15ed
            let pool = create_test_pool();

            let pool_request_meta: Vec<_> = pool.to_exchanges(&mut EmptyExchangeContext {}).collect();
            let pool_request_meta = pool_request_meta.into_iter().find(|x| x.request.source_token == address!("0x7b79995e5f793a07bc00c21412e50ecae098e7f9") &&
                x.request.target_token == address!("0xb19382073c7a0addbb56ac6af1808fa49e377b75")).unwrap();
            let result_ok = pool_request_meta.swap(su256const!(10000000000000000));
            assert_eq!(result_ok.unwrap(), su256const!(452983383563178802));
        }

        #[test]
        fn test_complete_stable_surge_above_threshold() {
            // Replicating: > surgeThresholdPercentage, should use surge fee
            // https://www.tdly.co/shared/simulation/ce2a1146-68d4-49fc-b9d2-1fbc22086ea5
            let pool = create_test_pool();

            let pool_request_meta: Vec<_> = pool.to_exchanges(&mut EmptyExchangeContext {}).collect();
            let pool_request_meta = pool_request_meta.into_iter().find(|x| x.request.source_token == address!("0xb19382073c7a0addbb56ac6af1808fa49e377b75") &&
                x.request.target_token == address!("0x7b79995e5f793a07bc00c21412e50ecae098e7f9")).unwrap();
            let result_ok = pool_request_meta.swap(su256const!(8000000000000000000));
            assert_eq!(result_ok.unwrap(), su256const!(3252130027531260));
        }
    }

}


pub mod balancer_v3_reclamm {
    use std::sync::Arc;
    use crate::barter_lib::amm_lib::*;

    use crate::barter_lib::common::Swap;
    use crate::{
        barter_lib::{amm_lib::ExchangeInfo, safe_math::{MathResult, SafeMathError}, SafeU256}, types::balancer_v3_reclamm::FlowerData
    };
    use balancer_maths_rust::vault::Vault; 
    use balancer_maths_rust::common::types::{SwapInput, SwapKind, PoolStateOrBuffer};
    use balancer_maths_rust::pools::reclammv2::{ReClammV2State, ReClammV2Mutable, ReClammV2Immutable};
    use balancer_maths_rust::common::types::BasePoolState;

    pub type BalancerV3ReclammError = SafeMathError;
    #[derive(Debug, Clone)]
    pub struct BalancerV3ExchangeRequest {
        pub source_token: Address,
        pub target_token: Address,
        pub exchange_info: ExchangeInfo,
    }

    #[derive(Debug, serde::Serialize, serde::Deserialize, Hash, Eq, PartialEq, Clone)]
    #[serde(rename_all = "camelCase")]
    #[serde(deny_unknown_fields)]
    pub struct BalancerV3Meta {
        pub pool_address: Address,
        pub source_token: Address,
        pub target_token: Address,
    }

    #[allow(unused)]
    impl GetAddress for BalancerV3Meta {
        fn get_address(&self) -> Address {
            self.pool_address
        }
    }
    #[allow(unused)]
    impl ToExchanges for FlowerData {
        type Ex = BalancerV3ReclammExchange;
        type ExIter<'a, T: ExchangeContext + 'a> =
            impl Iterator<Item = Self::Ex> + 'a;

        fn to_exchanges<
            'a,
            T: ExchangeContext + 'a,
        >(
            self,
            context: &'a mut T,
        ) -> Self::ExIter<'a, T> {
            let pool_address = self.pool_info.address;
            let tokens = self.pool_info.tokens.clone();
            let p = Arc::new(self);
            
            // Generate exchanges for all token pairs
            let mut exchanges = Vec::new();
            for (i, &token_a) in tokens.iter().enumerate() {
                for (j, &token_b) in tokens.iter().enumerate() {
                    // Skip same token pairs
                    if i == j {
                        continue;
                    }
                    
                    // Get token IDs, skip if any token is not found
                    if let (Some(source_id), Some(target_id)) = (
                        context.get_token_id(&token_a),
                        context.get_token_id(&token_b)
                    ) {
                        exchanges.push(BalancerV3ReclammExchange {
                            pool_info: Arc::clone(&p),
                            request: BalancerV3ExchangeRequest {
                                source_token: token_a,
                                target_token: token_b,
                                exchange_info: ExchangeInfo {
                                    exchange_id: context.get_exchange_id(&p.pool_info.address),
                                    source: source_id,
                                    target: target_id,
                                },
                            },
                            meta: Arc::new(BalancerV3Meta {
                                pool_address,
                                source_token: token_a,
                                target_token: token_b,
                            }),
                        });
                    }
                }
            }

            exchanges.into_iter()
        }
    }
    
    #[allow(unused)]
    impl Swap for BalancerV3ReclammExchange {
        type Error = BalancerV3ReclammError;

        #[inline(never)]
        fn swap(&self, amount: SafeU256) -> MathResult<SafeU256, Self::Error> {
            let vault = Vault::new();

            let swap_input = SwapInput {
                swap_kind: SwapKind::GivenIn,
                amount_raw: amount.to_big_int(),
                token_in: self.request.source_token.to_string(),
                token_out: self.request.target_token.to_string(),
            };

            let pool_state = create_reclamm_state_from_pool_info(&self.pool_info);

            let output_amount = vault.swap(
                &swap_input,
                &PoolStateOrBuffer::Pool(Box::new(pool_state.into())),
                None,
            );

            match output_amount {
                Ok(big_int) => {
                    let result = SafeU256::from_dec_str(&big_int.to_string()).unwrap_or(SafeU256::zero());
                    MathResult::ok(result)
                },
                Err(_) => MathResult::err(SafeMathError::Div),
            }
        }
    }

    #[allow(unused)]
    impl SwapGas for BalancerV3ReclammExchange {
        type Methods = ();
        fn swap_gas(&self, gas_storage: &impl GasStorage<Self::Methods>) -> Gas {
            // https://github.com/balancer/reclamm/tree/main/test/gas/.hardhat-snapshots
            return 250800;
        }
    }

    /// =========== IMPLEMENTATION DETAILS BELOW ==============

    pub type BalancerV3ReclammExchange = PoolRequestMeta<Arc<FlowerData>, BalancerV3ExchangeRequest, Arc<BalancerV3Meta>>;

    /// Creates a ReclammState for use in balancer-maths-rust from pool_info (FlowerData)
    fn create_reclamm_state_from_pool_info(pool_info: &FlowerData) -> ReClammV2State {
        let base_pool_state = BasePoolState {
            pool_address: pool_info.pool_info.address.to_string(),
            pool_type: "RECLAMM".to_string(),
            tokens: pool_info.pool_info.tokens.iter().map(|addr| addr.to_string()).collect(),
            scaling_factors: pool_info.pool_info.decimal_scaling_factors.iter().map(|sf| sf.to_big_int()).collect(),
            token_rates: pool_info.token_rates.iter().map(|rate| rate.to_big_int()).collect(),
            balances_live_scaled_18: pool_info.balances_live_scaled_18.iter().map(|balance| balance.to_big_int()).collect(),
            swap_fee: pool_info.swap_fee.to_big_int(),
            aggregate_swap_fee: pool_info.aggregate_swap_fee.to_big_int(),
            total_supply: pool_info.total_supply.to_big_int(),
            supports_unbalanced_liquidity: pool_info.pool_info.supports_unbalanced_liquidity,
            hook_type: None,
        };

        let reclamm_mutable = ReClammV2Mutable { 
            last_virtual_balances: pool_info.last_virtual_balances.iter().map(|balance| balance.to_big_int()).collect(), 
            daily_price_shift_base: pool_info.daily_price_shift_base.to_big_int(), 
            last_timestamp: pool_info.last_timestamp.to_big_int(), 
            centeredness_margin: pool_info.centeredness_margin.to_big_int(), 
            start_fourth_root_price_ratio: pool_info.start_fourth_root_price_ratio.to_big_int(), 
            end_fourth_root_price_ratio: pool_info.end_fourth_root_price_ratio.to_big_int(), 
            price_ratio_update_start_time: pool_info.price_ratio_update_start_time.to_big_int(), 
            price_ratio_update_end_time: pool_info.price_ratio_update_end_time.to_big_int(),
            current_timestamp: pool_info.current_timestamp.to_big_int(),
        };

        ReClammV2State {
            base: base_pool_state,
            mutable: reclamm_mutable,
            immutable: ReClammV2Immutable {
                pool_address: pool_info.pool_info.address.to_string(),
                tokens: pool_info.pool_info.tokens.iter().map(|addr| addr.to_string()).collect(),
            },
        }
    }

    #[cfg(test)]
    mod tests {
        use alloy_primitives::address;

        use crate::{su256const, types::balancer_v3_reclamm::{PoolInfo}};

        use super::*;

        fn create_test_pool() -> FlowerData {
            FlowerData {
                pool_info: PoolInfo {
                    address: address!("0x12c2de9522f377b86828f6af01f58c046f814d3c"),
                    tokens: vec![
                        address!("0x60a3E35Cc302bFA44Cb288Bc5a4F316Fdb1adb42"),
                        address!("0x833589fCD6eDb6E08f4c7C32D4f71b54bdA02913"),
                    ],
                    decimal_scaling_factors: vec![su256const!(1000000000000), su256const!(1000000000000)],
                    supports_unbalanced_liquidity: false,
                },
                token_rates: vec![
                    su256const!(1000000000000000000),
                    su256const!(1000000000000000000),
                ],
                balances_live_scaled_18: vec![
                    su256const!(3231573612000000000000),
                    su256const!(6289473995000000000000),
                ],
                swap_fee: su256const!(250000000000000),
                aggregate_swap_fee: su256const!(500000000000000000),
                total_supply: su256const!(37431808905174667155226173),
                last_virtual_balances: vec![
                    su256const!(362594117476852465718411),
                    su256const!(422163369011063269890448),
                ],
                daily_price_shift_base: su256const!(999999197747274347),
                last_timestamp: su256const!(1752054083),
                centeredness_margin: su256const!(500000000000000000),
                start_fourth_root_price_ratio: su256const!(1011900417200324692),
                end_fourth_root_price_ratio: su256const!(1011900417200324692),
                price_ratio_update_start_time: su256const!(1751988959),
                price_ratio_update_end_time: su256const!(1751988959),
                current_timestamp: su256const!(1752054103),
            }
        }

        #[test]
        fn test_complete_reclamm_1() {
            let pool = create_test_pool();

            let pool_request_meta: Vec<_> = pool.to_exchanges(&mut EmptyExchangeContext {}).collect();
            let pool_request_meta = pool_request_meta.into_iter().find(|x| x.request.source_token == address!("0x833589fCD6eDb6E08f4c7C32D4f71b54bdA02913") &&
                x.request.target_token == address!("0x60a3e35cc302bfa44cb288bc5a4f316fdb1adb42")).unwrap();
            let result_ok = pool_request_meta.swap(su256const!(100000));
            assert_eq!(result_ok.unwrap(), su256const!(85361));
        }

        #[test]
        fn test_complete_reclamm_2() {
            let pool = create_test_pool();

            let pool_request_meta: Vec<_> = pool.to_exchanges(&mut EmptyExchangeContext {}).collect();
            let pool_request_meta = pool_request_meta.into_iter().find(|x| x.request.source_token == address!("0x60a3e35cc302bfa44cb288bc5a4f316fdb1adb42") &&
                x.request.target_token == address!("0x833589fCD6eDb6E08f4c7C32D4f71b54bdA02913")).unwrap();
            let result_ok = pool_request_meta.swap(su256const!(20000000));
            assert_eq!(result_ok.unwrap(), su256const!(23416743));
        }
    }

}

pub mod balancer_v3_quantamm {
    use std::sync::Arc;
    use crate::barter_lib::amm_lib::*;

    use crate::barter_lib::common::Swap;
    use crate::{
        barter_lib::{amm_lib::ExchangeInfo, safe_math::{MathResult, SafeMathError}, SafeU256}, types::balancer_v3_quantamm::FlowerData
    };
    use balancer_maths_rust::pools::QuantAmmMutable;
    use balancer_maths_rust::vault::Vault; 
    use balancer_maths_rust::common::types::{SwapInput, SwapKind, PoolStateOrBuffer};
    use balancer_maths_rust::pools::quantamm::{QuantAmmState, QuantAmmImmutable};
    use balancer_maths_rust::common::types::BasePoolState;

    pub type BalancerV3QuantammError = SafeMathError;
    #[derive(Debug, Clone)]
    pub struct BalancerV3ExchangeRequest {
        pub source_token: Address,
        pub target_token: Address,
        pub exchange_info: ExchangeInfo,
    }

    #[derive(Debug, serde::Serialize, serde::Deserialize, Hash, Eq, PartialEq, Clone)]
    #[serde(rename_all = "camelCase")]
    #[serde(deny_unknown_fields)]
    pub struct BalancerV3Meta {
        pub pool_address: Address,
        pub source_token: Address,
        pub target_token: Address,
    }

    #[allow(unused)]
    impl GetAddress for BalancerV3Meta {
        fn get_address(&self) -> Address {
            self.pool_address
        }
    }
    #[allow(unused)]
    impl ToExchanges for FlowerData {
        type Ex = BalancerV3QuantammExchange;
        type ExIter<'a, T: ExchangeContext + 'a> =
            impl Iterator<Item = Self::Ex> + 'a;

        fn to_exchanges<
            'a,
            T: ExchangeContext + 'a,
        >(
            self,
            context: &'a mut T,
        ) -> Self::ExIter<'a, T> {
            let pool_address = self.pool_info.address;
            let tokens = self.pool_info.tokens.clone();
            let p = Arc::new(self);
            
            // Generate exchanges for all token pairs
            let mut exchanges = Vec::new();
            for (i, &token_a) in tokens.iter().enumerate() {
                for (j, &token_b) in tokens.iter().enumerate() {
                    // Skip same token pairs
                    if i == j {
                        continue;
                    }
                    
                    // Get token IDs, skip if any token is not found
                    if let (Some(source_id), Some(target_id)) = (
                        context.get_token_id(&token_a),
                        context.get_token_id(&token_b)
                    ) {
                        exchanges.push(BalancerV3QuantammExchange {
                            pool_info: Arc::clone(&p),
                            request: BalancerV3ExchangeRequest {
                                source_token: token_a,
                                target_token: token_b,
                                exchange_info: ExchangeInfo {
                                    exchange_id: context.get_exchange_id(&p.pool_info.address),
                                    source: source_id,
                                    target: target_id,
                                },
                            },
                            meta: Arc::new(BalancerV3Meta {
                                pool_address,
                                source_token: token_a,
                                target_token: token_b,
                            }),
                        });
                    }
                }
            }

            exchanges.into_iter()
        }
    }
    
    #[allow(unused)]
    impl Swap for BalancerV3QuantammExchange {
        type Error = BalancerV3QuantammError;

        #[inline(never)]
        fn swap(&self, amount: SafeU256) -> MathResult<SafeU256, Self::Error> {
            let vault = Vault::new();

            let swap_input = SwapInput {
                swap_kind: SwapKind::GivenIn,
                amount_raw: amount.to_big_int(),
                token_in: self.request.source_token.to_string(),
                token_out: self.request.target_token.to_string(),
            };

            let pool_state = create_quantamm_state_from_pool_info(&self.pool_info);

            let output_amount = vault.swap(
                &swap_input,
                &PoolStateOrBuffer::Pool(Box::new(pool_state.into())),
                None,
            );

            match output_amount {
                Ok(big_int) => {
                    let result = SafeU256::from_dec_str(&big_int.to_string()).unwrap_or(SafeU256::zero());
                    MathResult::ok(result)
                },
                Err(_) => MathResult::err(SafeMathError::Div),
            }
        }
    }

    #[allow(unused)]
    impl SwapGas for BalancerV3QuantammExchange {
        type Methods = ();
        fn swap_gas(&self, gas_storage: &impl GasStorage<Self::Methods>) -> Gas {
            // https://etherscan.io/tx/0x7ea370c34fc1338c4839eab5592c77d824da086dd66827664fc8f0da55000977
            return 196000;
        }
    }

    /// =========== IMPLEMENTATION DETAILS BELOW ==============

    pub type BalancerV3QuantammExchange = PoolRequestMeta<Arc<FlowerData>, BalancerV3ExchangeRequest, Arc<BalancerV3Meta>>;

    /// Converts I256 to BigInt preserving sign
    fn convert_i256_to_bigint(value: &alloy_primitives::Signed<256, 4>) -> num_bigint::BigInt {
        let raw = value.into_raw();
        let bytes = raw.to_be_bytes::<32>();
        num_bigint::BigInt::from_signed_bytes_be(&bytes)
    }

    /// Creates a QuantAmmState for use in balancer-maths-rust from pool_info (FlowerData)
    fn create_quantamm_state_from_pool_info(pool_info: &FlowerData) -> QuantAmmState {
        let base_pool_state = BasePoolState {
            pool_address: pool_info.pool_info.address.to_string(),
            pool_type: "QUANT_AMM_WEIGHTED".to_string(),
            tokens: pool_info.pool_info.tokens.iter().map(|addr| addr.to_string()).collect(),
            scaling_factors: pool_info.pool_info.decimal_scaling_factors.iter().map(|sf| sf.to_big_int()).collect(),
            token_rates: pool_info.token_rates.iter().map(|rate| rate.to_big_int()).collect(),
            balances_live_scaled_18: pool_info.balances_live_scaled_18.iter().map(|balance| balance.to_big_int()).collect(),
            swap_fee: pool_info.swap_fee.to_big_int(),
            aggregate_swap_fee: pool_info.aggregate_swap_fee.to_big_int(),
            total_supply: pool_info.total_supply.to_big_int(),
            supports_unbalanced_liquidity: pool_info.pool_info.supports_unbalanced_liquidity,
            hook_type: None,
        };

        let quantamm_mutable = QuantAmmMutable { 
            first_four_weights_and_multipliers: pool_info.first_four_weights_and_multipliers.iter().map(convert_i256_to_bigint).collect(),
            second_four_weights_and_multipliers: pool_info.second_four_weights_and_multipliers.iter().map(convert_i256_to_bigint).collect(),
            last_update_time: pool_info.last_update_time.to_big_int(),
            last_interop_time: pool_info.last_interop_time.to_big_int(),
            current_timestamp: pool_info.current_timestamp.to_big_int(),
        };

        QuantAmmState {
            base: base_pool_state,
            mutable: quantamm_mutable,
            immutable: QuantAmmImmutable {
                max_trade_size_ratio: pool_info.pool_info.max_trade_size_ratio.to_big_int()
            },
        }
    }

    #[cfg(test)]
    mod tests {
        use alloy_primitives::{address, I256};

        use crate::{su256const, types::balancer_v3_quantamm::{PoolInfo}};

        use super::*;

        fn create_test_pool() -> FlowerData {
            FlowerData {
                pool_info: PoolInfo {
                    address: address!("0x6b61d8680c4f9e560c8306807908553f95c749c5"),
                    tokens: vec![
                        address!("0x2260fac5e5542a773aa44fbcfedf7c193bc2c599"),
                        address!("0x45804880de22913dafe09f4980848ece6ecbaf78"),
                        address!("0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48"),
                    ],
                    decimal_scaling_factors: vec![su256const!(10000000000), su256const!(1), su256const!(1000000000000)],
                    supports_unbalanced_liquidity: false,
                    max_trade_size_ratio: su256const!(100000000000000000),
                },
                token_rates: vec![
                    su256const!(1000000000000000000),
                    su256const!(1000000000000000000),
                    su256const!(1000000000000000000),
                ],
                balances_live_scaled_18: vec![
                    su256const!(900794470000000000),
                    su256const!(1304051331499334098),
                    su256const!(41955655751000000000000),
                ],
                swap_fee: su256const!(20000000000000000),
                aggregate_swap_fee: su256const!(0),
                total_supply: su256const!(8935547542387177179),
                first_four_weights_and_multipliers: vec![
                    I256::try_from(670600731000000000i64).unwrap(), 
                    I256::try_from(30079278000000000i64).unwrap(), 
                    I256::try_from(299405491000000000i64).unwrap(), 
                    I256::try_from(129000000000i64).unwrap(), 
                    I256::try_from(0).unwrap(), 
                    I256::try_from(-129000000000i64).unwrap(), 
                    I256::try_from(0).unwrap(), 
                    I256::try_from(0).unwrap()
                    ],
                second_four_weights_and_multipliers: vec![
                    I256::try_from(0).unwrap(), 
                    I256::try_from(0).unwrap(), 
                    I256::try_from(0).unwrap(), 
                    I256::try_from(0).unwrap(), 
                    I256::try_from(0).unwrap(), 
                    I256::try_from(0).unwrap(), 
                    I256::try_from(0).unwrap()
                ],
                last_update_time: su256const!(1747699223),
                last_interop_time: su256const!(1747785323),
                current_timestamp: su256const!(1747745435),
            }
        }

        #[test]
        fn test_complete_quantamm_1() {
            let pool = create_test_pool();

            let pool_request_meta: Vec<_> = pool.to_exchanges(&mut EmptyExchangeContext {}).collect();
            let pool_request_meta = pool_request_meta.into_iter().find(|x| x.request.source_token == address!("0x2260fac5e5542a773aa44fbcfedf7c193bc2c599") &&
                x.request.target_token == address!("0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48")).unwrap();
            let result_ok = pool_request_meta.swap(su256const!(1000000));
            assert_eq!(result_ok.unwrap(), su256const!(1033749354));
        }

        #[test]
        fn test_complete_quantamm_2() {
            let pool = create_test_pool();

            let pool_request_meta: Vec<_> = pool.to_exchanges(&mut EmptyExchangeContext {}).collect();
            let pool_request_meta = pool_request_meta.into_iter().find(|x| x.request.source_token == address!("0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48") &&
                x.request.target_token == address!("0x2260fac5e5542a773aa44fbcfedf7c193bc2c599")).unwrap();
            let result_ok = pool_request_meta.swap(su256const!(10000000));
            assert_eq!(result_ok.unwrap(), su256const!(9124));
        }
    }

}