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

            use crate::{
                barter_lib::{common::Swap, safe_math::SafeMathError, SafeU256}, model::dodo_v1::{
                        pricing::{
                            get_expected_target,
                            rbelow_back_to_one,
                            rbelow_sell_base_token,
                        }, DodoV1ExchangeRequest, DodoV1Meta, FlowerData, PoolRequestMeta, SwapDirection
                    }, su256const, types::dodo_v1::RStatus
            };

            use crate::barter_lib::amm_lib::{Address, ExchangeId, ExchangeInfo, TokenId, ZERO_ADDRESS};

            use crate::types::dodo_v1::PoolInfo as DodoV1PoolInfo;

            #[test]
            fn rbelow_sell_base_token_test() {
                let state = FlowerData {
                    pool_info: DodoV1PoolInfo {
                        base_token: Address::try_from(ZERO_ADDRESS).unwrap(),
                        quote_token: Address::try_from(ZERO_ADDRESS).unwrap(),
                        address: Address::try_from(ZERO_ADDRESS).unwrap(),
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
                        base_token: Address::try_from(ZERO_ADDRESS).unwrap(),
                        quote_token: Address::try_from(ZERO_ADDRESS).unwrap(),
                        address: Address::try_from(ZERO_ADDRESS).unwrap(),
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
                        base_token: Address::try_from(ZERO_ADDRESS).unwrap(),
                        quote_token: Address::try_from(ZERO_ADDRESS).unwrap(),
                        address: Address::try_from(ZERO_ADDRESS).unwrap(),
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
                        base_token: Address::try_from(ZERO_ADDRESS).unwrap(),
                        quote_token: Address::try_from(ZERO_ADDRESS).unwrap(),
                        address: Address::try_from(ZERO_ADDRESS).unwrap(),
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
                            base_token: Address::try_from("0x4691937a7508860F876c9c0a2a617E7d9E945D4B").unwrap(),
                            quote_token: Address::try_from("0xdAC17F958D2ee523a2206206994597C13D831ec7").unwrap(),
                            address: Address::try_from("0x181D93EA28023bf40C8bB94796c55138719803B4").unwrap(),
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
                        pool_address: Address::try_from("0x181D93EA28023bf40C8bB94796c55138719803B4").unwrap(),
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
                            base_token: Address::try_from("0x4691937a7508860F876c9c0a2a617E7d9E945D4B").unwrap(),
                            quote_token: Address::try_from("0xdAC17F958D2ee523a2206206994597C13D831ec7").unwrap(),
                            address: Address::try_from("0x181D93EA28023bf40C8bB94796c55138719803B4").unwrap(),
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
                        pool_address: Address::try_from("0x181D93EA28023bf40C8bB94796c55138719803B4").unwrap(),
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
        use crate::{su256const, types::dodo_v1::{PoolInfo, RStatus}};

        use super::*;

        #[test]
        fn test_complete() {
            let pool: FlowerData = FlowerData {
                pool_info: PoolInfo {
                    address: Address::from_const("0x75c23271661d9d143dcb617222bc4bec783eff34"),
                    base_token: Address::from_const("0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2"),
                    quote_token: Address::from_const("0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48"),
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