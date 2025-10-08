use alloy::network::Network;
use alloy::providers::Provider;
use alloy_primitives::{Address, address};
use serde::{Deserialize, Serialize};
use serde_with::serde_as;
use std::collections::HashMap;

use crate::barter_lib::SafeU256;
use crate::contracts::Erc4626Contract;

// Balancer V3 Vault address on mainnet
pub const VAULT: Address = address!("0xbA1333333333a1BA1108E8412f11850A5C319bA9");

#[derive(Clone, Debug)]
pub struct Erc4626 {
    pub address: Address,
    pub can_use_buffer_for_swaps: bool,
    pub asset: Address,
}

#[serde_as]
#[derive(Debug, Deserialize, Serialize, Clone, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct BufferState {
    pub pool_type: String,
    pub pool_address: Address,
    pub tokens: Vec<Address>,
    pub rate: SafeU256,
    pub max_deposit: SafeU256,
    pub max_withdraw: SafeU256,
}

#[serde_as]
#[derive(Debug, Deserialize, Serialize, Clone, Eq, PartialEq)]
pub enum TokenType {
    Regular(Address),
    Erc4626 { token: Address, asset: Address },
}

impl TokenType {
    pub fn address(&self) -> Address {
        match self {
            TokenType::Regular(addr) => *addr,
            TokenType::Erc4626 { token, .. } => *token,
        }
    }

    pub fn is_erc4626(&self) -> bool {
        matches!(self, TokenType::Erc4626 { .. })
    }

    pub fn asset(&self) -> Option<Address> {
        match self {
            TokenType::Regular(_) => None,
            TokenType::Erc4626 { asset, .. } => Some(*asset),
        }
    }
}

// GraphQL Response structures for the Balancer API
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct Erc4626ReviewData {
    can_use_buffer_for_swaps: bool,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct TokenData {
    address: String,
    underlying_token_address: String,
    erc4626_review_data: Option<Erc4626ReviewData>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct TokenGetTokensResponse {
    token_get_tokens: Vec<TokenData>,
}

#[derive(Debug, Deserialize)]
struct GraphQLResponse {
    data: TokenGetTokensResponse,
}

#[derive(Debug, Serialize)]
struct GraphQLRequest {
    query: String,
}

pub async fn fetch_erc4626_tokens() -> Result<HashMap<Address, Erc4626>, Box<dyn std::error::Error>>
{
    let client = reqwest::Client::new();

    let query = r#"
        query MyQuery {
          tokenGetTokens(chains: MAINNET, where: {typeIn: ERC4626}) {
            address
            underlyingTokenAddress
            erc4626ReviewData {
              canUseBufferForSwaps
            }
          }
        }
    "#;

    let request_body = GraphQLRequest {
        query: query.to_string(),
    };

    let response = client
        .post("https://api-v3.balancer.fi/")
        .json(&request_body)
        .send()
        .await?;

    let graphql_response: GraphQLResponse = response.json().await?;

    let mut tokens = HashMap::new();

    for token_data in graphql_response.data.token_get_tokens {
        // Skip tokens without review data (assume not valid ERC4626)
        let Some(review_data) = token_data.erc4626_review_data else {
            continue;
        };

        // Parse addresses from hex strings
        let address = token_data.address.parse::<Address>()?;
        let asset = token_data.underlying_token_address.parse::<Address>()?;

        let erc4626 = Erc4626 {
            address,
            can_use_buffer_for_swaps: review_data.can_use_buffer_for_swaps,
            asset,
        };

        tokens.insert(address, erc4626);
    }

    Ok(tokens)
}

pub fn classify_tokens(
    token_addresses: Vec<Address>,
    erc4626_tokens: &HashMap<Address, Erc4626>,
) -> Vec<TokenType> {
    let mut result = Vec::new();

    for token_address in token_addresses {
        if let Some(erc4626_info) = erc4626_tokens.get(&token_address) {
            if erc4626_info.can_use_buffer_for_swaps {
                result.push(TokenType::Erc4626 {
                    token: erc4626_info.address,
                    asset: erc4626_info.asset,
                });
            } else {
                result.push(TokenType::Regular(token_address));
            }
        } else {
            result.push(TokenType::Regular(token_address));
        }
    }
    result
}

/// Fetches ERC4626 buffer states for tokens in a pool
///
/// This function checks each token to see if it's an ERC4626 token, and if so,
/// fetches the necessary buffer state information including:
/// - Rate (convertToAssets for 1e18)
/// - Max withdraw from the vault
/// - Max deposit to the underlying asset
///
/// # Arguments
/// * `provider` - The provider to use for contract calls
/// * `tokens` - Vector of token types to check
/// * `vault_address` - The vault address to query for max withdraw
///
/// # Returns
/// A HashMap mapping ERC4626 token addresses to their BufferState
pub async fn fetch_erc4626_buffer_states<P, N>(
    provider: P,
    tokens: &[TokenType],
    vault_address: Address,
) -> HashMap<Address, BufferState>
where
    P: Provider<N> + Clone,
    N: Network,
{
    let mut buffer_states = HashMap::new();

    // Check each token for ERC4626 type
    for token_type in tokens {
        if token_type.is_erc4626() {
            let erc4626_contract =
                Erc4626Contract::new(token_type.address().into(), provider.clone());
            let rate_result = erc4626_contract
                .convertToAssets(alloy_primitives::U256::from(1_000_000_000_000_000_000u128))
                .call()
                .await
                .unwrap();
            let max_withdraw_result = erc4626_contract
                .maxWithdraw(vault_address.into())
                .call()
                .await
                .unwrap();
            let max_deposit_result = erc4626_contract
                .maxDeposit(token_type.asset().unwrap().into())
                .call()
                .await
                .unwrap();
            buffer_states.insert(
                token_type.address(),
                BufferState {
                    pool_type: "Buffer".to_string(),
                    pool_address: token_type.address(),
                    tokens: vec![token_type.address(), token_type.asset().unwrap()],
                    rate: SafeU256::from(rate_result),
                    max_deposit: max_deposit_result.into(),
                    max_withdraw: max_withdraw_result.into(),
                },
            );
        }
    }

    buffer_states
}

// ============================================================================
// Swap Path Logic for Balancer V3 Boosted Pools
// ============================================================================

/// Helper enum to classify token types in the context of swaps
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SwapTokenType {
    /// Regular token address
    Regular,
    /// ERC4626 token address (contains the asset address)
    Erc4626Token(Address),
    /// Asset address of an ERC4626 token (contains the ERC4626 token address)
    Asset(Address),
}

/// Represents a single step in a swap path
#[serde_as]
#[derive(Debug, Deserialize, Serialize, Hash, Eq, PartialEq, Clone)]
#[serde(rename_all = "camelCase")]
pub struct SwapPathStep {
    pub pool: Address,
    pub token_out: Address,
    /// If true, the "pool" is an ERC4626 Buffer. Used to wrap/unwrap tokens
    pub is_buffer: bool,
}

/// Represents a complete swap path with multiple steps
#[serde_as]
#[derive(Debug, Deserialize, Serialize, Hash, Eq, PartialEq, Clone)]
#[serde(rename_all = "camelCase")]
pub struct SwapPath {
    pub token_in: Address,
    pub steps: Vec<SwapPathStep>,
}

/// Creates a mapping from token addresses to their swap types
///
/// This allows you to quickly determine if a token address is:
/// - A regular token
/// - An ERC4626 token (and get its asset)
/// - An asset (and get its ERC4626 wrapper)
pub fn create_token_type_mapping(tokens: &[TokenType]) -> HashMap<Address, SwapTokenType> {
    let mut address_to_token_type = HashMap::new();

    for token in tokens {
        match token {
            TokenType::Regular(addr) => {
                address_to_token_type.insert(*addr, SwapTokenType::Regular);
            }
            TokenType::Erc4626 {
                token: erc4626_addr,
                asset: asset_addr,
            } => {
                address_to_token_type
                    .insert(*erc4626_addr, SwapTokenType::Erc4626Token(*asset_addr));
                address_to_token_type.insert(*asset_addr, SwapTokenType::Asset(*erc4626_addr));
            }
        }
    }

    address_to_token_type
}

/// Creates a swap path based on token types following the Balancer V3 logic
///
/// Logic:
/// 1. If neither token is an asset: Normal single swap (no path needed)
/// 2. If tokenIn is asset AND tokenOut is asset: Full boosted swap
///    - wrap > swap > unwrap
/// 3. Mixed scenarios:
///    - If tokenIn is asset: add wrap step
///    - Add swap step
///    - If tokenOut is asset: add unwrap step
pub fn create_swap_path(
    pool_address: Address,
    token_in: Address,
    token_out: Address,
    source_type: &SwapTokenType,
    target_type: &SwapTokenType,
) -> Option<SwapPath> {
    let token_in_is_asset = matches!(source_type, SwapTokenType::Asset(_));
    let token_out_is_asset = matches!(target_type, SwapTokenType::Asset(_));

    // Case 1: Neither token is an asset - normal single swap (no path needed)
    if !token_in_is_asset && !token_out_is_asset {
        return None;
    }

    let mut steps = Vec::new();

    // Case 2: Both tokens are assets - full boosted swap
    if token_in_is_asset && token_out_is_asset {
        // Get the ERC4626 addresses for both assets
        if let SwapTokenType::Asset(erc4626_in) = source_type {
            if let SwapTokenType::Asset(erc4626_out) = target_type {
                // Step 1: Wrap tokenIn to erc4626In
                steps.push(SwapPathStep {
                    pool: *erc4626_in,
                    token_out: *erc4626_in,
                    is_buffer: true,
                });

                // Step 2: Swap erc4626In to erc4626Out
                steps.push(SwapPathStep {
                    pool: pool_address,
                    token_out: *erc4626_out,
                    is_buffer: false,
                });

                // Step 3: Unwrap erc4626Out to tokenOut
                steps.push(SwapPathStep {
                    pool: *erc4626_out,
                    token_out: token_out,
                    is_buffer: true,
                });
            }
        }
    } else {
        // Case 3: Mixed swap scenarios

        // Check if this is just a wrap or unwrap (no swap needed)
        let is_just_wrap = matches!(
            source_type,
            SwapTokenType::Asset(erc4626_addr) if token_out == *erc4626_addr
        );

        let is_just_unwrap = matches!(
            source_type,
            SwapTokenType::Erc4626Token(asset_addr) if token_out == *asset_addr
        );

        if is_just_wrap {
            // Just wrap: asset -> ERC4626
            steps.push(SwapPathStep {
                pool: token_out,
                token_out: token_out,
                is_buffer: true,
            });
        } else if is_just_unwrap {
            // Just unwrap: ERC4626 -> asset
            steps.push(SwapPathStep {
                pool: token_in,
                token_out: token_out,
                is_buffer: true,
            });
        } else {
            // There is an actual swap involved

            // If tokenIn is an asset, add wrap step
            if token_in_is_asset {
                if let SwapTokenType::Asset(erc4626_addr) = source_type {
                    steps.push(SwapPathStep {
                        pool: *erc4626_addr,
                        token_out: *erc4626_addr,
                        is_buffer: true,
                    });
                }
            }

            // Determine the intermediate token for the swap
            let swap_token_out = if token_out_is_asset {
                // If tokenOut is an asset, we need to swap to its ERC4626 token first
                if let SwapTokenType::Asset(erc4626_addr) = target_type {
                    *erc4626_addr
                } else {
                    token_out
                }
            } else {
                token_out
            };

            // Add swap step
            steps.push(SwapPathStep {
                pool: pool_address,
                token_out: swap_token_out,
                is_buffer: false,
            });

            // If tokenOut is an asset, add unwrap step
            if token_out_is_asset {
                if let SwapTokenType::Asset(erc4626_out) = target_type {
                    steps.push(SwapPathStep {
                        pool: *erc4626_out,
                        token_out: token_out,
                        is_buffer: true,
                    });
                }
            }
        }
    }

    Some(SwapPath { token_in, steps })
}

/// Convenience function that looks up token types and creates a swap path in one call
///
/// This combines `token_type_mapping` lookup with `create_swap_path()` for cleaner usage.
///
/// # Arguments
/// * `pool_address` - The pool address to use for swap steps
/// * `source_token` - The input token address
/// * `target_token` - The output token address
/// * `token_type_mapping` - HashMap from addresses to their SwapTokenType
///
/// # Returns
/// `Option<SwapPath>` - Some(path) if wrapping/unwrapping is needed, None for direct swaps
pub fn create_swap_path_for_tokens(
    pool_address: Address,
    source_token: Address,
    target_token: Address,
    token_type_mapping: &HashMap<Address, SwapTokenType>,
) -> Option<SwapPath> {
    let source_type = token_type_mapping
        .get(&source_token)
        .cloned()
        .unwrap_or(SwapTokenType::Regular);
    let target_type = token_type_mapping
        .get(&target_token)
        .cloned()
        .unwrap_or(SwapTokenType::Regular);

    create_swap_path(
        pool_address,
        source_token,
        target_token,
        &source_type,
        &target_type,
    )
}

/// Converts balancer_lib::BufferState to balancer_maths_rust::pools::BufferState
pub fn convert_buffer_state(buffer_state: &BufferState) -> balancer_maths_rust::pools::BufferState {
    use balancer_maths_rust::common::types::BasePoolState;
    use balancer_maths_rust::pools::{BufferImmutable, BufferMutable};

    balancer_maths_rust::pools::BufferState {
        base: BasePoolState {
            pool_address: buffer_state.pool_address.to_string(),
            pool_type: buffer_state.pool_type.clone(),
            tokens: buffer_state.tokens.iter().map(|t| t.to_string()).collect(),
            scaling_factors: vec![], // TODO: Remove these fields from balancer_maths
            token_rates: vec![],
            balances_live_scaled_18: vec![],
            swap_fee: num_bigint::BigInt::from(0),
            aggregate_swap_fee: num_bigint::BigInt::from(0),
            total_supply: num_bigint::BigInt::from(0),
            supports_unbalanced_liquidity: false,
            hook_type: None,
        },
        mutable: BufferMutable {
            rate: buffer_state.rate.to_big_int(),
            max_deposit: Some(buffer_state.max_deposit.to_big_int()),
            max_mint: Some(buffer_state.max_withdraw.to_big_int()),
        },
        immutable: BufferImmutable {
            pool_address: buffer_state.pool_address.to_string(),
            tokens: buffer_state.tokens.iter().map(|t| t.to_string()).collect(),
        },
    }
}

// ============================================================================
// Swap Path Execution Logic
// ============================================================================

/// Error types that can occur during swap path execution
#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
pub enum SwapPathError {
    BufferStateNotFound,
    BufferSwapError,
    PoolSwapError,
    ConversionError,
}

/// Executes a single swap through the Balancer V3 Vault
///
/// This is a helper function that creates a SwapInput and executes the swap.
///
/// # Arguments
/// * `amount` - The input amount to swap
/// * `token_in` - The input token address
/// * `token_out` - The output token address
/// * `pool_state` - The pool state for the swap
/// * `hook_state` - Optional hook state for the swap
/// * `vault` - The vault instance to execute the swap
///
/// # Returns
/// Result with the output amount as a BigInt, or a SwapPathError
pub fn execute_single_swap(
    amount: num_bigint::BigInt,
    token_in: String,
    token_out: String,
    pool_state: &balancer_maths_rust::common::types::PoolStateOrBuffer,
    hook_state: Option<&balancer_maths_rust::hooks::types::HookState>,
    vault: &balancer_maths_rust::vault::Vault,
) -> Result<num_bigint::BigInt, SwapPathError> {
    use balancer_maths_rust::common::types::{SwapInput, SwapKind};

    let swap_input = SwapInput {
        swap_kind: SwapKind::GivenIn,
        amount_raw: amount,
        token_in: token_in,
        token_out: token_out,
    };

    vault
        .swap(&swap_input, pool_state, hook_state)
        .map_err(|_| SwapPathError::PoolSwapError)
}

/// Executes a multi-step swap path through Balancer V3 pools and buffers
///
/// This function handles both buffer steps (wrap/unwrap) and regular pool swaps,
/// chaining them together to produce the final output amount.
///
/// # Arguments
/// * `swap_path` - The swap path to execute
/// * `initial_amount` - The input amount to swap
/// * `source_token` - The source token address
/// * `buffer_states` - Map of buffer addresses to their states
/// * `pool_state` - The pool state for regular pool swaps
/// * `hook_state` - Optional hook state for pool swaps
/// * `vault` - The vault instance to execute swaps
///
/// # Returns
/// Result with the final output amount as a BigInt, or a SwapPathError
pub fn execute_swap_path<'a>(
    swap_path: &SwapPath,
    initial_amount: num_bigint::BigInt,
    source_token: String,
    buffer_states: &HashMap<Address, BufferState>,
    pool_state: &'a balancer_maths_rust::common::types::PoolStateOrBuffer,
    hook_state: Option<&'a balancer_maths_rust::hooks::types::HookState>,
    vault: &balancer_maths_rust::vault::Vault,
) -> Result<num_bigint::BigInt, SwapPathError> {
    use balancer_maths_rust::common::types::{PoolStateOrBuffer, SwapInput, SwapKind};

    let mut current_amount = initial_amount;
    let mut token_in = source_token;

    for (i, step) in swap_path.steps.iter().enumerate() {
        if step.is_buffer {
            // Buffer step (wrap/unwrap)
            let swap_input = SwapInput {
                swap_kind: SwapKind::GivenIn,
                amount_raw: current_amount.clone(),
                token_in: token_in.clone(),
                token_out: step.token_out.to_string(),
            };

            if let Some(buffer_state) = buffer_states.get(&step.pool) {
                let converted_buffer = convert_buffer_state(buffer_state);

                current_amount = vault
                    .swap(
                        &swap_input,
                        &PoolStateOrBuffer::Buffer(Box::new(converted_buffer)),
                        None,
                    )
                    .map_err(|_| SwapPathError::BufferSwapError)?;
            } else {
                return Err(SwapPathError::BufferStateNotFound);
            }
        } else {
            // Regular pool step
            current_amount = execute_single_swap(
                current_amount,
                token_in,
                step.token_out.to_string(),
                pool_state,
                hook_state,
                vault,
            )?;
        }

        token_in = step.token_out.to_string();
    }

    Ok(current_amount)
}

/// Executes a swap through Balancer V3, handling both single swaps and multi-step swap paths
///
/// This is a convenience function that:
/// - Executes a multi-step swap path if provided
/// - Falls back to a single swap if no swap path is provided
/// - Converts the result from BigInt to SafeU256
///
/// # Arguments
/// * `swap_path` - Optional swap path for multi-step swaps
/// * `amount` - The input amount to swap (as SafeU256)
/// * `source_token` - The source token address (as String)
/// * `target_token` - The target token address (as String)
/// * `buffer_states` - Map of buffer addresses to their states (for swap paths)
/// * `pool_state` - The pool state for swaps
/// * `hook_state` - Optional hook state for swaps
/// * `vault` - The vault instance to execute swaps
///
/// # Returns
/// Result with the output amount as SafeU256, or a SwapPathError
pub fn execute_swap_with_path(
    swap_path: Option<&SwapPath>,
    amount: crate::barter_lib::SafeU256,
    source_token: String,
    target_token: String,
    buffer_states: &HashMap<Address, BufferState>,
    pool_state: &balancer_maths_rust::common::types::PoolStateOrBuffer,
    hook_state: Option<&balancer_maths_rust::hooks::types::HookState>,
    vault: &balancer_maths_rust::vault::Vault,
) -> Result<crate::barter_lib::SafeU256, SwapPathError> {
    use crate::barter_lib::SafeU256;

    let output_amount = if let Some(path) = swap_path {
        // Multi-step swap path
        execute_swap_path(
            path,
            amount.to_big_int(),
            source_token,
            buffer_states,
            pool_state,
            hook_state,
            vault,
        )?
    } else {
        // Single swap
        execute_single_swap(
            amount.to_big_int(),
            source_token,
            target_token,
            pool_state,
            hook_state,
            vault,
        )?
    };

    // Convert BigInt to SafeU256
    SafeU256::from_dec_str(&output_amount.to_string()).map_err(|_| SwapPathError::ConversionError)
}
