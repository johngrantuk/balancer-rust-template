# Barter Template

This is a template repository designed to accelerate the integration process for new liquidity sources into the Barter protocol. It provides a comprehensive framework for discovering, modeling, and executing swaps on automated market makers (AMMs).

# TLDR

This repository contains an example of implementing a Dodo V1 protocol integration. It demonstrates 4 essential steps: discovering new pools, fetching data for said pools, using that data to predict AMM behavior in offline mode (so the AMM output can be predicted solely based on the fetched state), and finally the encoder that uses part of this state (colloquially named Meta in this repo) to generate the executable calldata. Most of the time it's as easy as just encoding a swap function; in some cases (famously the Uniswap V4) it might be a sequence of custom-encoded bytes.

The information below provides details about how this is done, what constraints the implementation should conform to, and so on.

## Overview

This template helps developers integrate new AMM protocols by providing standardized interfaces and utility functions for all aspects of the integration process.

## Project Structure

The project is organized into several key modules, each handling a specific aspect of the AMM integration pipeline:

### Core Library (`barter_lib`)
The foundation of the template, containing essential utility types and traits:
- **SafeU256**: Safe arithmetic operations that prevent overflow/underflow
- **Swap trait**: Core interface for trade simulation and execution
- **Common types**: Standardized address, numeric, and error handling types
- **Math utilities**: Safe mathematical operations for financial calculations

### Module Organization

- **`contracts`** - Contains ABI-related code and smart contract interfaces for interacting with on-chain protocols
- **`types`** - Defines all relevant data structures following specific conventions:
  - `PoolInfo`: Immutable pool metadata (tokens, addresses, etc.) that never changes
  - `FlowerData`: Complete pool state data required for both simulation and execution
- **`discovery`** - Responsible for finding newly deployed liquidity pools on-chain. Can use any API or network method, though on-chain methods are preferred. Returns `Vec<PoolInfo>` with basic pool information
- **`polling`** - Handles real-time pool state updates. Takes a `PoolInfo` and returns current `FlowerData`
- **`model`** - Converts `FlowerData` into `Exchange` objects that implement the `Swap` trait for price prediction
- **`execution`** - Generates transaction calldata for executing actual swaps on-chain

### Reference Implementation

The repository includes a complete reference implementation for the **DODO V1** protocol, demonstrating all integration steps. You can examine the `main()` function to see the complete workflow in action. The current implementation uses the `web3-rs` library for blockchain interactions (migration to `alloy` is planned for future versions).

## Critical Requirements & Constraints

When implementing your AMM integration, you must adhere to these essential requirements to ensure system stability and correctness:

### Error Handling
- **No Panics**: The code MUST NOT panic under any circumstances. All error handling should use the `Result` type
- **Swap Trait Safety**: This is especially critical for `Swap` trait implementations, which are called frequently during route optimization
- **Safe Mathematics**: Use the provided `SafeU256` type for all mathematical operations. It handles overflow/underflow protection automatically. For other numeric types, use the `SafeMath` trait. `impl Into<SafeMathU256Result>` is a good type for an input argument for all functions for seamless error propagation

### Price Prediction Accuracy
- **Conservative Estimates**: The `Swap::swap` function MUST NOT return an output amount larger than what would actually be received in a real transaction executed on the block N+1 (where N is the block for which the state was fetched)
- **Precision Balance**: While being conservative, predictions should be as accurate as possible. Overly pessimistic estimates may cause your liquidity source to never be selected by the routing algorithm
- **State Consistency**: All simulations must be performed on the exact same blockchain state that will be used for execution

### Execution Requirements
- **Calldata Validity**: Generated calldata must be simulatable on the target block and produce results that comply with the `Swap::swap` function constraints
- **Gas Efficiency**: Execution paths should be optimized for gas consumption while maintaining accuracy
- **Transaction Safety**: All generated transactions must handle edge cases gracefully and include appropriate slippage protection

## Integration Workflow

The integration process follows a structured pipeline from liquidity discovery to trade execution. Here's the complete flow as demonstrated in the example `main()` function:

### 1. Pool Discovery
- **Objective**: Identify all available pools with liquidity for your target AMM protocol
- **Method**: Scan the blockchain (typically through registry contracts or events) to find deployed pool instances
- **Output**: Collection of `PoolInfo` objects containing immutable pool metadata

### 2. Model Validation
This step ensures your implementation correctly predicts swap outcomes:

#### Reference Transaction Setup
- **Select a test pool**: Choose any existing pool from your discovery results
- **Historical validation**: Use a real historical transaction as your reference point for accuracy verification
- **Block state**: Fetch pool data for the block immediately before your reference transaction

#### Exchange Creation and Testing
- **State conversion**: Transform the `FlowerData` into `Exchange` objects using the `to_exchanges()` method
- **Direction mapping**: Each pool typically generates multiple exchanges (e.g., a 2-token pool creates 2 exchanges: A→B and B→A)
- **Swap simulation**: Use the `swap()` function to predict the output for your reference input
- **Validation**: Compare predicted output with the actual historical result

### 3. Calldata Generation
- **Encoding**: Generate the exact transaction calldata needed to execute the swap on-chain
- **Testing**: The generated calldata should be simulatable using tools like Tenderly
- **Verification**: Ensure the simulation produces results that match your model's predictions

### Example Implementation Flow

```rust
// 1. Discover all pools
let pools = discovery::dodo_v1::get_all_pools(&web3).await;

// 2. Select a pool and fetch its current state
let pool_data = polling::dodo_v1::get_flower_data(&web3, pool_info, block_id).await;

// 3. Convert to exchanges
let exchanges = pool_data.to_exchanges(&mut exchange_context);

// 4. Test prediction accuracy
let predicted_output = exchange.swap(input_amount)?;

// 5. Generate execution calldata
let calldata = execution::dodo_v1::encode(input_amount, min_output, &exchange.meta);
```

This workflow ensures that your integration is thoroughly tested and ready for production use within the Barter routing system.

## Getting Started

### Prerequisites
- **Rust**: Nightly toolchain (compiled on rustc 1.89.0-nightly)
- **Environment**: Set up your `.env` file with required RPC endpoints
- **Dependencies**: All required crates are specified in `Cargo.toml`

### Quick Start
1. **Clone the repository**
2. **Study the DODO V1 implementation**: Examine all modules to understand the integration pattern
3. **Implement your AMM**: Replace DODO V1 logic with your target protocol
4. **Test thoroughly**: Validate against historical transactions
5. **Deploy and integrate**: Submit your implementation for review

### Environment Configuration
Create a `.env` file in the project root:
```env
MAINNET_RPC_URL=https://your-ethereum-rpc-endpoint
```

### Running the Example
```bash
cargo run
```

This will execute the complete DODO V1 integration workflow, demonstrating:
- Pool discovery from the registry contract
- State polling for a specific historical block
- Price prediction validation against a known transaction
- Calldata generation for swap execution

## Key Design Patterns

### Exchange Abstraction
The `Exchange` type abstracts individual trading pairs, allowing the routing algorithm to treat all liquidity sources uniformly. A single pool with N tokens generates N×(N-1) exchanges covering all possible trading directions.

### Safe Mathematics
All financial calculations use panic-safe arithmetic through `SafeU256` and related types. 

### Sync Architecture
The template uses async/await only for data fetching, output prediction and encoding steps should be pure functions with no network interaction

## Acknowledgments

We're grateful to our partners who help us integrate new liquidity sources. If you find any part of this process confusing or could be improved, please let us know so we can enhance this template for you.
