// Modified by 2024 HybirdVM

// Modified by 2021 Cycan Technologies 

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Modified by Alex Wang

use super::*;

use crate::mock::*;
use frame_support::{assert_noop, assert_ok};

use crate::{U256, H160, };

use pallet_contracts::{
	BalanceOf, ContractInfoOf, Schedule,
	chain_extension::{
		Environment, Ext, SysConfig, RetVal,
		UncheckedFrom, InitState, 
	},
};

use codec::{Encode, Decode};
use sp_runtime::{
	traits::{BlakeTwo256, Hash, IdentityLookup, Convert, },
	testing::{Header, H256},
	AccountId32, Perbill, PerThing,
};

use frame_support::{
	assert_ok, parameter_types,  
	traits::{Currency, GenesisBuild},
	weights::{Weight, constants::WEIGHT_PER_SECOND},
	dispatch::{DispatchError}, 
};

use pretty_assertions::assert_eq;
use ink_env::call::{Selector, ExecutionInput};
use sha3::{Keccak256, Digest};

use pallet_evm::{
        FeeCalculator, AddressMapping, EnsureAddressTruncated, Runner, 
		ExitReason, CallInfo, CreateInfo, SubstrateBlockHashMapping, 
};

use frame_system::pallet_prelude::*;
use std::error::Error;
use serde::{Deserialize, Serialize};

use crate as pallet_hybird_vm;

#[derive(Deserialize, Encode, Decode, Serialize, Debug)]
#[allow(non_snake_case)]
struct CallReturn  {
	Result: u32,
	Message: String,
	ReturnValue:Vec<String>,
}

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;


const GAS_LIMIT: Weight = 1000_000_000_000;

/// Load a given wasm module represented by a .wat file and returns a wasm binary contents along
/// with it's hash.
///
/// The fixture files are located under the `fixtures/` directory.
fn _compile_module<T>(
	fixture_name: &str,
) -> wat::Result<(Vec<u8>, <T::Hashing as Hash>::Output)>
where
	T: frame_system::Config,
{
	let fixture_path = ["fixtures/", fixture_name, ".wat"].concat();
	let wasm_binary = wat::parse_file(fixture_path)?;
	let code_hash = T::Hashing::hash(&wasm_binary);
	Ok((wasm_binary, code_hash))
}



use std::fs::File;
use std::io::Read;

fn read_a_file(filename: &str) -> std::io::Result<Vec<u8>> {
    let mut file = File::open(filename)?;

    let mut data = Vec::new();
    file.read_to_end(&mut data)?;

    return Ok(data);
}

fn contract_module<T>(
	contract_name: &str,
	wasmtype: bool,
) -> Result<(Vec<u8>, <T::Hashing as Hash>::Output), Box<dyn Error>>
where
	T: frame_system::Config,
{
	let contract_path = ["fixtures/", contract_name].concat();
	let contract_binary: Vec<u8>;
	
	if wasmtype {
		contract_binary = read_a_file(&contract_path)?;
		
	} else {
		let bytecode = read_a_file(&contract_path)?;
		contract_binary = hex::decode(bytecode)?;
	}
	
	let code_hash = T::Hashing::hash(&contract_binary);
	Ok((contract_binary, code_hash))
}

// Perform test for wasm contract  calling  EVM contract to transfer EVM ERC20 token
#[test]
fn test_wasm_call_evm(){

	// 1.  Get wasm and evm contract bin
	let (wasm, wasm_code_hash) = contract_module::<Test>("erc20.wasm", true).unwrap();
	let (evm, _evm_code_hash) = contract_module::<Test>("erc20_evm_bytecode.txt", false).unwrap();
	
	ExtBuilder::default()
	.existential_deposit(100)
	.build()
	.execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 10_000_000_000_000);
		let subsistence = Contracts::subsistence_threshold();
		
		// 2. Create wasm contract
		let mut a: [u8; 4] = Default::default();
		a.copy_from_slice(&BlakeTwo256::hash(b"new")[0..4]);		
		let new_call = ExecutionInput::new( Selector::new(a) );
	
		let init_supply: <Test as pallet_balances::Config>::Balance  = 100_000_000_000_000_000_000_000;
		let new_call = new_call.push_arg(init_supply);
		let creation = Contracts::instantiate_with_code(
			Origin::signed(ALICE.clone()),
			subsistence * 10_000_000,
			GAS_LIMIT,
			wasm,
			new_call.encode(),
			vec![],
		);
		
		assert_ok!(creation);
		let wasm_addr = Contracts::contract_address(&ALICE, &wasm_code_hash, &[]);

		assert!(ContractInfoOf::<Test>::contains_key(&wasm_addr));	
		
		//3. Create EVM contract  and tranfer to bob token
		let source = H160::from_slice(&(AsRef::<[u8; 32]>::as_ref(&ALICE)[0..20]));
		
		let creation4evm = <Test as pallet_evm::Config>::Runner::create(   
			source,
			evm,
			U256::default(),
			100_000_000_000,
			Some(U256::default()),
			Some(U256::from(0)),
			<Test as pallet_evm::Config>::config(),
		);
		
		assert_ok!(&creation4evm);
		
		let evm_addr: H160;
		
		match creation4evm.unwrap() {
			CreateInfo {
				exit_reason: ExitReason::Succeed(_),
				value: create_address,
				..
			} => {
				evm_addr = create_address;
			},
			CreateInfo {
				exit_reason: reason,
				value: _,
				..
			} => {
				panic!("Create EVM Contract failed!({:?})", reason);
			},
		}
		
		//3.1 Alice tranfer token to  Bob
		let transfer_selector = &Keccak256::digest(b"transfer(address,uint256)")[0..4];
		
		let source_bob = H160::from_slice(&(AsRef::<[u8; 32]>::as_ref(&BOB)[0..20]));
		let token: u128 = 1_883_000_000_000_000_000;
		
		let fun_para: [u8;20] = source_bob.into();
		let transfer_input = [&transfer_selector[..], &[0u8;12], &fun_para, &[0u8;16], &token.to_be_bytes()].concat();		
		
		let call4evm = <Test as pallet_evm::Config>::Runner::call(
				source,
				evm_addr,
				transfer_input.clone(),
				U256::default(),
				100_000_000,
				Some(U256::default()),
				Some(U256::from(1)),
				<Test as pallet_evm::Config>::config(),
			);

		assert_ok!(&call4evm);
		
		let transfer_result: u128;
		
		match call4evm.unwrap() {
			CallInfo {
				exit_reason: ExitReason::Succeed(_),
				value: return_value,
				..
			} => {
				let mut a: [u8; 16] = Default::default();
				a.copy_from_slice(&return_value[16..32]);
				transfer_result = u128::from_be_bytes(a);
			},
			CallInfo {
				exit_reason: reason,
				value: _,
				..			
			} => {
				panic!("Call EVM Contract balanceOf failed!({:?})", reason);
			},
		};
		println!("Alice transfer to Bob token:{}", transfer_result);
		
		//4. Get BOB balance of EVM token
		let balance_of_selector = &Keccak256::digest(b"balanceOf(address)")[0..4];
		
		let source_bob = H160::from_slice(&(AsRef::<[u8; 32]>::as_ref(&BOB)[0..20]));
			
		let fun_para: [u8;20] = source_bob.into();
		let balance_of_input = [&balance_of_selector[..], &[0u8;12], &fun_para].concat();		
		
		let call4evm = <Test as pallet_evm::Config>::Runner::call(
				source_bob,
				evm_addr,
				balance_of_input.clone(),
				U256::default(),
				100_000_000,
				Some(U256::default()),
				Some(U256::from(0)),
				<Test as pallet_evm::Config>::config(),
			);

		assert_ok!(&call4evm);
		
		let bob_balance_before: u128;
		
		match call4evm.unwrap() {
			CallInfo {
				exit_reason: ExitReason::Succeed(_),
				value: return_value,
				..
			} => {
				let mut a: [u8; 16] = Default::default();
				a.copy_from_slice(&return_value[16..32]);
				bob_balance_before = u128::from_be_bytes(a);
			},
			CallInfo {
				exit_reason: reason,
				value: _,
				..			
			} => {
				panic!("Call EVM Contract balanceOf failed!({:?})", reason);
			},
		};
		println!("bob_balance_before={}",bob_balance_before);
		
		//5.  Call wasm contract to call evm transfer evm token to bob.  H160: evm contract address, H160: bob's address  u128: value
		let mut a: [u8; 4] = Default::default();
		a.copy_from_slice(&BlakeTwo256::hash(b"wasmCallEvm")[0..4]);
		let call = ExecutionInput::new(Selector::new(a));
		
		let transfer_value: u128  = 12000000000000000000;
		
		let call = call.push_arg(format!("0x{:x}", evm_addr)).push_arg(format!("0x{:x}", source_bob)).push_arg(transfer_value);
		
		let result = Contracts::bare_call(
				ALICE, 
				wasm_addr,
				0,
				GAS_LIMIT,
				Encode::encode(&call).to_vec(),
			).exec_result.unwrap();
		assert!(result.is_success());
		println!("Alice transfer to Bob from wasm_call_evm:{}", transfer_value);
		
		//6. Get BOB balance of EVM token
		let call4evm = <Test as pallet_evm::Config>::Runner::call(
				source_bob,
				evm_addr,
				balance_of_input,
				U256::default(),
				100_000_000,
				Some(U256::default()),
				Some(U256::from(1)),
				<Test as pallet_evm::Config>::config(),
			);

		assert_ok!(&call4evm);
		
		let bob_balance_after: u128;
		
		match call4evm.unwrap() {
			CallInfo {
				exit_reason: ExitReason::Succeed(_),
				value: return_value,
				..
			} => {
				let mut a: [u8; 16] = Default::default();
				a.copy_from_slice(&return_value[16..32]);				
				bob_balance_after = u128::from_be_bytes(a);
			},
			CallInfo {
				exit_reason: reason,
				value: _,
				..			
			} => {
				panic!("Call EVM Contract balanceOf failed!({:?})", reason);
			},
		};		
		println!("bob_balance_after={}",bob_balance_after);
		//7. Test  the balance of BOB being correct
		assert_eq!(bob_balance_after, bob_balance_before + transfer_value);	
	});
}


// Perform test for EVM contract  calling  wasm contract to transfer wasm ERC20 token
#[test]
fn test_evm_call_wasm(){

	// 1.  Get wasm and evm contract bin
	let (wasm, wasm_code_hash) = contract_module::<Test>("erc20.wasm", true).unwrap();
	let (evm, _evm_code_hash) = contract_module::<Test>("erc20_evm_bytecode.txt", false).unwrap();
	
	ExtBuilder::default()
	.existential_deposit(100)
	.build()
	.execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 10_000_000_000_000);
		let subsistence = Contracts::subsistence_threshold();

		// 2. Create wasm contract
		let mut a: [u8; 4] = Default::default();
		a.copy_from_slice(&BlakeTwo256::hash(b"new")[0..4]);		
		let new_call = ExecutionInput::new( Selector::new(a) );
	
		let init_supply: <Test as pallet_balances::Config>::Balance  = 100_000_000_000_000_000_000_000;
		let new_call = new_call.push_arg(init_supply);
		let creation = Contracts::instantiate_with_code(
			Origin::signed(ALICE.clone()),
			subsistence  * 10_000_000,
			GAS_LIMIT,
			wasm,
			new_call.encode(),
			vec![],
		);
		let wasm_addr = Contracts::contract_address(&ALICE, &wasm_code_hash, &[]);

		assert_ok!(creation);
		assert!(ContractInfoOf::<Test>::contains_key(&wasm_addr));	
		
		//2.1 Transfer Token to BOB
		let mut a: [u8; 4] = Default::default();
		a.copy_from_slice(&BlakeTwo256::hash(b"transfer")[0..4]);		
		let transfer_call = ExecutionInput::new( Selector::new(a) );
		
		let token: <Test as pallet_balances::Config>::Balance  = 1_213_000_789_000_000_000_000;		
		let transfer_call = transfer_call.push_arg(&BOB).push_arg(token);
		
		let result = Contracts::bare_call(
					ALICE.clone(),
					wasm_addr.clone(),
					0,
					GAS_LIMIT,
					transfer_call.encode(),
				).exec_result.unwrap();
				
		assert!(result.is_success());
		
		//3. Create EVM contract
		let source = H160::from_slice(&(AsRef::<[u8; 32]>::as_ref(&ALICE)[0..20]));
		
		let creation4evm = <Test as pallet_evm::Config>::Runner::create(
			//Origin::signed(ALICE),
			source,
			evm,
			U256::default(),
			100_000_000,
			Some(U256::default()),
			Some(U256::from(0)),
			<Test as pallet_evm::Config>::config(),
		);
		
		assert_ok!(&creation4evm);
		
		let evm_addr: H160;
		match creation4evm.unwrap() {
			CreateInfo {
				exit_reason: ExitReason::Succeed(_),
				value: create_address,
				..
			} => {
				evm_addr = create_address;
			},
			CreateInfo {
				exit_reason: reason,
				value: _,
				..
			} => {
				panic!("Create EVM Contract failed!({:?})", reason);
			},
		}
		
		//4. Get BOB balance of wasm token
		let mut a: [u8; 4] = Default::default();
		a.copy_from_slice(&BlakeTwo256::hash(b"balance_of")[0..4]);		
		let balance_of_call = ExecutionInput::new( Selector::new(a) );
		
		let balance_of_call = balance_of_call.push_arg(&BOB);
						
		let result = Contracts::bare_call(
					BOB.clone(),
					wasm_addr.clone(),
					0,
					GAS_LIMIT,
					//Encode::encode(&balance_of_call).to_vec(),
					balance_of_call.encode(),
				).exec_result.unwrap();
		assert!(result.is_success());
		
		println!("result data before:{:?}", result);
		let bob_balance_before = result.data;
		
				
		//5.  Call EVM contract to call wasm contract transfer wasm token to bob,  the last bytes32 is the wasm contract accountid
		let evm_call_wasm_selector = &Keccak256::digest(b"evmCallWasm(bytes32,uint256,bytes32)")[0..4];

		let transfer_value: u128  = 12000000000000000000;
		
		let wasm_contract: [u8; 32] = wasm_addr.clone().into();
				
		let evm_call_wasm_input = [&evm_call_wasm_selector[..], AsRef::<[u8; 32]>::as_ref(&BOB), &[0u8;16], &transfer_value.to_be_bytes(), &wasm_contract].concat();
		
		let source_alice = H160::from_slice(&(AsRef::<[u8; 32]>::as_ref(&ALICE)[0..20]));
		
		let call4evm = <Test as pallet_evm::Config>::Runner::call(
				source_alice,
				evm_addr,
				evm_call_wasm_input,
				U256::default(),
				100_000_000_000,
				Some(U256::default()),
				Some(U256::from(1)),
				<Test as pallet_evm::Config>::config(),
			);
		assert_ok!(&call4evm);
		assert!(&call4evm.unwrap().exit_reason.is_succeed());
		println!("Alice transfer to Bob from evm_call_wasm:{}", transfer_value);

		//6. Get BOB balance of wasm token
		let result = Contracts::bare_call(
					BOB.clone(),
					wasm_addr.clone(),
					0,
					GAS_LIMIT,
					Encode::encode(&balance_of_call).to_vec(),
				).exec_result.unwrap();
		assert!(result.is_success());
	
		println!("result data after:{:?}", result);
		let bob_balance_after = result.data;		
				
		//7. Test  the balance of BOB being correct
		let after = <u128 as Decode>::decode(&mut &bob_balance_after[..]).unwrap();
		let before = <u128 as Decode>::decode(&mut &bob_balance_before[..]).unwrap();
		assert_eq!(after, before + transfer_value);	
	});
}

// Perform test for wasm contract calling  EVM contract to get bob's EVM ERC20 token balance
#[test]
fn test_wasm_call_evm_balance(){

	// 1.  Get wasm and evm contract bin
	let (wasm, wasm_code_hash) = contract_module::<Test>("erc20.wasm", true).unwrap();
	let (evm, _evm_code_hash) = contract_module::<Test>("erc20_evm_bytecode.txt", false).unwrap();
	
	ExtBuilder::default()
	.existential_deposit(100)
	.build()
	.execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 10_000_000_000_000);
		let subsistence = Contracts::subsistence_threshold();
		
		// 2. Create wasm contract
		let mut a: [u8; 4] = Default::default();
		a.copy_from_slice(&BlakeTwo256::hash(b"new")[0..4]);		
		let new_call = ExecutionInput::new( Selector::new(a) );
	
		let init_supply: <Test as pallet_balances::Config>::Balance  = 100_000_000_000_000_000_000_000;
		let new_call = new_call.push_arg(init_supply);
		let creation = Contracts::instantiate_with_code(
			Origin::signed(ALICE.clone()),
			subsistence * 10_000_000,
			GAS_LIMIT,
			wasm,
			new_call.encode(),
			vec![],
		);
		
		assert_ok!(creation);
		let wasm_addr = Contracts::contract_address(&ALICE, &wasm_code_hash, &[]);

		assert!(ContractInfoOf::<Test>::contains_key(&wasm_addr));	
		
		//3. Create EVM contract  and tranfer to bob token
		let source = H160::from_slice(&(AsRef::<[u8; 32]>::as_ref(&ALICE)[0..20]));
		
		let creation4evm = <Test as pallet_evm::Config>::Runner::create(   
			source,
			evm,
			U256::default(),
			100_000_000_000,
			Some(U256::default()),
			Some(U256::from(0)),
			<Test as pallet_evm::Config>::config(),
		);
		
		assert_ok!(&creation4evm);
		
		let evm_addr: H160;
		
		match creation4evm.unwrap() {
			CreateInfo {
				exit_reason: ExitReason::Succeed(_),
				value: create_address,
				..
			} => {
				evm_addr = create_address;
			},
			CreateInfo {
				exit_reason: reason,
				value: _,
				..
			} => {
				panic!("Create EVM Contract failed!({:?})", reason);
			},
		}
		
		//3.1 Alice tranfer token to  Bob
		let transfer_selector = &Keccak256::digest(b"transfer(address,uint256)")[0..4];
		
		let source_bob = H160::from_slice(&(AsRef::<[u8; 32]>::as_ref(&BOB)[0..20]));
		let token: u128 = 1_883_000_000_000_000_000;
		
		let fun_para: [u8;20] = source_bob.into();
		let transfer_input = [&transfer_selector[..], &[0u8;12], &fun_para, &[0u8;16], &token.to_be_bytes()].concat();		
		
		let call4evm = <Test as pallet_evm::Config>::Runner::call(
				source,
				evm_addr,
				transfer_input.clone(),
				U256::default(),
				100_000_000,
				Some(U256::default()),
				Some(U256::from(1)),
				<Test as pallet_evm::Config>::config(),
			);

		assert_ok!(&call4evm);
		
		let transfer_result: u128;
		
		match call4evm.unwrap() {
			CallInfo {
				exit_reason: ExitReason::Succeed(_),
				value: return_value,
				..
			} => {
				let mut a: [u8; 16] = Default::default();
				a.copy_from_slice(&return_value[16..32]);
				transfer_result = u128::from_be_bytes(a);
			},
			CallInfo {
				exit_reason: reason,
				value: _,
				..			
			} => {
				panic!("Call EVM Contract transfer failed!({:?})", reason);
			},
		};
		
		println!("Alice transfer to Bob evm result:{}, tokens:{}", transfer_result, token);

		//4.  Call wasm contract to call evm for getting BOB balance of EVM token.  H160: evm contract address, H160: BOB's address  
		let mut a: [u8; 4] = Default::default();
		a.copy_from_slice(&BlakeTwo256::hash(b"wasmCallEvmBalance")[0..4]);
		let call = ExecutionInput::new(Selector::new(a));
				
		let call = call.push_arg(format!("0x{:x}", evm_addr)).push_arg(format!("0x{:x}", source_bob));
		
		let result = Contracts::bare_call(
				ALICE, 
				wasm_addr,
				0,
				GAS_LIMIT,
				Encode::encode(&call).to_vec(),
			).exec_result.unwrap();
		println!("call wasmCallEvmBalance result:{:?}", result);	
		assert!(result.is_success());
		assert!(result.data[0] == 0u8);
		
		let balance_return = <u128 as Decode>::decode(&mut &result.data[1..]).unwrap();
		println!("BOB's  evm token balance:{:?}", balance_return);
		
		//5. Test  the evm token balance of BOB being correct 
		assert_eq!(balance_return, token);	
		
	});
}


// Perform test for EVM contract  calling  wasm contract to get bob's wasm ERC20 token balance
#[test]
fn test_evm_call_wasm_balance(){

	// 1.  Get wasm and evm contract bin
	let (wasm, wasm_code_hash) = contract_module::<Test>("erc20.wasm", true).unwrap();
	let (evm, _evm_code_hash) = contract_module::<Test>("erc20_evm_bytecode.txt", false).unwrap();
	
	ExtBuilder::default()
	.existential_deposit(100)
	.build()
	.execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 10_000_000_000_000);
		let subsistence = Contracts::subsistence_threshold();

		// 2. Create wasm contract
		let mut a: [u8; 4] = Default::default();
		a.copy_from_slice(&BlakeTwo256::hash(b"new")[0..4]);		
		let new_call = ExecutionInput::new( Selector::new(a) );
	
		let init_supply: <Test as pallet_balances::Config>::Balance  = 100_000_000_000_000_000_000_000;
		let new_call = new_call.push_arg(init_supply);
		let creation = Contracts::instantiate_with_code(
			Origin::signed(ALICE.clone()),
			subsistence  * 10_000_000,
			GAS_LIMIT,
			wasm,
			new_call.encode(),
			vec![],
		);
		let wasm_addr = Contracts::contract_address(&ALICE, &wasm_code_hash, &[]);

		assert_ok!(creation);
		assert!(ContractInfoOf::<Test>::contains_key(&wasm_addr));	
		
		//2.1 Transfer Token to BOB
		let mut a: [u8; 4] = Default::default();
		a.copy_from_slice(&BlakeTwo256::hash(b"transfer")[0..4]);		
		let transfer_call = ExecutionInput::new( Selector::new(a) );
		
		let token: <Test as pallet_balances::Config>::Balance  = 1_213_000_789_000_000_000_000;		
		let transfer_call = transfer_call.push_arg(&BOB).push_arg(token);
		
		let result = Contracts::bare_call(
					ALICE.clone(),
					wasm_addr.clone(),
					0,
					GAS_LIMIT,
					transfer_call.encode(),
				).exec_result.unwrap();
				
		assert!(result.is_success());
		println!("Alice transfer to Bob wasm token:{}", token);
		
		//3. Create EVM contract
		let source = H160::from_slice(&(AsRef::<[u8; 32]>::as_ref(&ALICE)[0..20]));
		
		let creation4evm = <Test as pallet_evm::Config>::Runner::create(
			//Origin::signed(ALICE),
			source,
			evm,
			U256::default(),
			100_000_000,
			Some(U256::default()),
			Some(U256::from(0)),
			<Test as pallet_evm::Config>::config(),
		);
		
		assert_ok!(&creation4evm);
		
		let evm_addr: H160;
		match creation4evm.unwrap() {
			CreateInfo {
				exit_reason: ExitReason::Succeed(_),
				value: create_address,
				..
			} => {
				evm_addr = create_address;
			},
			CreateInfo {
				exit_reason: reason,
				value: _,
				..
			} => {
				panic!("Create EVM Contract failed!({:?})", reason);
			},
		}
		
		//4.  Call evm contract to call wasm for getting BOB balance of wasm token.  H160: BOB's address , the last bytes32 is the wasm contract accountid
		let evm_call_wasm_selector = &Keccak256::digest(b"evmCallWasmBalance(bytes32,bytes32)")[0..4];
		
		let wasm_contract: [u8; 32] = wasm_addr.clone().into();
				
		let evm_call_wasm_input = [&evm_call_wasm_selector[..], AsRef::<[u8; 32]>::as_ref(&BOB), &wasm_contract].concat();
		
		let source_alice = H160::from_slice(&(AsRef::<[u8; 32]>::as_ref(&ALICE)[0..20]));
		
		let call4evm = <Test as pallet_evm::Config>::Runner::call(
				source_alice,
				evm_addr,
				evm_call_wasm_input,
				U256::default(),
				100_000_000_000,
				Some(U256::default()),
				Some(U256::from(1)),
				<Test as pallet_evm::Config>::config(),
			);
		assert_ok!(&call4evm);
						
		println!("call evmCallWasmBalance reuslt:{:?}", call4evm);
		
		let bob_balance: u128;
		match call4evm.unwrap() {
			CallInfo {
				exit_reason: ExitReason::Succeed(_),
				value: return_value,
				..
			} => {
				let mut a: [u8; 16] = Default::default();
				a.copy_from_slice(&return_value[16..32]);				
				bob_balance = u128::from_be_bytes(a);
			},
			CallInfo {
				exit_reason: reason,
				value: _,
				..			
			} => {
				panic!("Call EVM Contract fun evmCallWasmBalance failed!({:?})", reason);
			},
		};		
		
		println!("BOB's  wasm token balance:{}", bob_balance);
		
		//5. Test  the wasm token balance of BOB being correct 
		assert_eq!(bob_balance, token);
		
	});
}

// Perform test for wasm contract calling  EVM echo contract, testing parameters of different data types.
#[test]
fn test_wasm_call_evm_echo(){

	// 1.  Get wasm and evm contract bin
	let (wasm, wasm_code_hash) = contract_module::<Test>("erc20.wasm", true).unwrap();
	let (evm, _evm_code_hash) = contract_module::<Test>("erc20_evm_bytecode.txt", false).unwrap();
	
	ExtBuilder::default()
	.existential_deposit(100)
	.build()
	.execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 10_000_000_000_000);
		let subsistence = Contracts::subsistence_threshold();
		
		// 2. Create wasm contract
		let mut a: [u8; 4] = Default::default();
		a.copy_from_slice(&BlakeTwo256::hash(b"new")[0..4]);		
		let new_call = ExecutionInput::new( Selector::new(a) );
	
		let init_supply: <Test as pallet_balances::Config>::Balance  = 100_000_000_000_000_000_000_000;
		let new_call = new_call.push_arg(init_supply);
		let creation = Contracts::instantiate_with_code(
			Origin::signed(ALICE.clone()),
			subsistence * 10_000_000,
			GAS_LIMIT,
			wasm,
			new_call.encode(),
			vec![],
		);
		
		assert_ok!(creation);
		let wasm_addr = Contracts::contract_address(&ALICE, &wasm_code_hash, &[]);

		assert!(ContractInfoOf::<Test>::contains_key(&wasm_addr));	
		
		//3. Create EVM contract  
		let source = H160::from_slice(&(AsRef::<[u8; 32]>::as_ref(&ALICE)[0..20]));
		
		let creation4evm = <Test as pallet_evm::Config>::Runner::create(   
			source,
			evm,
			U256::default(),
			100_000_000_000,
			Some(U256::default()),
			Some(U256::from(0)),
			<Test as pallet_evm::Config>::config(),
		);
		
		assert_ok!(&creation4evm);
		
		let evm_addr: H160;
		
		match creation4evm.unwrap() {
			CreateInfo {
				exit_reason: ExitReason::Succeed(_),
				value: create_address,
				..
			} => {
				evm_addr = create_address;
			},
			CreateInfo {
				exit_reason: reason,
				value: _,
				..
			} => {
				panic!("Create EVM Contract failed!({:?})", reason);
			},
		}
		
		//4.  Call wasm contract to call evm using  parameters of different data types.
		let mut a: [u8; 4] = Default::default();
		a.copy_from_slice(&BlakeTwo256::hash(b"wasmCallEvmProxy")[0..4]);
		let call = ExecutionInput::new(Selector::new(a));
		let call_para = [
				r#"{"VM":"evm", "Account":""#, 
				&format!("0x{:x}", evm_addr), 
				r#"","Fun":"echo(string,uint256[])","InputType":["string","uint[]"],"InputValue":["#,
				r#""test string!","3","231","19","6"],"OutputType":[["string","uint[]"]]}"#
			].concat();
		let call = call.push_arg(call_para);
		
		let result = Contracts::bare_call(
				ALICE, 
				wasm_addr,
				0,
				GAS_LIMIT,
				Encode::encode(&call).to_vec(),
			).exec_result.unwrap();
		println!("call wasmCallEvmProxy result:{:?}", result);	
		assert!(result.is_success());
		assert!(result.data[0] == 0u8);
		
		let echo_result = <String as Decode>::decode(&mut &result.data[1..]).unwrap();
		println!("Evm echo return:{:?}", echo_result);
		let call_return: CallReturn = serde_json::from_slice(echo_result.as_bytes()).unwrap();
		let echo_string = (call_return.ReturnValue[0]).parse::<String>().unwrap();
		let mut echo_arr = [0usize; 100];
		let echo_arr_len = (call_return.ReturnValue[1]).parse::<usize>().unwrap();
		let mut i: usize = 0;
		while i< echo_arr_len {
			echo_arr[i] = (call_return.ReturnValue[2+i]).parse::<usize>().unwrap();
			i += 1;
		}
		println!("array:{:?}", echo_arr);
		//5. Test  whether the evm echo result is correct 
		assert_eq!(&echo_string, "test string!");
		assert_eq!(echo_arr[0..echo_arr_len], [231usize, 19usize, 6usize][..]);
		
	});
}


// Perform test for EVM contract calling  wasm echo contract, testing parameters of different data types.
#[test]
fn test_evm_call_wasm_echo(){

	// 1.  Get wasm and evm contract bin
	let (wasm, wasm_code_hash) = contract_module::<Test>("erc20.wasm", true).unwrap();
	let (evm, _evm_code_hash) = contract_module::<Test>("erc20_evm_bytecode.txt", false).unwrap();
	
	ExtBuilder::default()
	.existential_deposit(100)
	.build()
	.execute_with(|| {
		let _ = Balances::deposit_creating(&ALICE, 10_000_000_000_000);
		let subsistence = Contracts::subsistence_threshold();

		// 2. Create wasm contract
		let mut a: [u8; 4] = Default::default();
		a.copy_from_slice(&BlakeTwo256::hash(b"new")[0..4]);		
		let new_call = ExecutionInput::new( Selector::new(a) );
	
		let init_supply: <Test as pallet_balances::Config>::Balance  = 100_000_000_000_000_000_000_000;
		let new_call = new_call.push_arg(init_supply);
		let creation = Contracts::instantiate_with_code(
			Origin::signed(ALICE.clone()),
			subsistence  * 10_000_000,
			GAS_LIMIT,
			wasm,
			new_call.encode(),
			vec![],
		);
		let wasm_addr = Contracts::contract_address(&ALICE, &wasm_code_hash, &[]);

		assert_ok!(creation);
		assert!(ContractInfoOf::<Test>::contains_key(&wasm_addr));	
		
		//3. Create EVM contract
		let source = H160::from_slice(&(AsRef::<[u8; 32]>::as_ref(&ALICE)[0..20]));
		
		let creation4evm = <Test as pallet_evm::Config>::Runner::create(
			//Origin::signed(ALICE),
			source,
			evm,
			U256::default(),
			100_000_000,
			Some(U256::default()),
			Some(U256::from(0)),
			<Test as pallet_evm::Config>::config(),
		);
		
		assert_ok!(&creation4evm);
		
		let evm_addr: H160;
		match creation4evm.unwrap() {
			CreateInfo {
				exit_reason: ExitReason::Succeed(_),
				value: create_address,
				..
			} => {
				evm_addr = create_address;
			},
			CreateInfo {
				exit_reason: reason,
				value: _,
				..
			} => {
				panic!("Create EVM Contract failed!({:?})", reason);
			},
		}
		
		//4.  Call evm contract to call wasm  using  parameters of different data types.
		let evm_call_wasm_selector = &Keccak256::digest(b"evmCallWasmProxy(string)")[0..4];
		
		let wasm_contract: [u8; 32] = wasm_addr.clone().into();
		
		let call_para = [
				r#"{"VM":"wasm", "Account":"0x"#, 
				&hex::encode(wasm_contract), 
				r#"","Fun":"echo","InputType":["string","vec","u8","u8","u8"],"InputValue":["#,
				r#""test string!","3","231","19","6"],"OutputType":[["string","vec"],["2"],["u8"]]}"#
			].concat();		
		let call_para_len: u128 = call_para.len() as u128;
				
		let evm_call_wasm_input = [&evm_call_wasm_selector[..], &[0u8; 31], &[32u8], &[0u8; 16], &call_para_len.to_be_bytes(), call_para.as_bytes()].concat();
		
		let source_alice = H160::from_slice(&(AsRef::<[u8; 32]>::as_ref(&ALICE)[0..20]));
		
		let call4evm = <Test as pallet_evm::Config>::Runner::call(
				source_alice,
				evm_addr,
				evm_call_wasm_input,
				U256::default(),
				100_000_000_000,
				Some(U256::default()),
				Some(U256::from(1)),
				<Test as pallet_evm::Config>::config(),
			);
		assert_ok!(&call4evm);
						
		println!("call evmCallWasmProxy reuslt:{:?}", call4evm);
		
		let echo_result: String;
		match call4evm.unwrap() {
			CallInfo {
				exit_reason: ExitReason::Succeed(_),
				value: return_value,
				..
			} => {
				let mut output_value: [u8; 16] = Default::default();
				let mut out_value: [u8; 16] = Default::default();
				output_value.copy_from_slice(&return_value[16..32]);
				let uintdata = u128::from_be_bytes(output_value) as usize;
				out_value.copy_from_slice(&return_value[uintdata+16..uintdata+32]);
				
				let datalen = u128::from_be_bytes(out_value) as usize;							
				let data = &return_value[uintdata+32..uintdata+32+datalen];
				echo_result = String::from_utf8(data.to_vec()).unwrap();				
			},
			CallInfo {
				exit_reason: reason,
				value: _,
				..			
			} => {
				panic!("Call EVM Contract fun evmCallWasmBalance failed!({:?})", reason);
			},
		};		
		
		println!("Wasm echo return:{:?}", echo_result);
		let call_return: CallReturn = serde_json::from_slice(echo_result.as_bytes()).unwrap();
		let echo_string = (call_return.ReturnValue[0]).parse::<String>().unwrap();
		let mut echo_arr = [0usize; 100];
		let echo_arr_len = (call_return.ReturnValue[1]).parse::<usize>().unwrap();
		let mut i: usize = 0;
		while i< echo_arr_len {
			echo_arr[i] = (call_return.ReturnValue[2+i]).parse::<usize>().unwrap();
			i += 1;
		}
		println!("array:{:?}", echo_arr);
		//5. Test  whether the wasm echo result is correct 
		assert_eq!(&echo_string, "test string!");
		assert_eq!(echo_arr[0..echo_arr_len], [231usize, 19usize, 6usize][..]);		
		
	});
}

