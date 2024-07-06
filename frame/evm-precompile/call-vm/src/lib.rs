// Copyright (C) 2021 Cycan Technologies
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::vec::Vec;
use core::marker::PhantomData;
use fp_evm::Precompile;
use evm::{ExitSucceed, ExitError, Context, executor::PrecompileOutput};
use pallet_evm::AddressMapping;
use frame_system::Config as SysConfig;
use frame_system::pallet_prelude::*;

pub struct CallVm<T: pallet_evm::Config> 
{
	_marker: PhantomData<T>,
}

pub trait EvmChainExtension<C: SysConfig> {
	fn call_vm4evm(
			origin: OriginFor<C>,
			data: Vec<u8>,
			target_gas: Option<u64>
		) -> Result<(Vec<u8>, u64),sp_runtime::DispatchError>;
}

impl<T> Precompile for CallVm<T> where
	T: pallet_evm::Config + EvmChainExtension<T>,

	<T as SysConfig>::Origin: From<Option<<T as SysConfig>::AccountId>>,
{
	fn execute(
		input: &[u8],
		target_gas: Option<u64>,
		context: &Context,
	) -> core::result::Result<PrecompileOutput, ExitError> {   //(ExitSucceed, Vec<u8>, u64)
	
		let origin = T::AddressMapping::into_account_id(context.caller);
		
		match T::call_vm4evm(Some(origin).into(), input.iter().cloned().collect(), target_gas) {
			Ok(ret) => Ok(PrecompileOutput{exit_status:ExitSucceed::Returned, cost:ret.1, output:ret.0, logs:Vec::new()}),
			Err(e) => {
				let errstr:&'static str = e.into();
				Err(ExitError::Other(errstr.into()))	 //Err(ExitError::Other("call wasmc execution failed".into())),
			},
		}		
	}
}
