// Copyright (C) HybirdVM.
// This file is part of HybirdVM.

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

extern crate alloc;

use alloc::{vec, vec::Vec};
use core::marker::PhantomData;
use fp_evm::{ExitError, ExitRevert, ExitSucceed, Precompile, PrecompileFailure};
use fp_evm::{PrecompileHandle, PrecompileOutput, PrecompileResult};
use pallet_evm::AddressMapping;
use precompile_utils::prelude::*;

pub struct CallHybirdVM<T> {
	_marker: PhantomData<T>,
}

impl<T> Precompile for CallHybirdVM<T> where
	T: pallet_evm::Config + EvmHybirdVMExtension<T>,
{
	fn execute(handle: &mut impl PrecompileHandle) -> PrecompileResult {
		let context = handle.context();
		let target_gas = handle.gas_limit();
		let origin = RawOrigin::from(Some(T::AddressMapping::into_account_id(context.caller)));
		
		match T::call_hybird_vm(origin.into(), handle.input(), target_gas) {
			Ok(ret) => Ok(PrecompileOutput{exit_status:ExitSucceed::Returned, cost:ret.1, output:ret.0, logs:Vec::new()}),
			Err(e) => {
				let errstr:&'static str = e.into();
				Err(ExitError::Other(errstr.into()))	 
			},
		}				
	}
}