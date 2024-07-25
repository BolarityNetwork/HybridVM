// Copyright (C) HybridVM.
// This file is part of HybridVM.

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

use frame_system::pallet_prelude::*;
use frame_support::traits::fungible::Inspect;
use sp_std::vec::Vec;
use sp_core::H160;

pub trait EvmHybridVMExtension<C: frame_system::Config> {
	fn call_hybrid_vm(
		origin: OriginFor<C>,
		data: Vec<u8>,
		target_gas: Option<u64>,
	) -> Result<(Vec<u8>, u64), sp_runtime::DispatchError>;
}
	
pub trait U256BalanceMapping<T: frame_system::Config> {
	type BalanceOf<T>: Inspect<<T as frame_system::Config>::AccountId>>::Balance;
	fn u256_to_balance(value: U256) -> BalanceOf<T>;
}

pub trait AccountIdMapping<C: frame_system::Config> {
	fn into_address(account_id: C::AccountId) -> H160;
}