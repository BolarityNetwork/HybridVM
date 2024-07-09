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

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

mod interoperate;

use frame_support::traits::{
	tokens::{fungible::Inspect, ExistenceRequirement},
	Currency, Get,
};
use scale_info::prelude::string::String;
use sp_core::{crypto::AccountId32, Hasher, H256};
use sp_std::collections::btree_map::BTreeMap;
use sp_std::vec::Vec;
use ethereum::TransactionV2 as Transaction;
use self::interoperate::InterCall;

pub use self::pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: frame_system::Config + pallet_contracts::Config + pallet_evm::Config {
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

        type Call: From<Call<Self>>;
		// Currency type for balance storage.
		type Currency: Currency<Self::AccountId> + Inspect<Self::AccountId>;
		
		#[pallet::constant]
		type Enable2EVM: Get<bool>;
		
		#[pallet::constant]
		type Enable2WasmC: Get<bool>;		
	}

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		EVMExecuted(H160),
		WasmCExecuted(T::AccountId),
		HybirdVMCalled(T::AccountId),
	}

	#[pallet::error]
	#[derive(PartialEq)]
	pub enum Error<T> {
		EVMExecuteFailed,
		WasmCExecuteFailed,
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::call_index(0)]
		#[pallet::weight(Weight::from_parts(10_000, 0) + T::DbWeight::get().writes(1))]
		pub fn call_hybird_vm(
			origin: OriginFor<T>,
			transaction: Transaction,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			// Todo 
			Self::deposit_event(Event::HybirdVMCalled(who));
			
			Ok(().into())
		}
	}

	impl<T: Config> Pallet<T>
	{
		pub fn call_wasm4evm(
		    origin: OriginFor<T>,
		    data: Vec<u8>,
		    target_gas: Option<Weight>
	    ) -> Result<(Vec<u8>, Weight)> {
			InterCall::<T>::call_wasm4evm(origin, data, target_gas)
		}

	    pub fn  call_evm4wasm(mut env: Environment<Ext<T>, InitState>)-> Result<RetVal>
		{
			InterCall::<T>::call_evm4wasm(env)
		}
	}
}
