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

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

mod interoperate;

use self::interoperate::InterCall;
use ethereum::TransactionV2 as Transaction;
use frame_support::traits::{tokens::fungible::Inspect, Currency, Get};
use frame_support::RuntimeDebugNoBound;
use pallet_contracts::chain_extension::{Environment, Ext, InitState, RetVal};
use sp_core::{H160, U256};
use sp_runtime::{AccountId32, DispatchError};
use sp_std::vec::Vec;
//use sp_std::fmt::Debug;
use hp_system::{AccountId32Mapping, AccountIdMapping, U256BalanceMapping};

pub use self::pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	type Result<T> = sp_std::result::Result<T, DispatchError>;

	#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, Clone, RuntimeDebugNoBound, PartialEq)]
	#[scale_info(skip_type_params(T))]
	pub enum UnifiedAddress<T: Config> {
		WasmVM(T::AccountId),
	}

	#[pallet::config]
	pub trait Config: frame_system::Config + pallet_contracts::Config + pallet_evm::Config {
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		// Currency type for balance storage.
		type Currency: Currency<Self::AccountId> + Inspect<Self::AccountId>;

		type U256BalanceMapping: U256BalanceMapping<Balance = <<Self as pallet_contracts::Config>::Currency as Inspect<Self::AccountId>>::Balance>;

		type AccountIdMapping: AccountIdMapping<Self>;

		type AccountId32Mapping: AccountId32Mapping<Self>;

		#[pallet::constant]
		type EnableCallEVM: Get<bool>;

		#[pallet::constant]
		type EnableCallWasmVM: Get<bool>;

		#[pallet::constant]
		type GasLimit: Get<u64>;

		#[pallet::constant]
		type GasPrice: Get<Option<U256>>;
	}

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	// HybridVM contracts
	#[pallet::storage]
	#[pallet::getter(fn hvm_contracts)]
	pub type HvmContracts<T: Config> =
		StorageMap<_, Twox64Concat, H160, UnifiedAddress<T>, OptionQuery>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		EVMExecuted(H160),
		WasmVMExecuted(T::AccountId),
		HybridVMCalled(T::AccountId),
		RegistContract(H160, UnifiedAddress<T>, T::AccountId),
	}

	#[pallet::error]
	#[derive(PartialEq)]
	pub enum Error<T> {
		EVMExecuteFailed,
		WasmVMExecuteFailed,
		UnifiedAddressError,
		NoWasmVMContract,
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::call_index(0)]
		#[pallet::weight(Weight::from_parts(10_000, 0) + T::DbWeight::get().writes(1))]
		pub fn call_hybrid_vm(
			origin: OriginFor<T>,
			_transaction: Transaction,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			// Todo
			Self::deposit_event(Event::HybridVMCalled(who));

			Ok(().into())
		}

		#[pallet::call_index(1)]
		#[pallet::weight(Weight::from_parts(10_000, 0) + T::DbWeight::get().writes(1))]
		pub fn regist_contract(
			origin: OriginFor<T>,
			unified_address: UnifiedAddress<T>,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			match unified_address.clone() {
				UnifiedAddress::<T>::WasmVM(account) => {
					let value = pallet_contracts::Pallet::<T>::get_storage(account.clone(), vec![]);
					match value {
						Err(t) => {
							if t == pallet_contracts::ContractAccessError::DoesntExist {
								return Err(Error::<T>::NoWasmVMContract.into());
							}
						},
						_ => {},
					}
					let address = T::AccountIdMapping::into_address(account);

					HvmContracts::<T>::insert(address, unified_address.clone());

					Self::deposit_event(Event::RegistContract(address, unified_address, who));
					Ok(().into())
				},
			}
		}
	}

	impl<T: Config> Pallet<T>
	where
		T::AccountId: From<AccountId32> + Into<AccountId32>,
	{
		pub fn call_wasm_vm(
			origin: OriginFor<T>,
			data: Vec<u8>,
			target_gas: Weight,
		) -> Result<(Vec<u8>, Weight)> {
			InterCall::<T>::call_wasm_vm(origin, data, target_gas)
		}

		pub fn call_evm<E: Ext<T = T>>(env: Environment<E, InitState>) -> Result<RetVal> {
			InterCall::<T>::call_evm(env)
		}
	}
}
