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

impl<T: pallet_evm::Config> Precompile for CallHybirdVM<T>
{
	fn execute(handle: &mut impl PrecompileHandle) -> PrecompileResult {
	}
}