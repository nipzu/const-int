// TODO remove this
#![allow(incomplete_features)]
#![feature(const_panic)]
#![feature(const_mut_refs)]
#![feature(const_generics)]
#![feature(const_evaluatable_checked)]
#![feature(const_trait_impl)]
#![feature(destructuring_assignment)]
#![feature(result_flattening)]
#![no_std]

#[cfg(not(any(target_pointer_width = "64", target_pointer_width = "32")))]
compile_error!("Only targets with pointers of 32 or 64 bits are currently supported.");

mod uint;
pub use uint::{ConstUint, U1024, U192, U2048, U256, U320, U384, U4096, U448, U512, U8192};

// TODO clippy::pedantic
// also when to use inline(always)
