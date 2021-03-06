//! # A crate for dealing with big integers both at compile time and runtime.
//! 🚧 Currently under construction 🚧

// TODO remove this
#![allow(incomplete_features)]
#![feature(const_panic)]
#![feature(const_mut_refs)]
#![feature(const_generics)]
#![feature(const_evaluatable_checked)]
#![feature(const_trait_impl)]
#![feature(destructuring_assignment)]
#![no_std]

#[cfg(not(any(target_pointer_width = "64", target_pointer_width = "32")))]
compile_error!("Only targets with pointers of 32 or 64 bits are currently supported.");

mod uint;
pub use uint::*;

mod error;
pub use error::*;

// TODO clippy::pedantic
// also when to use inline(always)

// TODO this seems pretty important for the crate
// https://github.com/rust-lang/rust/issues/84846
