#![feature(try_blocks)]

pub mod inet;
pub mod term;

#[cfg(test)]
mod tests;

use std::sync::OnceLock;

pub static DEBUG: OnceLock<bool> = OnceLock::new();
pub static FAST_DISPATCH: OnceLock<bool> = OnceLock::new();
