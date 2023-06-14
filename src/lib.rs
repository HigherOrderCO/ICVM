#![feature(try_blocks)]
#![feature(assert_matches)]

pub mod inet;
pub mod term;

#[cfg(test)]
mod tests;

use std::sync::OnceLock;

pub static DEBUG: OnceLock<bool> = OnceLock::new();
