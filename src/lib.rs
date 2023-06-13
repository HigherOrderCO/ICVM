#![allow(unused_mut)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(unused_variables)]

pub mod inet;
pub mod term;

#[cfg(test)]
mod tests;

use std::sync::OnceLock;

pub static DEBUG: OnceLock<bool> = OnceLock::new();
