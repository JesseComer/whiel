//! Engine-owned generic proposer transport and process supervision.
//!
//! The semantic API remains `proposer_api`; this module owns only its process host.
mod generic_child;
pub mod generic_io;
pub mod generic_process;

#[cfg(test)]
mod generic_io_tests;

#[cfg(test)]
mod generic_process_tests;
