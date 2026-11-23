//! Native linkage for the Lean solver. The Tamarin adapter owns initialization
//! and interprets the numeric ABI.
//!
//! Every declaration of the C bridge (`native/lean_unification.c`) is
//! generated from its definition there by `build.rs`: the functions named
//! `tamarin_lean_*` and the structs they exchange. A caller that declares one
//! by hand could disagree with the definition without any diagnostic, so the
//! Rust backend imports them from this crate only. The build also compiles the
//! bridge against the declarations that Lean generated for its exports, so the
//! chain from a Rust call to the Lean function is checked at both joints.
//!
//! # Safety
//! `tamarin_lean_initialize` is called exactly once per process before any
//! other function, and `tamarin_lean_thread_initialize` once on each thread
//! before it uses Lean; `tamarin_lean_thread_finalize` after that thread
//! released its last Lean object. Every pointer and slice must be readable
//! (or writable, for an output) for the supplied number of elements during
//! the call. A returned `*mut c_void` is an owned Lean object that the row
//! readers borrow and `tamarin_lean_match_release` releases.

include!(concat!(env!("OUT_DIR"), "/bridge.rs"));

impl WholeWordSlice {
    /// The slice must outlive every call that receives this value.
    pub fn new(words: &[u64]) -> Self {
        Self {
            data: words.as_ptr(),
            size: words.len(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cargo_links_the_lean_solver() {
        let lhs = [1, 2, 1];
        let rhs = [2, 1, 1];
        // SAFETY: this test owns the process's only initialization. The arrays
        // stay live across the call and the worker releases no objects later.
        unsafe {
            assert_eq!(tamarin_lean_initialize(), 0);
            tamarin_lean_thread_initialize();
            let status =
                tamarin_lean_flat_ac_equal(lhs.as_ptr(), lhs.len(), rhs.as_ptr(), rhs.len());
            tamarin_lean_thread_finalize();
            assert_eq!(status, 2);
        }
    }
}
