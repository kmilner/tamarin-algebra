//! Native linkage for the Lean solver. The Tamarin adapter owns initialization
//! and interprets the numeric ABI.

unsafe extern "C" {
    /// # Safety
    /// Call exactly once per process, before using the solver.
    pub fn tamarin_lean_initialize() -> u8;
    /// # Safety
    /// Call once on each worker before using Lean on that thread.
    pub fn tamarin_lean_thread_initialize();
    /// # Safety
    /// Call on the initialized worker after releasing its last Lean object.
    pub fn tamarin_lean_thread_finalize();

    /// Compare two finite bags of atoms. The status is 2 for equality, 1 for
    /// inequality and 0 when the query is outside the supported fragment.
    ///
    /// # Safety
    /// Initialize the runtime and this thread first. Both arrays must be
    /// readable for the supplied numbers of elements during the call.
    pub fn tamarin_lean_flat_ac_equal(
        lhs: *const u64,
        lhs_length: usize,
        rhs: *const u64,
        rhs_length: usize,
    ) -> u8;
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
