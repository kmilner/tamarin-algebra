# tamarin-algebra

Lean specifications, executable solvers and proofs for Tamarin’s equational operations. The Cargo package `tamarin-algebra-sys` builds the solver from source and links it into the Rust prover through a numeric C ABI. The Tamarin-specific term conversion lives in `tamarin-term`.

## Build and verify

Native builds currently support x86_64 GNU/Linux. Install Rust, elan, a C toolchain and GNU binutils. Lake uses the toolchain pinned in `lean/lean-toolchain`.

```sh
cargo test --locked
cd lean
lake build TamarinCI TamarinRuntime TamarinProposers
lake env leanchecker --fresh TamarinCI
lake env lean --run Tests/ExportAudit.lean --sources . --unpinned TamarinProposers
```

`cargo build` elaborates the proof root and runs the export audit before it links the runtime, so a runtime whose contract exports lack their theorems, or with an export the manifest lists neither as contract nor as proposer, does not link. Set `TAMARIN_ALGEBRA_SKIP_PROOFS=1` to build only the runtime while experimenting; Cargo then warns that the proofs were not checked. The kernel replay (`leanchecker --fresh`, about four minutes) runs in CI only.

Cargo consumers can pin this repository with a Git dependency. For local solver development, a Cargo patch can select a sibling checkout. The consumer’s lockfile records the selected source.

```sh
# From the tamarin-rs root, with tamarin-algebra checked out alongside it
cargo --config 'patch."https://github.com/kmilner/tamarin-algebra.git".tamarin-algebra-sys.path="../tamarin-algebra"' test -p tamarin-term --features lean-unification --test native_backend
```

The `lean-spec` job checks the nine contract exports against their contracts, requires every other export to be a listed proposer that no contract statement mentions, replays the whole environment in the kernel, audits the compiled modules from outside and exercises mutations of the proof gate. [Solver contracts and coverage](lean/README.md) · [Cargo build](build.rs) · [Review rules](.github/CODEOWNERS)

The import preserves the Lean and C source history from `kmilner/tamarin-rs` through commit `774b0c3`. The source repository’s MIT notice is in [LICENSE](LICENSE). The native Cargo package carries the original Rust package’s GPL-3.0 designation, with the license text in [COPYING](COPYING).
