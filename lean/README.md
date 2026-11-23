# Verified algebra for Tamarin

This Lake package specifies the algebra operations that Tamarin currently asks Maude to perform.
Rust links selected Lean kernels in-process with the `lean-unification` feature. The goal is to run
the prover with no Maude binary and let developers replace the search algorithms under fixed
correctness and completion contracts. Today, native-only mode completes some full protocol proofs.
The acceptance criterion is mathematical soundness and completeness on the original query under Tamarin’s theory assumptions.
Maude comparisons check compatibility and expose discrepancies. Where a concrete witness proves
Maude missed a variant, native-only must retain that witness. A three-rule regression exercises
both the reachable trace and the false universal lemma. [Theory](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-prover/tests/fixtures/native_ac_marker_trace.spthy) · [Verdict test](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-prover/tests/native_backend.rs)

Native-only batch proofs and the `variants` command fall back to general Lean implementations for all four Maude commands.
Unification and directional matching operate modulo the declared free/C/AC symbols.
Reduction and variants operate on the combined user and builtin equation table. On
a range-restricted canonical presentation, reduction reaches the unique normal form.
Variant generation additionally requires the finite variant property. Both reference
drivers retry unfinished stages while the budget and result fit the numeric interface.
[Active-table reference](Tamarin/CompleteNarrowing.lean) · [Export contracts](TamarinCI.lean)

## Run the experimental backend

The native link supports host builds on x86_64 GNU Linux. Use elan/Lake, a C toolchain and GNU `ar`,
`nm` and `objcopy`. The package pins the Lean version. [Toolchain](lean-toolchain)

From the tamarin-rs repository root, build and run a proof that needs a witness shared across two substitution
images.

```sh
cargo build --release --features lean-unification
target/release/tamarin-rs --algebra-backend=native-only --prove crates/tamarin-prover/tests/fixtures/native_shared_offset.spthy
```

Set `TAM_RS_NATIVE_REFERENCE=1` with `--algebra-backend=native-only` to route ordinary
unification, matching, reduction and variants directly to their references. This setting
also applies to derived first-match and existence queries. A protocol regression combines
user-defined AC, subterm and ground-result equations, pairing and DH exponent cancellation.
[Theory](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-prover/tests/fixtures/native_mixed_subterms.spthy)

Rust callers can also invoke the four references without a session through
`unify_modulo_attributes`, `match_modulo_attributes`, `reduction_for_convergent_theory`
and `variants_for_convergent_theory`. The matcher takes the pattern on the left,
the subject on the right and an explicit predicate selecting bindable pattern variables.
[Rust API](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-term/src/lean_unification.rs)

| Backend | Behavior |
| --- | --- |
| `maude` | Default without the feature. Uses the existing Rust fast paths and starts Maude. |
| `hybrid` | Default with the feature. Uses supported Lean operations and delegates other queries to Maude. |
| `native-only` | Supports library, batch and variants requests. Skips all Maude discovery and subprocesses. Unsupported queries and native failures produce errors. Interactive mode and the installation self-test currently reject this setting. |

A native-only failure is shared across session handles. Batch checks the session before publishing
output. Library callers that recover from algebra errors must likewise call
`MaudeHandle::check_backend_status` before using their results. Native-only requires
`TAM_RS_NO_LEAN_UNIFY`, `TAM_RS_VERIFY_LEAN_UNIFY` and `TAM_RS_VERIFY_REDUCE_NF` to be unset.
[Backend selection](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-term/src/algebra_backend.rs) ·
[No-Maude CLI tests](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-prover/tests/native_backend.rs)

## What an implementation must prove

The acceptance target is `MaudeOperations.Reference sig rules` for the module Tamarin emits.
The upstream Haskell and Rust adapters issue the same four algebra commands. Installation probes
and module initialization are separate. Rules and enabled builtins determine the active theory,
including DH, bilinear pairing, multiset, natural numbers, XOR and user-declared free or AC symbols.
[Whole-module contract](Tamarin/MaudeOperations.lean) · [Reference assembly](Tamarin/FoldingNarrowing.lean#L161) · [Upstream command builders](https://github.com/tamarin-prover/tamarin-prover/blob/573a43953195d83e62fdbe32fc98253031bca60f/lib/term/src/Term/Maude/Process.hs#L194) · [Rust adapter](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-term/src/maude_proc.rs) · [Module printer](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-term/src/maude_print.rs#L344) · [Active equations](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-term/src/maude_sig.rs#L285) · [Upstream signature](https://github.com/tamarin-prover/tamarin-prover/blob/573a43953195d83e62fdbe32fc98253031bca60f/lib/term/src/Term/Maude/Signature.hs#L187)

The basis B consists of the declared free, binary commutative (C) and associative-commutative (AC)
symbols. Pure AC preserves multiplicities and has no unit. The command domain includes arity-correct
applications at Maude's kind level. A ground natural-number sum containing a public name can match
itself modulo AC even though it has no Tamarin sort. A `Msg` variable cannot bind to that sum.
[Algebra](Tamarin/Algebra.lean) · [Lean regression proofs](Tests/MaudeOperations.lean) · [Maude 3.5.1 regression queries](Tests/check_maude_operations.py)

| Command | Required answer | Lean and Maude 3.5.1 sources |
| --- | --- | --- |
| `unify` | A finite family of sort-respecting substitutions that solve the whole conjunction modulo B. Every solution, including a nonground one, factors through one answer using one substitution on all query variables. A complete empty family proves impossibility. | [Unification](Tamarin/Unification.lean) · [Whole-problem contract](Tamarin/WholeContract.lean) · [Maude unification](https://github.com/maude-lang/Maude/blob/7269fc720072a2cd8b7222736721ba26dd3752b2/src/Mixfix/unify.cc) |
| `match` | All assignments to the bindable pattern variables, up to B on their images. The subject and any pattern variables frozen by the caller stay rigid. A Boolean query asks whether an assignment exists. | [Matching](Tamarin/Matching.lean) · [Maude pattern and subject search](https://github.com/maude-lang/Maude/blob/7269fc720072a2cd8b7222736721ba26dd3752b2/src/Mixfix/match.cc#L42-L127) |
| `reduce` | A reachable, irreducible result for the input, including open terms, using the active rewrite equations modulo B. On a convergent, sort-preserving presentation, all normal forms agree modulo B. | [Rewriting](Tamarin/Rewriting.lean) · [Maude reduction](https://github.com/maude-lang/Maude/blob/7269fc720072a2cd8b7222736721ba26dd3752b2/src/Mixfix/execute.cc#L245-L269) |
| `get variants` | A finite covering family of normalized substitutions and values. A single further substitution explains every binding and position in a packed query modulo B, without another reduction. Rust retains the bindings and must be able to recover the values by substituting and reducing. | [Reconstruction](Tamarin/VariantReconstruction.lean) · [Packed rule queries](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-theory/src/tools/rule_variants.rs#L125) · [Rust reply parser](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-term/src/maude_parse.rs#L218-L250) · [Maude initialization](https://github.com/maude-lang/Maude/blob/7269fc720072a2cd8b7222736721ba26dd3752b2/src/Higher/variantSearch.cc#L215-L295) · [Printed rows and incomplete search](https://github.com/maude-lang/Maude/blob/7269fc720072a2cd8b7222736721ba26dd3752b2/src/Mixfix/getVariants.cc#L119-L174) |

Maude reduces the initial variant and narrows with executable equations marked `[variant]`.
Tamarin marks every emitted equation this way, so reduction and variants share one table.
Core Maude additionally requires explicit coherence modulo the axioms for variant narrowing.
Tamarin emits the active rules directly. Some builtin tables include AC extension equations.
User tables receive no general coherence completion in the printer. With the bare rule
`plus(f(Z),a) = g(Z)`, Maude 3.5.1 reduces inside a larger AC product and omits the
`X = a` variant of `plus(f(c),b,X)`. Adding the explicit remainder to both sides recovers it.
The Lean contract requires this solution. Lean proves that adding the remainder rule preserves
every contextual rewrite and the full variant contract. It also exposes every such rewrite at
the whole root of a well-sorted AC product. Comparisons with Maude variant enumeration assume coherence of the actual emitted table.
[Conservative equation extensions](Tamarin/ACEquationExtensions.lean) · [Maude’s explicit coherence requirement](https://maude.lcc.uma.es/maude31-manual-html/maude-manualch21.html) · [Pinned Maude probe](Tests/check_maude_operations.py) · [Active tables](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-term/src/maude_sig.rs#L285) · [Equation emission](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-term/src/maude_print.rs#L511)

Tamarin uses plain `get variants`, which permits redundant answers. Tamarin requires convergent user theories with the
finite variant property and leaves these conditions unchecked. The total reference must establish
completion on its full domain. A bounded export must establish completion on its advertised domain
and distinguish exhaustion, interruption and unsupported input from a complete answer.
[Maude narrowing equation selection](https://github.com/maude-lang/Maude/blob/7269fc720072a2cd8b7222736721ba26dd3752b2/src/Higher/variantNarrowingSearchState.cc#L150-L175) · [Equation printer](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-term/src/maude_print.rs#L511-L523) · [Tamarin's theory assumptions](https://github.com/tamarin-prover/tamarin-prover/blob/573a43953195d83e62fdbe32fc98253031bca60f/manual/src/004_cryptographic-messages.md#L129-L143)

### The contract and the gate

The exports fall into two classes, listed in [`ExportManifest.txt`](ExportManifest.txt).

**Contract exports** are the eighteen whose reply the Rust backend uses as the answer. Each is
mentioned by theorems of the proof root [`TamarinCI.lean`](TamarinCI.lean), and those theorems
are the whole of what is promised to a caller.

| Export | What a reply means | Where it may decline |
| --- | --- | --- |
| `tamarin_total_unify` | The reply decodes to a complete, sound, domain-restricted family of unifiers of the decoded query, also in every extension of the caller's signature (`exportedTotalUnify_correct`, `_ambient`). | `#[#[0]]` on a malformed packet, or when one answer of the family adds at least `2^64 - bound` distinct variables to the query, `bound` being the least identifier above the query's variables (`TotalUnifyWire.Packet.Overflows`): the unifier names the variables it adds by consecutive identifiers from that bound (`UnifierDensity.verified_dense`). Never on a query without solutions (`_unsatisfiable`). `#[#[4]]` exactly when the caller's `poll` says stop (`_interrupted`). |
| `tamarin_total_unify_exists` | 1 exactly when the decoded query has a unifier and 2 exactly when it has none, also in every signature extension (`exportedTotalUnifyExists_correct`, `_ambient`). No family is listed where the residuals of free factoring and of the alignments of commutative roots are sums of variables at one AC head, all of the sort of that head: a positive solution of the linear system decides. Other queries are decided by listing. | Malformed packets (reply 0). 4 exactly when the caller's `poll` says stop (`_interrupted`). |
| `tamarin_name_unifiers` | Tables that name the variables a family of unifiers adds to its query. The caller reads the reply of `tamarin_total_unify` through them and in no other way; the reading is specified (`UnifierNames.apply`). A reply that decodes to a family and can be read through the tables reads as that family, or as its members without a variable of the sort of natural numbers, up to an injective renaming of the range of each member, and no name of the range is the name of a query variable of its sort (`exportedNameUnifiers_correct`). With `tamarin_total_unify`'s own reply the reading is a complete family of unifiers (`_total`), and for a module without natural numbers it decides every solution without such a variable (`_natFree`). Without a proposal every name has the hint 0 and an index of no query variable, above every index of the query unless the caller set `low`. The export sees the labels of the query variables and what the caller says the range variables are, never the reply, and the statement assumes nothing about what it is told. | **No limit**: `#[#[0]]` may be the reply to any call. It is the reply when two query variables of one sort have one label, and when no index is left above the query and `low` is not set. A proposal that fails the test of the tables is replaced by the default names. |
| `tamarin_unpack_conjunction` | The rows are the conjunction the packed command denotes, or the clash header (`exportedUnpackConjunction_correct`). | Malformed packets only. |
| `tamarin_total_match`, `tamarin_total_match_exists` | The complete set of scoped matches, and 1 or 2 exactly as one exists, also in every signature extension. | Malformed packets only. |
| `tamarin_certify_table` | `true`: the packet decodes and its table is range restricted, a canonical presentation and has the finite variant property over all ambient names (`exportedCertifyTable_sound`). | `false` is the reply to a malformed packet. It is never the reply to a decoded table of constructor-pattern rules whose results are subterms or constants (`exportedCertifyTable_subterm`, class `SubtermTable.Presentation`, below), nor to three concrete packets (`exportedPhysicalXorTable_admitted`, `exportedPhysicalJointGroupTable_admitted`, `exportedPhysicalBilinearTable_admitted`). On any other table it carries no information. |
| `tamarin_session_reduce` | On a table `certify_table` accepted: the unique normal form of the term (`exportedSessionReduce_certified`). | `#[#[3]]` only while some rewrite path from the term has at least `n` steps (`exportedSessionReduce_complete`, stated with `CheckedReduction.Within`). `#[#[4]]` exactly when the caller's `poll` says stop (`_interrupted`). |
| `tamarin_path_reduce` | Status 1: an irreducible reduct that keeps the sorts of the input, on any table. Not known to be unique. | 2 only if the table is not range restricted or an irreducible reduct lost a sort, 3 only while a rewrite path has at least `n` steps (`exportedPathReduce_correct`). `#[#[4]]` exactly when the caller's `poll` says stop (`_interrupted`). |
| `tamarin_theory_*` (eight) | The export above on the packet of the theory of a Tamarin file (`Tamarin.Theory`, below): `theory_unify`, `theory_unify_exists`, `theory_match`, `theory_match_exists`, `theory_certify`, `theory_path_reduce`, `theory_reduce`, `theory_variant_check`, with the counterparts of its theorems stated over `Theory.Signature` and `Theory.Table` (`theoryUnify_correct`, …). A reduction or variant-check call takes its certificate as `theoryCertify … = true` on the same table arguments (`theoryReduce_certified`, `theoryVariantCheck_certified`, …). | As the export above, and `#[#[0]]`, 0 or `false` for arguments that are not those of a valid signature (`_foreign`). `theory_certify` is never `false` on a valid combination of builtins without user symbols or rules, at any budget (`theoryCertify_builtin`). |
| `tamarin_session_variant_check` | Status 1 on a canonical presentation: the proposed family is closed, hence a complete set of variants with exactly the proposed substitutions (`exportedSessionVariantCheck_correct`, `_certified`). A rejection names the clause of closedness that fails (`_decides`). | Status 3 only if a term the check has to normalize (`VariantCertificate.Demand`: a term of the query, its instance by a member, or a value of a most general narrowing successor of a member) has a rewrite path at least as long as the depth, or the work limit is nonzero and below the positions of the narrowing layers (`VariantCertificate.Overcharged`); see `_decides`, `_complete` and `variantDemand_bounded`. `#[#[4]]` exactly when the caller's `poll` says stop (`_interrupted`). |

No contract statement names a search, a classifier or a reference procedure. A decline is limited
either by a condition on the decoded packet and the rewrite relation, or by a concrete packet, or
by the caller's `poll`. The one reply that is not limited everywhere is `false` of `certify_table`
outside its class and its three packets: termination, confluence and the finite variant property
are undecidable. There coverage is guarded by the corpus and the benchmarks.

The class of `exportedCertifyTable_subterm` is stated on the decoded table alone
([`Tamarin/SubtermTable.lean`](Tamarin/SubtermTable.lean)):

- every left side is a free application whose arguments contain no operator that heads a left
  side (constructor patterns, with free, C and AC constructors, names and repeated variables);
- the rules of one head either all return the subterm at one common position below the root of
  their left side, or all return one closed term that contains no head of a left side and has
  fewer symbols than the left side;
- every result has the sort of the root of its left side.

These are the equations of pairing, symmetric and asymmetric encryption, signatures (`verify`
returning `true`), revealing signatures, and user equations of the same shape. Not in the class:
a left side with a defined operator below its root (`f(g(x))` where `g` has an equation), a result
that is neither a subterm nor a closed constructor term, a constant result that is not smaller
than its left side (`f(x) = c`), a C or AC operator at the root of a left side, and every table
with an equation of Diffie-Hellman, XOR, bilinear pairing, multisets or natural numbers. The
certifier accepts many such tables (the three packets, user AC units, defined calls in results),
and nothing in the contract makes it.

**Interruption.** The ten exports whose searches can run for a time or allocate memory exponential
in the width of an AC product (`total_unify`, `total_unify_exists`, `session_reduce`,
`path_reduce`, `session_variant_check` and their `theory_*` counterparts) take a first argument `poll : Unit → Bool`. Every statement about their answers has
the hypothesis `poll () = false` and is otherwise the statement it was, and the reply is the
interrupted status exactly when `poll () = true`. The searches receive `poll` as an instance
argument `[Interrupt]` and wrap their loops in combinators that are, as definitions, the plain
computation (`Interrupt.guard d x` is `x ()`, `Interrupt.map f xs` is `xs.map f`) and are compiled,
through a proved `@[csimp]` equation, to code that asks `poll` first and returns a default when
told to stop. A proof never sees the question. All instances are equal, so the library's theorems,
which are stated for the default instance, hold for the instance an export builds. A search that
is given no instance (the matchers, the certifier, every proposer but the folding one) runs as
before and is compiled without the questions. The variant checker hands its instance to every unification,
matching and reduction it runs, and asks itself before every member, every narrowing successor
and every choice of a product. [Combinators and proofs](Tamarin/Interrupt.lean)

Inside Lean the stopping branch is dead: a function on `Unit` has one value. It exists for the C
bridge, whose `poll` is a closure that starts to reply `true` when the Rust caller's request is
cancelled or the call has asked more questions than its work bound, and keeps replying `true`.
Two things are trusted about it, both in [`native/lean_unification.c`](../native/lean_unification.c):

- the bridge hands a reply to its caller only if the closure replied `false` to every question of
  that call, and otherwise releases the reply unread and reports the reason;
- a run in which the closure replied `false` every time is a run of the compiled export with the
  constant function, which is what the theorems describe. This needs nothing of the compiler
  beyond what every export already needs, since the compiled code can observe the closure only by
  calling it.

What an interrupted search computes is therefore irrelevant. The export's own reply `#[#[4]]` is
produced only when the very first question is answered `true`.

**Proposer exports** are the other 43 (`proposer` lines of the manifest): the pieces of the
specialised variant solvers that still run in Lean, the folding variant generator
`tamarin_general_variants`, the bounded narrowing search `tamarin_checked_variants` (the proposer
for kind-level queries and for tables the certifier did not accept), and `tamarin_fold_variants`,
the proposer for a sorted query that no specialised solver covers. The latter runs folding variant narrowing in the order of Maude's
`VariantSearch` and `VariantFolder` on the narrowing layer and the subsumption test of the
certificate checker: a successor that is an instance of a retained variant is dropped, a
successor that is kept evicts the retained variants it subsumes other than its ancestors, and a
layer is listed when it is complete ([`Tamarin/VariantFold.lean`](Tamarin/VariantFold.lean)).
`tamarin_apply_names` is the specified reading of a reply through the tables of
`tamarin_name_unifiers`, as a function the Rust tests compare the backend's reader with;
production does not call it.
A call stops with status 3 beyond a given number of narrowing sites, and the caller retries with a
larger number. It takes a `poll` like the interruptible contract exports, so a call also stops
when the caller cancels. They carry no contract. The Rust backend
assembles their output into a proposed family of variants and uses that family only after
`tamarin_session_variant_check` accepted it; a rejected or undecided family fails the session.
A wrong proposal, including a wrong pruning decision inside the proposer, therefore costs a
rejection and never a wrong answer, which is why nothing has to be promised about a proposer.
It follows that a proposer's output must never reach the prover without that check. The Rust
backend has one place where a family of variants is returned (`MaudeHandle::variants`). It
passes every family through the checker, without exception.

### The theory of a Tamarin file

[`Tamarin/Theory.lean`](Tamarin/Theory.lean) fixes the signature and the builtin rewrite rules in
the specification instead of taking them from the caller. A `Theory.Signature` is what the theory
file says: the five equational builtins (`dh`, `xor`, `bp`, `mset`, `nat`; `bp` needs `dh`), the
arities of the other free symbols (user functions and the symbols of the rule-carrying builtins
such as pairing and encryption, whose equations are user rules) and the number of user AC symbols.
The builtins have fixed ids (free `exp 0, inv 1, one 2, DH_neutral 3, zero 4, pmult 5, tone 6`; AC
`mult 0, xor 1, union 2, tplus 3`; C `em 0`), user symbol `i` has id `16 + i`, and every symbol has
sort msg except `tplus : nat nat → nat` and `tone : → nat`. `Signature.symbols` lists them and
`theorySignature_decodes` proves that the declaration words decode to exactly that list. The rules
of DH (13), XOR (3) and bilinear pairing (3) are written as terms there; multisets and natural
numbers have none. A `Theory.Table` adds the user rules as node rows indexed from 0, and
`Table.packet` places the builtin rule rows first and the user rows after them.
`theoryTable_rules` reads the decoded rules back without the rows: they are the builtin rules
as terms of the decoded signature (`Term.denote`, `Signature.builtinEquations`) followed by the
rules of the user's block decoded by itself; `theoryTable_builtin` states that a builtin-only
table decodes to exactly its builtin rules and is certified. The terms of a
call on a table arrive as rows numbered from 0 that may name only each other. Since a session call
receives the same table arguments as `theory_certify`, the identity of the certified table and the
table of the call is no longer an obligation of the caller.

The theorems about proposers that were contract statements are kept, unpinned and without an
owner, in [`TamarinProposers.lean`](TamarinProposers.lean), together with the coverage statements
that were stated through reference procedures and the library facts that mention no export. CI
builds that module so the proofs stay alive. Nothing in it is promised to a caller: a theorem
there can be weakened or deleted without review.

**For an optimization**, change any implementation module. A standalone audit reads the compiled
modules without importing them into its own elaboration. It fails unless:

- every export is listed in the manifest exactly once, as `export` or as `proposer`;
- every contract export has a theorem of the proof root, and the kernel statement of every
  public theorem of the proof root is the recorded one (SHA-256 of a canonical encoding);
- every definition those statements depend on, in whatever module it is defined, is the one
  recorded in [`SpecManifest.txt`](SpecManifest.txt) (422 constants: terms, signatures,
  substitutions, the rewrite relation, the reply specifications and the wire decoders);
- no theorem of the proof root mentions a proposer, and no proposer is in that closure;
- no module, proposer code included, defines macros, syntax, elaborators or initializers, imports
  `Lean`, replaces compiled code (`implemented_by`, `extern`, unsafe, or partial or opaque code
  behind an export) or uses an unapproved axiom. Proposer code runs in the caller's process, so
  it has to stay ordinary, memory-safe Lean even though its results are not trusted.

CI replays the whole environment of the proof root in the kernel. Cargo builds run the proof
root and the audit unless `TAMARIN_ALGEBRA_SKIP_PROOFS=1` is set for an unproved experiment.

The foreign interface is checked at both joints by the Cargo build. The C bridge
([`native/lean_unification.c`](../native/lean_unification.c)) is compiled against the
declarations Lean generated for its exports. The Rust declarations of the bridge's functions and
structs, and of the five Lean exports that take machine words only and need no bridge function,
are generated from the bridge's source and from those declarations
([`build.rs`](../build.rs), [`src/lib.rs`](../src/lib.rs)). The Rust backend declares none by
hand, and a test of `tamarin-term` fails on an `extern "C"` block in its sources. A call that
disagrees with the bridge in the number or type of an argument or in the result does not compile.

A definition that a contract statement depends on (a wire decoder, a semantic predicate) cannot
be changed in place: the audit fails until an owner regenerates the record. Add a faster copy,
prove it equal (a `@[csimp]` equality needs no other change) and leave the original. Everything
else can be changed in place, including the unifier, the matcher, the table classifier, the
reducers and every proposer: no statement reaches them. The `contractTyped` list of the audit,
which used to exempt the verified unifier, is empty for that reason.

What the tightening gave up, relative to the previous contract:

- `certify_table` no longer has to accept what the reference classifier `CertifiedTable.admits`
  accepts. No semantic statement can replace that clause in full: termination, confluence and
  the finite variant property are undecidable, Maude does not check them and Tamarin assumes
  them. It has to accept the class of `exportedCertifyTable_subterm` and three packets.
- `checked_reduce` is no export. It followed every rewrite path and declined by a resource
  policy with no counterpart in the rewrite relation (a factorial charge per AC head against a
  fixed work limit), so its decline could not be limited. A session reduces along one path:
  `session_reduce` on a table the certifier accepted, `path_reduce` on any other, whose replies
  are all specified. What the caller loses: on a table the certifier did not accept, a reduct is
  proved irreducible and sort preserving but not unique, so the Rust backend counts every such
  reduction as assumed (it counted those the all-paths check settled as proved), and a raw
  session, which follows no path, reports the uncertified table. Proofs are unaffected: same
  verdicts and step counts. The procedure `CheckedReductionWire.run` and what was proved of it
  (its two floors included) stay in the library and in `TamarinProposers.lean`.
- `general_variants` is a proposer. Measured on the whole corpus, all 10,282 families of
  variants reached the prover through a Rust proposer and the checker and none through this
  export. The caller loses its two statements (`exportedGeneralVariants_malformed`, `_sound`):
  a folding family is used only if the checker accepts it, and one the checker does not decide
  fails the session where it used to count as assumed. The statements are still proved in
  `TamarinProposers.lean`, with the clauses that forced a reply when the reference search
  `GeneralVariants.run` finishes and the corollaries for DH, constructor and subterm tables.
- `checked_variants` is a proposer. It was kept as a contract export only for kind-level
  queries, on which the checker was exponential; it no longer is. Its family goes through the
  checker like every other, so the caller loses its two statements
  (`exportedCheckedVariants_malformed`, `_sound`, still proved in `TamarinProposers.lean`) and
  a family the checker does not accept fails the session.
- `general_reduce` is no export. It followed every rewrite path to the given depth and listed
  every match of every rule at every step, so one call on a wide AC product allocated without
  limit (4.8 GB in 15 s on one test query) and nothing in its contract let a caller prevent
  that. Production never called it. The caller loses the only all-paths reducer whose declines
  were specified (`exportedGeneralReduce_correct`: 2 only on a conflict, 3 only while a path
  within the depth is unsettled). The reference procedure `GeneralReductionWire.run` and its
  specification stay in the library.

Known weak clauses:

- Total unification. `tamarin_total_unify` may reply with the decline word `#[#[0]]` on a
  decodable query when some complete family has a variable identity or an arity outside 64 bits
  (`TotalUnifyWire.Packet.Correct.valid`). The clause names no search, so it only asks for a proof
  that such a family exists, and one exists for most solvable queries. Missing is a bound on the
  fresh identities of the installed unifier. With it `valid` becomes
  `(∃ answers, Decodes p (kernel ds ns es) answers ∧ (Outcome.complete answers).CorrectIn p []) ∨
  (kernel ds ns es = #[#[0]] ∧ ¬ Headroom p)`, where `Headroom p` speaks about the decoded
  identities only. This is the counterpart of Maude refusing a query whose variable names
  collide with its fresh ones (`unsafe variable name`, `src/Higher/unificationProblem.cc`).
  Until then the caller treats the decline word as a hard error, never as "no unifier", and
  `exportedTotalUnify_unsatisfiable` rules it out for queries without solutions.
- Variant certificates: what limits status 3. The clause is exact in one direction
  (`Decision.exhausts`): a reply with status 3 at depth `n` and work limit `w` implies that some
  term in `VariantCertificate.Demand` has a rewrite path of at least `n` steps (stated with
  `CheckedReduction.Within`, as for `session_reduce`), or that `w` is nonzero and below
  `Charge`, the number of positions that are not variables in the normal forms of the
  instantiated query, added up over the members (slots whose query term is a variable do not
  count). `Demand` is defined through the rewrite relation and subsumption modulo the declared
  laws alone. It holds the terms of the query, their instances by the members, and the values
  of the *most general narrowing successors* of the members. A successor of a member is an
  instance of it that keeps its images normal and takes one rewrite step in one value (the
  premise of `Folds`); it is most general when every successor of which it is an instance is an
  instance of it. No unifier, narrower or reducer is named, so an implementation is free in how
  it enumerates successors. `variantDemand_bounded` proves that the clause is not empty: on a
  range-restricted canonical presentation one depth bounds every rewrite path from every term
  of `Demand`. What the clause does not capture:
  - It is not an equivalence. The checker follows one rewrite path per term, so it can answer at
    a depth below the longest path of a term it normalizes, and it need not normalize a
    successor that is an instance of another one.
  - The depth is compared with the longest rewrite path, not with the shortest one or with the
    path a particular reducer takes, so the depth that `variantDemand_bounded` provides for a
    family can be above the depth at which the checker in fact answers. No bound is computed
    from the packet: 65536 suffices on the whole corpus.
  - To meet the clause the checker rereads the layer of a member whose scan the depth ended, and
    passes over a successor it could not normalize when that successor is an instance of one it
    normalized and found subsumed. This costs nothing unless the depth is exhausted.
  - Nothing bounds the time or the memory of a call. The work limit charges positions, not the
    cost of the unifications at a position, which can be exponential (below). The caller's
    `poll` and a bound on its questions stop such a call.
- Kind-level products in the variant checker. The narrowing layer set aside every sub-product
  of an AC product that holds a factor outside the sort of its operator: 2^k views of `k`
  factors (20 factors 5.4 s and 1.43 GB). It now sets aside sub-products of the factors outside
  the sort only (`ACSplits.asides`), so the number of views is 2^u in the number `u` of those
  factors and independent of the width: the identity family on 129 public names and one Node
  variable checks in milliseconds (Rust test `kind_level_product_check_is_not_exponential`). A
  product of many factors outside the sort is still exponential in their number. No well-sorted
  theory produces one, and such a call is stopped by `poll` like any other.
- Repeated variables in products. The check of a family whose members hold products with
  repeated variables can take far longer than Maude takes to list the family, and need not
  finish: `mult('c',x,x,x)` over Diffie-Hellman exponents, 8 variants, takes about 5 s in the
  checker where Maude lists the family in 0.3 s, and the 247 variants of
  `LIST(x*y, x*inv(y))` are not checked within 900 s (7.7 GB). By stack samples of the first,
  60% of the checker's time is in the unifier (a product with repeated factors against the
  extended left sides of the rules) and 38% in the normality tests of the unifiers it returns. The unifier was not changed. Such a call is now interruptible: it
  returns within 0.1 s of a cancellation, and the Rust backend stops it after 2^26 questions.
- Reduction on a table `certify_table` did not accept. `tamarin_path_reduce` answers, with
  every reply specified, and claims no uniqueness, so the Rust backend counts its answers as
  assumed. Every family of variants on such a table is assumed as well.
- Running time. No statement bounds the time of a call. AC matching and unification are
  exponential in the worst case. `tamarin_path_reduce` and `tamarin_session_reduce` look for
  the first match of a rule, and that search can be exponential in the width of an AC product:
  `select(pair(f0+…+f63, hash(x)), other)` against a rule whose left side has a product of three
  variables gives no answer in 120 s, at a flat 15 MB. The depth argument bounds rewrite steps,
  not the search for one step. These two exports and the two unification exports can be
  interrupted (see Interruption above): the caller's cancellation and a bound on the number of
  questions one call may ask stop them. Measured on the runaway queries of the fuzzing
  campaign: the reducer returns 0.2 ms after the request and the unifier 54 ms after a
  request made at 0.3 s; a later request takes as long as releasing what the unifier had
  built takes (0.4 s for 0.8 GB). The questions are asked where those searches spend their
  time: the first-match search of the bag matcher, the selection of basis solutions and the
  construction of their answers in the homogeneous solver, the frontier and the children of a
  component search and the partition fallback. Nothing proves that every long loop asks.
  The variant checker is interruptible as well: it hands `poll` to every unification, matching
  and reduction it runs and asks before every member and every narrowing successor.
  So is the folding proposer `tamarin_fold_variants`, which takes a `poll` as well.
  Still uninterruptible: `total_match` and `total_match_exists` (a fuzzing run found a
  scoped match that ignores its cancellation), `certify_table` and every other proposer.

The repository includes a GitHub ruleset for the default branch. Importing it in Settings →
Rules → Rulesets requires the GitHub Actions `lean-spec` check and code-owner approval for
changes to the contract, its two records, the audit, the ABI and their build configuration. Every
other file has no owner and can be changed under the gate alone; the ownership file says what the
gate does and does not enforce for them. GitHub reads CODEOWNERS from the base branch.
Install the workflow and ownership file when activating the ruleset. [Ruleset](../.github/rulesets/lean-spec.json) ·
[Ownership](../.github/CODEOWNERS) · [Mutation tests](Tests/check_audit.py)

## What crosses the Rust–Lean boundary

This section describes the packets of every export, contract and proposer alike. The exports
of the bounded solvers it describes (flat and sorted AC matching, operand and residual steps,
factor checks, cancellation and DH image tables) are proposers now: the Rust backend calls them
only while assembling a family of variants for `tamarin_session_variant_check`. Ordinary
unification and matching go to `tamarin_unpack_conjunction`, `tamarin_total_unify`,
`tamarin_total_unify_exists`, `tamarin_total_match` and `tamarin_total_match_exists` alone.

For native-only ordinary unification, Rust first submits the original conjunction.
It sends declarations for the symbols used in the query, a shared graph of numeric term rows, and
pairs of equation roots. A separate Lean kernel decodes Maude’s free TOP list wrappers for
both unification and directional matching. Equal shapes produce one conjunction over the
corresponding algebraic coordinates, including nested packs and repeated variables.
Unequal widths or a wrapper opposite an algebraic leaf give an empty answer family.
Tamarin’s variable sorts are all strictly below TOP, so a wrapper cannot be a variable
image. Every algebraic leaf must still belong to the module. The packet supports wrappers
at command coordinates; the general kernel can decline synthetic Rust terms with a wrapper
beneath an algebraic operator. [Packed command contract](Tamarin/PackedConjunction.lean)

One AC row holds references to all its children, including repeated occurrences. Lean checks arities, child sorts and backward references. The graph export decides
identity and closed clashes. For homogeneous AC queries, Lean counts occurrences in those same
equation roots and returns witness slots per variable per answer. Every reference to a shared
child contributes its full multiplicity. For residual worklist equations, Rust sends the column ID
of each operand occurrence and retains the corresponding terms locally. Lean validates and counts
the IDs. Rust reconciles every returned arm with the original operands and pending equations
before reporting a complete result.
The reference switch sends these roots directly to the total export. The default native-only
path tries the bounded solvers first and sends the original roots when they defer.
Hybrid also uses it for existence queries. Ordered hybrid enumeration retains Maude as its
fallback. The total export accepts arity-correct kind-level trees. It returns one numeric
row per input variable per answer, with term constructors in postfix order. Lean proves
that the family covers substitutions containing additional symbols from the caller’s
signature. The exhaustive search can be expensive for large answer families.
[Packet contract](Tamarin/TotalUnifyPacket.lean) · [Signature extension](Tamarin/SignatureExtension.lean) · [Rust reader](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-term/src/lean_unification/whole/total.rs)

**Names of the range.** The variables in the range of an answer are numbered by the
unifier in the space of request rows, and the caller reads the range of an answer as fresh:
none of its variables may be one the caller holds. Rust decides nothing about them. It
sends `tamarin_name_unifiers` the label of every query variable (the identifier of its name
hint, and its index), the identifier and sort words of the query variables as the rows of an
arm list them, and for each arm the range variables in the order of first occurrence. The
reply holds a table for each arm that is kept, with a target for each range variable: a
label, or a row of the arm. Rust reads the reply of the unifier through the tables, as
`UnifierNames.apply` specifies: a variable token is the variable its label names, and a row
that binds a query variable to a variable whose target is that row is left out, so the
variable stays unbound. A variable without a target, a row target anywhere else, an arm that
lists other query variables than the tables do, or an arm without a table that has no
variable of the sort of natural numbers in a module with that sort has no reading, and is
an error. The reading is therefore safe whatever Rust told the export about the range.

By default a range variable gets the hint 0, which Rust spells `x`, and the least indices
the query does not use, moved up together so that the first is the least index above the
query. That is the numbering of the Maude reply decoder and keeps a range variable apart
from every variable the caller keeps below that bound. Rust can instead propose a label for
every range variable; it proposes the names the Maude backend composes, which carry the
name hints of query variables. The export takes a proposal when no two variables of an arm
get one target at one sort, where the label of a query variable of that sort means that
variable's row; otherwise the whole family gets the default names. Arms with a variable of
the sort of natural numbers get no table when the caller's module lacks that sort
([Sort restriction](Tamarin/UnavailableSort.lean)).
[Tables, reading and proof](Tamarin/UnifierNames.lean) · [Renaming preserves a complete family](Tamarin/CallerFreshening.lean) · [Packet tests](Tests/UnifierNames.lean)

The general matcher adds the IDs of bindable pattern variables to the same packet. It
returns literal subject-variable IDs on the right side of a binding. For reduction and
variants, Rust sends the ordered observation roots and both roots of every active equation.
The table packet declares the whole module's operators. The variant proof admits arbitrary
additional caller names of each sort; each returned image must use names Rust can recover.
The default checked variant fallback attempts four narrowing layers, charging the rule table, positions,
and AC choices before expansion. Both table fallbacks check preservation of declared sorts. It checks every pair of overlapping terminal rows,
including a row paired with an independently renamed copy of itself. A stopped search
returns status 2. A malformed packet has a separate failure status.
[Matching export](Tamarin/TotalMatchWire.lean) · [Table input](Tamarin/TableWire.lean) ·
[Variant packing and name scope](Tamarin/TableAmbient.lean)

For an operand query of 2–64 equations, Lean selects row indices using the original
pairs of root IDs. It discards identities and keeps one occurrence of each remaining
equation up to symmetry. A second pass compares equalities inside a shared free or AC context
and selects the original rows. The residual solver repeats row selection when decomposition
exposes another duplicate. Variables occurring solely in discarded rows still get an
image in every answer. In one 23-equation GDH query, this exposes a three-factor
equation and its image under a shared context. All 20 unifiers agree with Maude up
to fresh naming. [Row selection and caller projection](Tamarin/OperandRefinement.lean) ·
[Selection under shared contexts](Tamarin/ContextRowSelection.lean)

Equations outside the matrix stay in the residual worklist. For a variable equation, Rust sends the selected variable’s ID, the opposite
root kind, the two root sorts and the opposite term’s variable IDs. Lean derives the occurs check
and chooses a sorted binding, identity or clash. For a rigid pair, Rust sends each root’s kind and symbol ID with its ordered
immediate-child IDs. Lean checks the two rows, including multiplicities, and selects identity,
clash, free decomposition, C alignment or AC cancellation. When cancellation and ordinary
bindings leave open AC equations, Rust batches equations at one head and calls the same
homogeneous solver through the operand export. It reserves names locally from the original query,
pending terms and accumulated bindings, including witnesses confined to another variable’s image.
[Rigid-step worklist proof](Tamarin/ResidualRigidWorklist.lean) · [Variable-step contract](Tamarin/ResidualVariable.lean) · [Lazy binding refinement](Tamarin/ResidualVariableWorklist.lean) ·
[Residual action contract](Tamarin/Residual.lean) · [Worklist semantics](Tamarin/ResidualSearch.lean) ·
[Rust encoder](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-term/src/lean_unification/whole.rs) ·
[Fixed graph wire format](TamarinWire.lean) · [Flat-row proof](Tamarin/WholeLayout.lean) ·
[C bridge](../native/lean_unification.c)

Rust retains full term identities and concrete caller names. For witness-bearing answers, every
occurrence of a slot in an answer must receive the same fresh name. Distinct live slots must receive
distinct names of their declared sorts, disjoint from the caller’s scope. Rust may reorder C or AC
children after renaming. The projection theorem permits this reordering modulo B, requires exact
identity outside the original domain and allows identical projected answers to be returned once. Other answers can reuse
slot numbers. Rust’s substitution adapter checks that a uniform index shift fits, using gaps in the
caller’s scope when necessary. The whole-problem export takes no freshness argument.
[Caller freshening theorem](Tamarin/CallerFreshening.lean) ·
[Rust allocator](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-term/src/subst_vfresh.rs)

In native-only ordinary unification, Rust proposes a substitution θ and residual equations. Composing θ
with any residual solution must solve the original equations. Every original solution ρ must
also solve the residual and agree with ρ ∘ θ on every original variable. Lean proves these
properties by checking three root lists in one graph. An empty residual certifies that θ alone
covers every solution. With a residual AC matrix, its variables index the columns and slot
allocation reserves variables from all three lists.
If the original equations do not directly justify the proposed bindings, the checker replays
single bindings, exposes matching free heads and compares the result modulo C/AC. Exhausting
the replay budget on the top-level factor sends the original query to the total solver. CI requires
acceptance for the direct sorted-binding fragment and a chain whose second elimination specializes
the first binding.
[Factoring laws](Tamarin/FactoredUnification.lean) · [Checker](TamarinRuntime/FactorCheck.lean) · [Guaranteed fragment](Tamarin/FactorAdmission.lean)

For completed homogeneous answers, Lean tags each row with its column and renumbers witness slots
in first-use order across all arms. Projection succeeds even for a complete clash (zero arms).
Rust assigns the ordinals unused local indices. On the checked factored path it composes the
residual answer with θ and writes one binding per original variable. This includes identities so
a variable shared with another image stays shared when the caller freshens that arm. Lean proves
that interpreting the tagged packet, composing and opening this table gives a complete set on
the original equations for any valid caller allocation. The proof allows AC factors in any order.
[Tagged packet semantics](Tamarin/ProjectedBindings.lean) · [Local allocation](Tamarin/OrdinalAllocation.lean) ·
[Caller opening theorem](Tamarin/DenseOpening.lean)

Rust still supplies the graph and column-to-variable mapping and implements the modeled binding
operations. Native-only validates successful free factoring before returning a family, deciding
AC-free unifiability or solving a changed residual. Branch-local checks also cover C orientations,
AC cancellation and variant joins. Hybrid and Maude retain their existing factoring paths.
The residual worklist, caches, C bridge and Lean toolchain also remain trusted.
[Graph-to-matrix refinement](Tamarin/GraphMatrixRefinement.lean) · [Joint contract](Tamarin/GraphUnification.lean)

CI compares proof runs against Maude because branch order and redundant instances can affect
Tamarin’s proof search even when two answer sets cover the same solutions.
[Reference encoding](Tamarin/TermEncoding.lean) ·
[Fresh substitution representation](Tamarin/FreshSubstitution.lean) ·
[Proof comparisons](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-prover/tests/lean_unification.rs)

## Coverage and remaining work

| Operation | Native coverage today | Remaining completeness work |
| --- | --- | --- |
| Ordinary free/C/AC unification | The reference switch sends both enumeration and existence queries straight to the complete solver. Nested packed equations share one substitution. The solver accepts mixtures of free, commutative and AC heads, including kind-level inputs. | Check Rust representation and observable answer ordering across the protocol corpus. [Solver contract](Tamarin/TotalUnifyPacket.lean) |
| Directional matching | The reference switch uses the complete matcher for enumeration, existence and first-match queries, including caller-designated rigid variables. For source refinement every backend selects the least restored binding map, including on ambiguous matches. | Full hybrid enumeration retains its existing order for callers that consume the whole sequence. [Matcher contract](Tamarin/TotalMatchPacket.lean) · [Selection theorem](Tamarin/MatchOrder.lean) |
| Reduction | Protocol sessions retry the original term against the entire emitted equation table after a bounded decline. A finite stage suffices on every range-restricted, sort-preserving canonical table, including proper AC subproducts. | The packet must decode and the final numeric budget must cover the rewrite height. [Export and driver proofs](TamarinCI.lean) |
| Variants | Protocol sessions retry general folding for the original observation tuple under the same assumptions and FVP. Each accepted substitution reconstructs unique values even without assuming confluence. | The stages and bindings must fit the interface. Raw library sessions still offer certificate-only admission. [Export and driver proofs](TamarinCI.lean) · [Replay](Tamarin/GeneralVariants.lean) |

The all-paths reference reducer (`GeneralReductionWire.run`, a library procedure and no longer
an export) has its progress specified in terms of the rewrite relation. Once the
stage covers every path from this input and all reachable normal endpoints preserve its
sorts, it must return the unique normal form or report a conflict between inequivalent
normal forms. This obligation applies even when other terms in the module have divergent
rewrites. A replacement reducer may establish either outcome earlier.
[Progress specification](Tamarin/CheckedReductionPacket.lean) · [Semantic depth bound](Tamarin/CheckedReduction.lean)

A table-wide certificate applies to every arity-correct input, including kind-level contexts. The
first admitted class defines nullary free symbols by ground terms built from constructors. Multiple
definitions of one symbol must agree modulo C/AC, every right side must preserve the declared sort,
and every active rule must qualify. The checked Rust path can encode declared nullary symbols in rules. It still
defers tables containing query-local literal names in rule buckets. [Class and normalizer](Tamarin/ConstantDefinitions.lean) · [Public regression](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-term/tests/native_backend/checked_reduction.rs)

For destructor tables, every left side has a defined free head over constructor patterns.
All rules with the same head return a subterm at a common path through free constructors.
Patterns can test repeated variables or contain C/AC constructors. This admits pairing projections
and symmetric decryption. On an arity-correct but ill-sorted input the matcher still checks
the sorts of rule variables. The finite-variant proof counts free applications with a reducible
subterm, so even large irreducible substitution images contribute zero. Generic narrowing can
emit redundant instances. [Table admission and reduction](Tamarin/DestructorTable.lean) ·
[Uniform bound and variants](Tamarin/DestructorVariants.lean)

The general folding reference accepts an arbitrary range-restricted table, including user
equations mixed with builtins. Set `TAM_RS_NATIVE_REFERENCE_VARIANTS=1` with
`--algebra-backend=native-only` to select it for variant queries. Rust callers can use
`variants_for_convergent_theory` directly.
Lean checks each row against the original tuple. For a sort-preserving, terminating and
confluent presentation with the finite variant property modulo C/AC, Lean proves that the
search reaches a complete family at a finite budget. Rust retries incomplete stages with
a larger budget and checks cancellation between calls. The numeric packet must represent
the budget and bindings. Batch proofs, intruder variants and library callers using
`MaudeHandle::start_for_tamarin_theory` take this route on a bounded decline, including when
the specialized rule table could not be prepared. The source of the full rule set is the
same `MaudeSig::rrules()` used by the Maude printer. The theorem covers any sequence of retry
budgets with a sufficiently funded last stage. Rust constructs and decodes the packets.
Tamarin’s theory assumptions come from the author. An invalid presentation can diverge or
lose completeness. Lean rejects witnessed ambiguity and verifies unique reconstruction of
each accepted reference row. Raw library handles opened with `start_with_backend` retain the
certificate-only default for untrusted equations.
[Table classifier](Tamarin/CertifiedTable.lean) · [Promotion contract](Tamarin/CertifiedTableWire.lean)
[Executable and theorems](Tamarin/GeneralVariants.lean) · [Rust acceptance test](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-term/tests/native_backend/checked_variants.rs)

For a canonical table, it suffices to give each operator a bound on **one** normalization
path when its arguments are already normal. These bounds compose for the whole query,
including shared variables. In DH, well-sorted factors can cancel in groups. Factors of an
incompatible sort remain in the surrounding AC product. The mixed-table proof allows a
free or commutative rule to return a subterm, a ground expression that uses other equations,
or a constructor expression built from matched variables. For `decode(box(x)) → ok(x)`,
normal arguments give a normal image for `x`, and `ok` has no defining equation in the
combined table. The same proof covers nested free, commutative and AC result constructors.
Ground outputs may themselves reduce. The structural checker compares competing rules by
projection paths, normal ground outputs, or unification of the two patterns modulo C/AC.
When this criterion is inconclusive, Lean can compute a finite covering family of variants
for a single rule's left side in the entire table. Agreement on every overlap gives a unique
normal form for each normalized instance. The finite family also bounds the path to that
form. This works for defined calls in a result, such as `decode(box(x)) → check(x)`, and
for calls nested in a pattern, such as `inspect(check(x)) → x`. Search can defer if it
cannot certify the family within its budget. [Rule check](Tamarin/DefinedPatterns.lean) ·
[Uniform bound](Tamarin/OperatorVariantBounds.lean) · [Whole-table proof](Tamarin/PresentationComponents.lean)

For a user-declared AC symbol with the single law `join(x,e) → x`, Lean checks that `e`
is an irreducible message constant. Two normal message operands take at most one rewrite.
In a flattened product containing a Node, a unit can still cancel against a message
elsewhere in the product. With only the Node and the unit, neither factor can reduce.
[AC unit proof](Tamarin/UserAC.lean) · [Sort and subproduct tests](Tests/UserAC.lean)

For XOR, two normal operands need at most two rewrites at the XOR head. This bound
applies even when each contains many common factors, since the repeated variable can
capture their entire product. DH and XOR share a proof that isolates the message-sorted
factors. For example, `node ⊕ m ⊕ m` reduces to `node ⊕ zero` when `node` has sort
Node and `m` has sort Msg. The XOR checker accepts Fresh names and variables and
currently requires every declared operator to have an output sort other than Fresh.
Each component lists its equations and the heads it interprets. Lean checks all
inventories against the full table, including the other components and user equations.
For bilinear pairing, the point action uses the DH product bound and the commutative map
uses the DH power bound. A single component proof works for multiple maps sharing a
point action. The same rule matcher recognizes renamed equations for XOR and bilinear
pairing, and termination weights can be inferred from the oriented equations.
[Composition criterion](Tamarin/PresentationComponents.lean) · [Bilinear bounds](Tamarin/BilinearOperatorPaths.lean) ·
[Production packet](Tamarin/BilinearWire.lean)

Arbitrary user extensions require a whole-table argument. For example, the two rules
`f(s(x)) → g(x)` and `g(x) → f(x)` each take at most one root step above normal arguments
in isolation. Together, reducing `f(sⁿ(a))` to `f(a)` consumes every occurrence of `s`.
The uniform path bound implied by any finite family fails on the single query `f(x)`.
Lean proves this failure, and the Maude probe requests only the first six variants.
[Tamarin's theory assumptions](https://github.com/tamarin-prover/tamarin-prover/blob/573a43953195d83e62fdbe32fc98253031bca60f/manual/src/004_cryptographic-messages.md#L129-L143) ·
[Counterexample](Tests/VariantCompositionLimit.lean) · [Bounded Maude probe](Tests/check_maude_operations.py)

**Retiring older paths.** At `cd3d2f0`, the four general operations and their wire and semantic
proofs imported 194 of the 419 modules under `lean/Tamarin`. Review the remaining 225 modules
by Rust caller. For each candidate, run its public regressions with the specialized branch
bypassed and check completion, first-answer behavior, and Boolean or paged queries that avoid
materializing the full family. Preserve shared proof dependencies when retiring an entry point.

Ordinary unification and narrowing now use the same Lean sort check on the original terms.
The separate natural-sum sort-profile packet has been retired. Native-only preserves the empty
identity binding for reflexive kind-level sums. Independent unification components keep their
own solver so a conjunction with few answers can finish without enumerating partitions across
components. [Sort checks](Tamarin/NarrowingClash.lean) · [General packet regression](Tests/TotalUnifyPacket.lean) · [Public regressions](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-term/tests/native_backend.rs)

The default native-only path treats a Rust factoring failure as a proposed clash. Lean replays free
decomposition, sort checks, variable elimination, and occurs checks on the equations
before factoring. A confirmed clash rules out solutions in the caller's full signature.
An inconclusive replay leaves the original query available to the general solver.
[Refutation contract](Tamarin/TotalUnifyWire.lean) · [Checked replay](Tamarin/FactorRefutation.lean) · [Unfactored Maude comparison](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-term/src/lean_unification_integration_tests.rs)

The atom case of `X + a = Y + b` now takes its completeness and freshness proof from the
general compound-offset theorem. The dependent allocation path for `X + Y = Z + A[X]` still
preserves the Rust caller's witness allocation after factoring. [Atom specialization](Tamarin/SharedOffset.lean) · [Dependent allocation](Tamarin/DependentAllocation.lean)

**AC reference.** The homogeneous solver is total for any finite system of variable products
at one AC head when every variable has the operator’s sort. For arbitrary sorted operands,
the reference flattens and interns equal operands, then returns residual conjunctions whose
union preserves the original solutions and pending bindings.

The mixed reference interns subterms and merges equated roots. Competing free definitions
identify corresponding arguments. Competing C definitions branch on the two alignments.
For each AC operator, the homogeneous solver splits all its slot equations together. Each
child retains the other operators’ constraints and the observed slot values. The internal
one-sort signature also admits kind-level input terms. Projection restores source sorts and
caller freshness. [Purification](Tamarin/MixedReconstruction.lean) · [AC frontier](Tamarin/MixedComponentSearch.lean) · [Sort transfer](Tamarin/MixedComponentEncoding.lean)

For `X + a = Y + b`, the reference returns the exact swap and the family with a common
nonempty remainder. A second AC operator can force two previously distinct sums to agree.
The solver then reruns the original equations with that equality. Each retry consumes one pair
of original subterms, so generated witnesses cannot trigger an unbounded chain of retries.
The regression `Y = X + a, Y + b = X + Z` recovers `Z = a + b` with `X` free.

If that search leaves a residual open, a finite fallback enumerates partitions of the original
slots. Every source solution induces one such partition by equality modulo B. Within it, each
AC operator supplies one simultaneous solution. A singleton local witness reconnects to its
original slot. Other witnesses stay private to their operator. The solver assembles the
definitions and checks each candidate on the original equations. Partition counts can grow
rapidly with the number of slots. [Partition proof](Tamarin/MixedSlotPartitions.lean) · [Combination proof](Tamarin/MixedCombination.lean)

CI requires the public entry point to return a complete, sorted family with caller-fresh
parameters for every input, including kind-level trees. An empty family proves that the
conjunction has no sorted unifier. [Mixed driver](Tamarin/MixedUnification.lean) · [Coverage theorem (unpinned)](TamarinProposers.lean) · [Executable cases](Tests/MixedUnification.lean)

[Sort refinement](Tamarin/UnifierSorts.lean) · [Maude sort assignment](https://github.com/maude-lang/Maude/blob/7269fc720072a2cd8b7222736721ba26dd3752b2/src/Higher/unificationProblem.cc#L306-L442) · [Homogeneous reference](Tamarin/ACReference.lean) · [Source-level AC step](Tamarin/ACReferenceBranch.lean) · [Maude dependency cycle](https://github.com/maude-lang/Maude/blob/eee00f5b0bea3a7da2b9e9f5bf1e83ce3cd1fa9f/src/ACU_Theory/ACU_UnificationSubproblem2.cc#L173-L210) · [Reopening same-head bindings](https://github.com/maude-lang/Maude/blob/eee00f5b0bea3a7da2b9e9f5bf1e83ce3cd1fa9f/src/ACU_Theory/ACU_UnificationSubproblem2.cc#L277-L343) · [Residual search contract](Tamarin/ResidualSearch.lean)

The matcher reads an AC subject as the bag of its flattened operands. Each rigid pattern
operand removes one subject operand, and the bindable variables of the same application
then share what is left, each receiving a nonempty sub-bag of its sort. Syntactically
identical operands are interchangeable, so each assignment is listed once. Requirements
on a shared variable are compared as branches are combined, and each surviving branch is
one answer without a second check on the equations. Ordinary equality modulo B is the
same procedure with no bindable variable. A variable that occurs `k` times in one
application chooses only among `⌊m / k⌋` of every `m` equal operands. Reduction matches a
left side against the same bag and keeps the operands it does not consume as the untouched
complement, just as Maude rewrites AC terms with extension, and lists each one-step result
once modulo B. A first-answer search with the same order backs the existence and
first-match entry points without listing the remaining answers. Kind-level narrowing splits
a product only to set unsorted factors aside. The variant folder checks bindings and values together before
dropping a subsumed row. The source-level probes exercise both the reference and Maude.
[Bag matcher proof](Tamarin/BagMatching.lean) · [First-answer search](Tamarin/BagSearch.lean) · [Bag matcher tests](Tests/BagMatching.lean) · [Single-path reduction on certified tables](Tamarin/CertifiedReductionWire.lean) · [AC partition proof](Tamarin/ACSplits.lean) · [Maude AC equation application](https://github.com/maude-lang/Maude/blob/7269fc720072a2cd8b7222736721ba26dd3752b2/src/ACU_Theory/ACU_Symbol.cc#L91-L112) · [Maude variant folding](https://github.com/maude-lang/Maude/blob/7269fc720072a2cd8b7222736721ba26dd3752b2/src/Higher/variantFolder.cc#L173-L217) · [Executable reference tests](Tests/ReferenceCommands.lean)

**Variant certificates.** A proposed family of variants is checked instead of searched for.
Each proposed substitution is completed with the normal forms of the instantiated query.
The family passes the closure test when every member is normal, some member subsumes the
normalized query, and every normalized one-step narrowing successor of a member is subsumed
by a member. On a canonical presentation such a family is a complete set of variants; the
proof runs the descent of the folding search inside the proposed family. The narrowing layer
uses the total unifier, so the cost of the test is one such layer per member. A product of
sorted factors is narrowed once as a whole: only unsorted factors are ever set aside. A slot
whose query term is a variable is not narrowed, since a step there makes the image of that
variable reducible. Subsumption first tries a substitution found by an unverified
left-to-right search, as Maude's folder matches one term after the other under one
substitution, and tests it with the proved equality; the complete matcher decides only when
no guess passes.

A family that is a product is not tested member by member. The slots of the query are split
into groups that share only variables every member sends to variables, each group gets the
members of distinct shape on its slots as representatives, and the closure test runs on the
representatives of each group alone. The family is accepted when, for every choice of one
representative per group, some member restricts on each group to a row that subsumes the
chosen representative, and the variables it shares between groups are images of keys common
to them. The instances found group by group then join into one. Four exponentiations with
seven variants each give 2401 members and one test on seven members per exponentiation. How the split is
chosen is not part of the proof; a family for which it fails takes the closure test on all
of its members.
[Checker and proof](Tamarin/VariantCertificate.lean) · [Closure test](Tamarin/VariantClosure.lean) · [Products](Tamarin/VariantFactoring.lean) · [Guessed matching](Tamarin/GuessedMatching.lean) · [Closed families and acceptance](Tamarin/VariantClosed.lean) · [Wire contract](Tamarin/VariantCheckWire.lean) · [Decision contract](Tamarin/VariantDecisionWire.lean) · [Packet tests](Tests/CheckedCommandPackets.lean)

**Single-path reduction.** On a certified table one rewrite path determines the unique
normal form. The path is local: a rewrite at a node is taken before its arguments are
visited, a node is looked at again only when an argument changed, and matching never
restarts at the root of the whole term. A node rewritten after its arguments is rewritten
further only at its root; the outermost path then confirms the result in one traversal or
finishes it. The same path is available for a table that is only range restricted, with a
weaker guarantee: the reply is an irreducible reduct that keeps the sorts of the input,
and nothing says it is the only one.
[Local normalizer](Tamarin/ReferenceReduction.lean) · [Wire contracts](Tamarin/CertifiedReductionWire.lean)

**Reduction and variant references.** With an empty rule table, the total reducer returns
its input and the total variant generator returns the identity family for every tuple and
free/C/AC signature. The abstract pairing reducer is total, with rule-table correspondence
on well-sorted inputs. For nonempty tables, stable tuples and linked constructor checks give
complete variant replies on their proven domains. For any finite tuple, a proposed frontier can now be checked with a
verified reducer and a complete one-step narrowing procedure. The checker includes the seed,
requires a representative of every live successor, and replays every normal row. One witness
must preserve all untouched slots and input images. Rejection leaves the query unresolved.
This certificate checks individual concrete steps. The total reference follows Maude’s
separate strategy of normalizing the seed and newly narrowed tuples before comparing variants.
[Tuple closure proof](Tamarin/TupleNarrowingFrontier.lean) · [Certified checker](Tamarin/ReferenceVariantFrontier.lean) · [Maude expansion and reduction](https://github.com/maude-lang/Maude/blob/7269fc720072a2cd8b7222736721ba26dd3752b2/src/Higher/variantSearch.cc#L397-L490)
[Reference instances](Tamarin/MaudeOperationRefinements.lean) · [Pairing table correspondence](Tamarin/PairingRewriting.lean#L37) · [Export theorem (unpinned)](TamarinProposers.lean)

**Termination of variant search.** A local narrower must prove that each branch replays one
rewrite and that some branch covers every concrete step exposed by specializing a symbolic term.
The driver carries all inputs and untouched tuple positions through the same branch substitution.
The sum of the concrete rewrite heights decreases after narrowing and normalizing. This proves
that every actual normal result has a representative at a finite depth. Applying this to a finite
covering family proves that a breadth-first layer will eventually be covered by earlier or current
rows. The reference tests subsumption at layer boundaries and permits redundant rows, as Tamarin’s
plain command does. It needs no depth bound or supplied set of expected answers.
A final renaming protects the caller’s scope across bindings and values. Root search
standardizes each rule apart and uses the total ordinary unifier. Positional narrowing
preserves untouched siblings, tuple values and input images under one shared substitution.
For a proper AC subproduct, the narrower can retain whole unsorted factors in their source
context and abstract the remaining sorted factors with a fresh variable. This covers kind-level
inputs as well as well-sorted products. [Position proof](Tamarin/TablePositions.lean) ·
[AC remainder proof](Tamarin/KindACNarrowing.lean) · [Four-command assembly](Tamarin/CompleteNarrowing.lean)
[Local root search](Tamarin/TableNarrowing.lean) · [Local obligations and command implementation](Tamarin/FoldingNarrowing.lean) · [Finite variant property to finite search](Tamarin/VariantSaturation.lean) · [Breadth-first loop](Tamarin/VariantLayers.lean) · [Rewrite heights](Tamarin/ReductionHeight.lean) · [Freshening](Tamarin/VariantFreshening.lean)

### Specification-generated coverage

Run the generated coverage test from the repository root.

```sh
cargo test --profile ci -p tamarin-term --features lean-unification --test spec_coverage -- --nocapture
```

Lean generates sorted terms through five syntax nodes for two signatures, plain AC with a
free hash and XOR with the same hash. The test exercises all four public operations,
including shared captures in conjunctions and packed variant observations. Lean marks
mandatory cases from constructor normality, incompatible matching heads and ground AC
multiset equality. CI fails if native-only defers one of those cases or returns an answer
that contradicts the expectation. Every generated reduction, ordinary unification and match must complete.
The generated set has bounded term size and answer multiplicity. Separate regressions
exercise larger families. Matching three distinct variables against eight distinct AC factors
returns all 5,796 substitutions. With two variables and 64 distinct factors, existence
succeeds without collecting the exponentially large family.
[Public regressions](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-term/tests/native_backend/paged_bag_matches.rs)

The test checks that wrapping a term in hash wraps its normal form in the same hash.
This follows from the [free constructor reduction theorem](Tamarin/ConstructorReduction.lean).
Packed queries consisting of ground or constructor-only slots in these two presentations must
admit the identity substitution. A ground slot may rewrite before its value is reconstructed.
The [observation proof](Tamarin/ObservationRepresentative.lean) requires a unique normal value
modulo C/AC for that slot. Other slots may still constrain shared variables.
Flattened cancellation sums with constructor-only factors are mandatory throughout the
five-node grammar, including packed and hash-wrapped observations. All 24,154 original
requests complete. Nine larger mandatory queries cross a hash boundary where an outer
operand may cancel the changing hash. Two wider shared-variable sums must also complete. The mixed pairing and cancellation
presentation requires all 16 staged expressions to reduce and all 16 joint variant queries to complete.
Two larger mixed variants have 71 and 72 rows. A separate user-defined AC presentation
has 345 mandatory exact reductions, each also checked under a hash. The expected answer
comes from the multiplicities of two declared constants, public names and rigid variables.
All four open marker variant families are mandatory. They have 3, 7, 13 and 7 distinct
rows. For example, a normalized input `m = merge(a,c)` makes `merge(m,a)` reduce to
`merge(a,c)`. With only the bare marker equations Maude 3.5.1 omits this variant.
Adding the equivalent proper-subproduct equations makes Maude agree with the independent
multiplicity model and the native rows. This difference applies to experimental native-only
answers. [Variant comparisons](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-term/src/lean_variant_frontier_tests.rs)

The DH generator uses the expression language of the power proofs and Rust’s full builtin
DH signature. It exercises all four public operations, including both sides of seven DH
equations. Joint observations of two distinct stable factors on the same open exponent
give 14 variants. An observation with an independent exponent gives 12. Each count is
mandatory, and separate Maude comparisons check all input images and reduced values.
The product of two independent Msg variables has 47 variants. Their power `X^Y`,
the tower `(g^X)^Y` and the flat power `g^(X*Y)` each have 48. Observing
`(B^Y)^r` alongside `Y`, with independent Msg inputs and a Fresh exponent
`r`, yields all 160 Maude rows. The bilinear-pairing grammar exercises
the three rules at `pmult` and `emap`, with joint comparisons of bindings and
normal values. Native-only completes the unrestricted two-variable families for
both operations (47 and 48 Maude rows). All 47 bilinear variant queries are mandatory,
including a pairing of two point actions with 336 variants. The seventh presentation uses Nat-sorted variables and positive integer partitions across all four operations.
All 24,744 requests in the current grammar must complete, including all 6,861 ordinary unifications and 6,884 matching requests. [Bilinear family proof](Tamarin/BilinearRows.lean)
The report prints the smallest deferred request per operation and compares it with Maude
when `MAUDE_PATH` is set.
The report counts syntactic requests in this bounded grammar. Protocol regressions
separately exercise ordering and proof search.
[Lean generator and expectations](Tests/NativeCoverage.lean) ·
[Public API check](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-term/tests/spec_coverage.rs)

### Native algorithms and protocol regressions

- **Source selection.** Upstream Haskell uses the first matcher Maude enumerates. Rust selects
  the lexicographically least complete binding map across all backends. Bindings occur in
  caller variable order, images use the caller's canonical C/AC term order, and identity
  bindings are explicit. This can select a different valid substitution from upstream when
  a source is ambiguous. Duplicating or reordering solutions preserves this choice.
  [Order contract](Tamarin/MatchOrder.lean) · [Source selection](https://github.com/tamarin-prover/tamarin-prover/blob/573a43953195d83e62fdbe32fc98253031bca60f/lib/theory/src/Theory/Constraint/Solver/Sources.hs#L279)
- **Existence and enumeration.** Two captures against 64 distinct AC factors already give an
  exponential family. Boolean matching and unifiability have decision paths. In paged matching,
  a page can advance without producing a binding, and sort filtering precedes the collection
  limit. Tests check the Boolean answer on the wide input and the entire family on smaller ones.
  [AC feasibility](Tamarin/ACFeasibility.lean) · [Page contract](Tamarin/ACPagePacket.lean) · [Public matching tests](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-term/tests/native_backend/paged_bag_matches.rs)
- **Shared variables.** An ordinary unifier must account for earlier bindings and residual equations
  together. For tuple variants such as `[fst(x), snd(x)]`, both values and the caller's image of
  `x` must share one substitution. Reopening witnesses and combining independent answer families
  can change which assignments survive. [Independent unification](Tamarin/IndependentUnification.lean) · [Variant joins](Tamarin/VariantJoinFamily.lean) · [Joint projection model](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-prover/tests/fixtures/native_joint_projections.spthy)
- **Theory-specific equations.** Cancellation requires the active equations and unit for the AC
  head. DH products use signed multiplicities, and bilinear variants reconstruct point and scalar
  values together. The public corpus exercises builtin and user-declared cancellation, received
  DH powers and bilinear pairing through theory closure, source refinement and proof search.
  [Cancellation](Tamarin/CancellationConvergence.lean) · [Signed products](Tamarin/SignedGraphContract.lean) · [Bilinear variants](Tamarin/BilinearRows.lean) · [Protocol comparisons](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-prover/tests/lean_unification.rs)

For end-to-end changes, the native-only CLI tests run with a missing Maude executable and check
that an unsupported theory cannot publish a proof. The AC marker regression also checks the
reachable trace when Maude omits a variant. [CLI and verdict tests](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-prover/tests/native_backend.rs)

### Proposed cross-query reuse

Today each AC unification can reuse a numeric matrix packet across its own branches.
The packet disappears when the query finishes. Session-wide reuse is a later roadmap
item, pending measurement and design review.

1. **Measure the opportunity.** On GDH and the wider proof corpus, count repeated
   matrix inputs *between* queries, separately from hits within one query. Weight
   repetitions by measured kernel time and simulate byte limits. Compare the projected
   savings with lookup, copying and contention costs before choosing a cache size.
2. **Keep the solver pure.** Start with one bounded, in-memory cache per theory session
   for the homogeneous operand kernel. Key it by its full numeric input (width and ordered
   occurrence rows). Store completed, immutable packets of column tags and witness
   ordinals, including a completed empty family. Rebuild all terms and fresh names in
   the current caller. Only publish a packet after a successful complete return.
3. **Prove the invariant.** For every stored entry `(k, p)`, the linked pure kernel on
   `k` returns exactly `some p`. Prove that lookup, insertion and eviction preserve
   this property, and that a hit reproduces the packet, arm order and caller-visible
   result. Keep the existing query-local accounting. Charge a session-cache hit just
   as the corresponding local miss would have been charged, and check cancellation on hits. For the same inputs, work budget
   and cancellation observations, the result must be independent of cache history.
4. **Check the adapter.** Own the shared packet bytes in Rust and compare full keys
   on collisions. Run misses outside the cache lock. Concurrent insertions for one
   key must yield the same packet. Test cold, warm, evicted and concurrent runs with
   different caller scopes, cancellation and tight budgets. Compare whole-proof time,
   memory, verdicts and branch order before enabling reuse.

## Verification and measurement

From this directory, these commands recheck the compiled proofs, run the whole-query examples and
exercise the fixed contract against incorrect candidates.

```sh
lake build TamarinCI TamarinRuntime
lake build TamarinProposers
lake env leanchecker --fresh TamarinCI
lake env lean --run Tests/ExportAudit.lean --sources . --unpinned TamarinProposers
lake env lean Tests/WholeProblem.lean
lake env lean Tests/ACRowElimination.lean
lake env lean --run Tests/ACPivot.lean
lake env lean Tests/FactoredUnification.lean
lake env lean Tests/FactorReplay.lean
lake env lean Tests/GraphUnification.lean
lake env lean Tests/AnswerProjection.lean
lake env lean Tests/OperandCounts.lean
lake env lean Tests/OperandUnification.lean
lake env lean Tests/ProjectedOperands.lean
lake env lean Tests/SortedMatch.lean
lake env lean Tests/OpenMatchSelect.lean
lake env lean Tests/CompoundPartitions.lean
lake env lean Tests/OpenMatch.lean
lake env lean Tests/MatchOrder.lean
lake env lean Tests/NestedTreeMatch.lean
lake env lean Tests/CanonicalTree.lean
lake env lean Tests/RecursiveACMatch.lean
lake env lean Tests/StableDH.lean
lake env lean Tests/DHProductUnique.lean
lake env lean Tests/VariantJoin.lean
lake env lean Tests/Theory.lean
python3 Tests/check_audit.py
```

Run `lake env lean --run Tests/DHTower.lean` to check all emitted tower rows against
independent generators and small signed exponent assignments.
`lake env lean --run Tests/DHExponent.lean` replays shared exponents before and after
multiplication against integer addition on three independent atoms.
For an independent count-based stress test of flat matching, run
`lake env lean --run Tests/MatchingStress.lean`. CI also checks variable capture, missing branches,
malformed packets, interruption and counterexamples involving rewrite rules.
[Stress test](Tests/MatchingStress.lean) · [Specification audit](Tests/ExistingSpecAudit.lean) ·
[Full CI commands](../.github/workflows/ci.yml)

From the repository root, the first command tests native operations without a Maude binary. The
remaining commands use Maude as an oracle. Set `MAUDE_PATH` to its executable when needed.

```sh
cargo test --profile ci -p tamarin-term --features lean-unification --test native_backend
cargo test --profile ci -p tamarin-term --features lean-unification --lib native_oracle_
TAM_RS_VERIFY_LEAN_UNIFY=1 cargo test --profile ci -p tamarin-term --features lean-unification --lib -- --test-threads=1
cargo test --profile ci -p tamarin-prover --features lean-unification --test lean_unification --test native_backend
```

For performance work, unset the oracle and native-disable switches, then run the flat AC benchmark.
It checks answers against Maude and reports cold and warm query times including dispatch, encoding
and conversion.

```sh
cargo run --profile ci -p tamarin-term --features lean-unification --example lean_unification_bench -- 1000
```

The benchmark above measures the hybrid path. A separate native-only measurement used the same
32 distinct factors on both sides of one equation, with 500 calls per run and seven alternating
warmed runs in the optimized `ci` profile. Compact AC rows reduced the packet from 228 to 138
words, median Rust encoding from 9.94 to 7.17 µs, C input copying from 1.50 to 0.89 µs, and the
complete kernel call including encoding from 184 to 65 µs. Full native-only proof output matched
on `counter`, `xor` and `NumberSubtermTests`, with median elapsed times moving by less than 3%.
[Hybrid benchmark source](https://github.com/kmilner/tamarin-rs/blob/774b0c35f7422b3fa2be54c713ef5f8c5d16a59b/crates/tamarin-term/examples/lean_unification_bench.rs)

An earlier revision of this file reported 4.12 s native-only against 3.43 s with Maude
for the full `ake/dh/NAXOS_eCK_PFS` proof. A November 2026 audit did not reproduce that
figure at this revision or at `ef88e27`: with one worker, native-only took 21.1 s and
Maude 2.67 s, and both found the same trace.

The same audit proved the 451 example theories with one worker and a 300 s limit.
Maude finished 448 and native-only finished 429 of those; the other
19 were 18 timeouts and one memory abort (`ake/dh/UM_one_pass_attack`, in the reference
matcher). No verdict differed on a theory both backends finished, apart from the
`native_ac_marker_trace` fixture, where Maude omits AC coherence completion. Free and
subterm-convergent theories ran at 0.4× to 1.4× of Maude's CPU time. Proof search over
DH, bilinear pairing and XOR ran 2.6× to 9.4× slower (CRxor 2.6×, wireguard 4.5×,
CH07 5.6×, NAXOS 7.9×, Joux 9.4×), and 28 theories that take Maude at least 1 s were
more than twice as slow. Native-only is therefore not yet a replacement for Maude on
those theories. The per-query measurements below are narrower than these end-to-end runs.

On `experiments/A-GDH2`, generating the closed theory took a median of 1.15 s
native-only and 15.09 s with Maude across three fresh, single-worker runs per backend
after warm-up on the final build, during local verification. This measures rule variants
and theory closure, before source saturation.

For the 47 variants of `[X*Y, X]` under DH, the native median was 414 ms and the
Maude median was 275 ms. Five alternating fresh-handle measurements followed one
warm-up per backend in the optimized `ci` profile. Timing covered the public variants
call, excluding handle startup and the independent answer comparison.

On the captured 16-equation GDH query, native unification took about 0.35 s after
context selection and query-local packet reuse, down from 3.52 s with the initial
owner split. Maude took about 7 ms. These are medians of three calls per backend in
the optimized `ci` profile with a fresh handle per call, excluding handle startup.

On `sp14/GDH`, source precomputation took 1.25 s native-only and 1.32 s with Maude
(medians of seven alternating fresh single-worker runs after warm-up). The ranges
overlapped at 1.21–1.68 s and 1.20–1.60 s respectively.

The flat AC matcher prunes assignments using the minimum remaining number of subject
positions, weighted by variable multiplicity. On five supported matching workloads,
the compiled Lean kernel ran 2.27× to 14.14× faster than the previous candidate.
These are medians of seven 16-query batches, including packet conversion and excluding
Rust and FFI. [Matcher proof](Tamarin/FlatMatchCandidateProofs.lean)
