import Tamarin
import Tamarin.ReductionSignatureExtension
import Tamarin.CheckedReductionPacket
import Tamarin.DHMixedVariants
import Tamarin.DHFiniteVariants
import Tamarin.TablePresentation
import Tamarin.DHWire
import Tamarin.DHConstructorWire
import Tamarin.XorConstructorWire
import Tamarin.JointGroupWire
import Tamarin.JointGroupTable
import Tamarin.BilinearWire
import Tamarin.CertifiedReduction
import Tamarin.CertifiedReductionWire
import Tamarin.VariantCheckWire
import Tamarin.SessionTableWire
import Tamarin.VariantDecisionWire
import Tamarin.Candidates.TableProofs
import Tamarin.TableStages
import Tamarin.DHMixedTermination
import Tamarin.TableConfluence
import Tamarin.CheckedVariantsPacket
import Tamarin.TotalUnifyPacket
import Tamarin.TotalUnifyDecline
import Tamarin.TotalMatchPacket
import Tamarin.SignatureExtension
import Tamarin.MatchingSignatureExtension
import Tamarin.UnavailableSort
import Tamarin.VariantSortRestriction
import Tamarin.ACMatchPacket
import Tamarin.ACMatchAnswerPacket
import Tamarin.ACPagePacket
import Tamarin.ACSortedBagPacket
import Tamarin.TotalFreeVariants
import Tamarin.ProjectedRuleMatches
import Tamarin.ACMatchSortedBags
import Tamarin.ACBagAnswers
import Tamarin.ACBagSearch
import Lean

/-!
# The contract

Every public theorem of this module is a contract statement: the export audit
pins its kernel statement in `ExportManifest.txt` and every definition the
statement depends on in `SpecManifest.txt`. Each one mentions a contract
export, one of the eleven exports whose reply the Rust backend uses as the
answer:

* `totalUnify`, `totalUnifyExists`, `unpackConjunction`, `totalMatch`,
  `totalMatchExists`;
* `certifyTable`, `sessionReduce`, `checkedReduce`, `pathReduce`;
* `sessionVariantCheck`, `checkedVariants`.

A statement here says what a reply means in terms of the decoded packet and
the rewrite relation. No statement names a search, a classifier or a
reference procedure, so declining is limited only where a semantic condition
or a concrete packet does it. The remaining exports are proposers and carry
no contract. Their theorems, and the coverage statements that were stated
through reference procedures, are in `TamarinProposers.lean`, which is not
pinned.
-/

namespace Tamarin

/-- Every arity-correct query has a complete family on its declared signature,
and the reply is that family fully decoded unless one of its answers adds at
least `2^64 - bound` distinct variables to the query, `bound` being the least
identifier above the variables of the query. Malformed input has the same
decline status. -/
theorem exportedTotalUnify_correct : TotalUnifyWire.Packet.Correct Executable.totalUnify :=
  TotalUnifyWire.Packet.correct

/-- The decision export answers 1 exactly when the decoded query has a
unifier, 2 exactly when it has none, and 0 exactly when the packet does not
decode. It never declines a decoded query. -/
theorem exportedTotalUnifyExists_correct :
    TotalUnifyWire.ExistsCorrect Executable.totalUnifyExists :=
  TotalUnifyWire.existsCorrect

/-- The decision also holds in the caller's entire signature, even when only
the declarations occurring in the terms crossed the wire. -/
theorem exportedTotalUnifyExists_ambient {ds ns es d p}
    (decoded : TotalUnifyWire.input ds ns es = some ⟨d,p⟩) (extra : Signature) :
    Executable.totalUnifyExists ds ns es = 1 ↔ ∃ σ, (SignatureExtension.query extra p).Solves σ := by
  obtain ⟨answers,ok,_⟩ := exportedTotalUnify_correct.valid _ _ _ _ _ decoded
  have lifted := (SignatureExtension.correctIn extra p [] ok).mathematical
  have here := ok.mathematical
  have local_iff : (∃ σ, p.Solves σ) ↔ answers ≠ [] := by
    constructor
    · rintro ⟨ρ,sol⟩ empty
      obtain ⟨σ,mem,_⟩ := here.covers ρ sol
      rw [empty] at mem
      cases mem
    · intro some
      obtain ⟨σ,rest,rfl⟩ := List.exists_cons_of_ne_nil some
      exact ⟨σ,here.sound σ List.mem_cons_self⟩
  have ambient_iff : (∃ σ, (SignatureExtension.query extra p).Solves σ) ↔ answers ≠ [] := by
    constructor
    · rintro ⟨ρ,sol⟩ empty
      obtain ⟨σ,mem,_⟩ := lifted.covers ρ sol
      rw [empty] at mem
      cases mem
    · intro some
      obtain ⟨σ,rest,rfl⟩ := List.exists_cons_of_ne_nil some
      exact ⟨_,lifted.sound _ List.mem_cons_self⟩
  rcases exportedTotalUnifyExists_correct.valid _ _ _ _ _ decoded with ⟨yes,hit⟩ | ⟨no,miss⟩
  · exact ⟨fun _ => ambient_iff.mpr (local_iff.mp hit),fun _ => yes⟩
  · refine ⟨fun yes => by simp [no] at yes,fun hit => ?_⟩
    exact (miss (local_iff.mpr (ambient_iff.mp hit))).elim

theorem exportedUnpackConjunction_correct : PackedConjunction.Correct Executable.unpackConjunction :=
  PackedConjunction.correct

theorem exportedTotalMatch_correct : TotalMatchWire.Correct Executable.totalMatch :=
  TotalMatchWire.correct

/-- Exact matching coverage in the caller's entire signature, even when
only the declarations occurring in the terms crossed the wire. -/
theorem exportedTotalMatch_ambient {ds ns es d p} (ids)
    (decoded : TotalUnifyWire.input ds ns es = some ⟨d,p⟩) :
    ∃ answers, TotalUnifyWire.Packet.Decodes p (Executable.totalMatch ds ns es ids) answers ∧
      ∀ extra : Signature, Matching.Complete (SignatureExtension.query extra p) (TotalMatchWire.Bindable ids)
        (answers.map (SignatureExtension.liftSubst extra)) := by
  obtain ⟨answers,hp,ok⟩ := exportedTotalMatch_correct.valid _ _ _ _ _ _ decoded
  exact ⟨answers,hp,fun extra => SignatureExtension.matching extra p ok⟩

/-- The decision export answers 1 exactly when a scoped match exists and 2
exactly when none exists. -/
theorem exportedTotalMatchExists_correct : TotalMatchWire.ExistsCorrect Executable.totalMatchExists :=
  TotalMatchWire.existsCorrect

/-- The decision also holds in the caller's entire signature, even when only
the declarations occurring in the terms crossed the wire. -/
theorem exportedTotalMatchExists_ambient {ds ns es d p} (ids)
    (decoded : TotalUnifyWire.input ds ns es = some ⟨d,p⟩) (extra : Signature) :
    Executable.totalMatchExists ds ns es ids = 1 ↔
      ∃ σ, Matching.Matches (SignatureExtension.query extra p) σ ∧
        Matching.Scoped (SignatureExtension.query extra p) (TotalMatchWire.Bindable ids) σ := by
  obtain ⟨answers,_,ok⟩ := exportedTotalMatch_correct.valid _ _ _ ids _ _ decoded
  have lifted := (SignatureExtension.matching extra p ok).nonempty_iff
  have here := ok.nonempty_iff
  have same : answers.map (SignatureExtension.liftSubst extra) ≠ [] ↔ answers ≠ [] := by simp
  rcases exportedTotalMatchExists_correct.valid _ _ _ ids _ _ decoded with ⟨yes,hit⟩ | ⟨no,miss⟩
  · exact ⟨fun _ => lifted.mp (same.mpr (here.mpr hit)),fun _ => yes⟩
  · refine ⟨fun yes => by simp [no] at yes,fun hit => ?_⟩
    exact (miss (here.mp (same.mp (lifted.mpr hit)))).elim

theorem exportedCheckedReduce_malformed {ds ns es root n}
    (malformed : TableWire.input ds ns es #[root] = none) :
    Executable.checkedReduce ds ns es root n = #[#[0]] :=
  CheckedReductionWire.correct.malformed _ _ _ _ _ malformed

/-- What a reply of the checked reducer means. A status 1 reply decodes to
the normal form of the term: a reduct that is irreducible, and to which every
other normal form of the term is equal modulo the declared C and AC laws, in
the dictionary of the packet and in every extension of it by further caller
symbols. The only other reply to a decoded packet is the decline `#[#[2]]`.

Nothing here limits declining. The reducer declines by a resource policy (a
table-derived depth and a work limit on the rewrite graph) that has no
counterpart in the rewrite relation: the cost it guards against is the number
of matches of a rule against a wide AC product, which no property of the
rewrite relation bounds. The two floors below are the only limits. A caller
that needs an answer where this export declines uses `pathReduce`, whose
replies are all specified by the rewrite relation and which claims no
uniqueness. -/
theorem exportedCheckedReduce_sound {ds ns es root n d t rs}
    (decoded : TableWire.input ds ns es #[root] = some ⟨d,rs,[t]⟩) :
    GeneralReductionWire.Answer d rs t (Executable.checkedReduce ds ns es root n) ∨
      Executable.checkedReduce ds ns es root n = #[#[2]] := by
  rcases CheckedReductionWire.correct.valid _ _ _ _ n _ _ _ decoded with ⟨u,packet,reply⟩ | ⟨declined,_⟩
  · suffices bound : ReferenceReduction.Bound rs from
      .inl ⟨u,packet,reply,fun extra => SignatureExtension.reduction extra rs bound t u reply⟩
    obtain ⟨words,_,shape,_⟩ := packet
    cases defs : CheckedReductionWire.definitions rs with
    | true => exact ConstantDefinitions.bound (Bool.and_eq_true_iff.mp defs).1
    | false =>
      cases proj : CheckedReductionWire.destructors rs with
      | true =>
        exact TableDecrease.bound ((DestructorTable.accepts_iff rs).mp (Bool.and_eq_true_iff.mp proj).1).decreasing
      | false =>
        cases ok : CheckedReductionWire.admitted rs t n with
        | true =>
          have parts : (CheckedReduction.rangeBound rs ∧ TableDecrease.sorted rs) ∧
              CheckedReduction.affordable rs (CheckedReductionWire.fuel rs t n) 100000 t := by
            simpa only [CheckedReductionWire.admitted,Bool.and_eq_true] using ok
          exact (CheckedReduction.rangeBound_iff _).mp parts.1.1
        | false =>
          have stop : CheckedReductionWire.run ds ns es root n = #[#[2]] := by
            simp [CheckedReductionWire.run,decoded,defs,proj,ok]
          rw [stop] at shape
          simp at shape
  · exact .inr declined

/-- What `true` means: the packet decodes and its table is certified, that is,
range restricted, a canonical presentation (terminating and confluent modulo
the declared C and AC laws) and with the finite variant property, over the
dictionary of the packet extended by all ambient names.

`false` carries no information. It is the reply to a malformed packet, and
the checker may also return it for any table, certified or not: termination,
confluence and the finite variant property are undecidable, so no statement
limits declining in general. The only limits are the three concrete packets
below. Which user tables are accepted is guarded by the corpus, not here. -/
theorem exportedCertifyTable_sound {ds ns es fuel}
    (hit : Executable.certifyTable ds ns es fuel = true) :
    ∃ d rs, TableWire.input ds ns es #[] = some ⟨d,rs,[]⟩ ∧ CertifiedTableWire.Certified rs := by
  have spec := CertifiedTableWire.correct ds ns es fuel
  cases decoded : TableWire.input ds ns es #[] with
  | none =>
    rw [decoded] at spec
    exact absurd (hit.symm.trans spec) (by decide)
  | some packet =>
    obtain ⟨d,rs,q⟩ := packet
    exact ⟨d,rs,decoded.symm.trans (TableWire.withoutObservations decoded),
      CertifiedTableWire.sound CertifiedTableWire.correct decoded hit⟩

/-- Coverage floors: these three production packets (XOR with the destructor
table, the joint group table, the bilinear pairing table) are accepted at
budget zero. A replacement of the checker may decline anything else. -/
theorem exportedPhysicalXorTable_admitted :
    Executable.certifyTable XorConstructorWire.declarations XorConstructorWire.nodes
      XorConstructorWire.ruleRoots 0 = true :=
  XorConstructorWire.admitted

theorem exportedPhysicalJointGroupTable_admitted :
    Executable.certifyTable JointGroupWire.declarations JointGroupWire.nodes JointGroupWire.ruleRoots 0 = true :=
  JointGroupWire.admitted

theorem exportedPhysicalBilinearTable_admitted :
    Executable.certifyTable BilinearWire.declarations BilinearWire.nodes BilinearWire.ruleRoots 0 = true :=
  BilinearWire.admitted

theorem exportedCheckedVariants_malformed {ds ns es roots n}
    (malformed : TableWire.input ds ns es roots = none) :
    Executable.checkedVariants ds ns es roots n = #[#[0]] :=
  CheckedVariantsWire.correct.malformed _ _ _ _ _ malformed

/-- What a reply of the checked variant generator means. A reply other than
the decline `#[#[2]]` decodes to a complete set of variants of the decoded
observations with unique values, over the dictionary of the packet extended
by all ambient names. The table needs no certificate: the generator returns
a family only where it established this itself. Nothing limits declining. -/
theorem exportedCheckedVariants_sound {ds ns es roots n d rs q}
    (decoded : TableWire.input ds ns es roots = some ⟨d,rs,q⟩) :
    CheckedVariantsWire.Decodes rs q (Executable.checkedVariants ds ns es roots n) ∨
      Executable.checkedVariants ds ns es roots n = #[#[2]] :=
  (CheckedVariantsWire.correct.valid _ _ _ _ n _ _ _ decoded).imp_right And.left

/-- On any decoded table a status 1 reply of the single-path reducer is an
irreducible reduct that keeps the sorts of the input. Convergence of the table
is not assumed, so the reply need not be the only normal form. Status 2 is
returned only for a table that is not range restricted or when an irreducible
reduct lost a sort, and status 3 only while some rewrite path is at least as
long as the depth. -/
theorem exportedPathReduce_correct : PathReductionWire.Correct Executable.pathReduce :=
  PathReductionWire.correct

/-- The session reducer reads the terms of a call from further node rows, over
the table of the rules-only packet and all ambient names. -/
theorem exportedSessionReduce_correct : SessionReductionWire.Correct Executable.sessionReduce :=
  SessionReductionWire.correct

/-- Once `certifyTable` accepts the rules-only packet `ds ns es`, every call
that adds node rows to that packet replies with the unique normal form of the
term the rows denote, or with a request for more depth. The certificate is
the one of the rules-only packet. -/
theorem exportedSessionReduce_certified {ds ns es extra root n d rs t budget}
    (decoded : SessionReductionWire.input ds ns es extra root = some ⟨d,rs,t⟩)
    (hit : Executable.certifyTable ds ns es budget = true) :
    SessionReductionWire.Answer d rs t (Executable.sessionReduce ds ns es extra root n) ∨
      Executable.sessionReduce ds ns es extra root n = #[#[3]] :=
  exportedSessionReduce_correct.valid _ _ _ _ _ _ _ _ _ decoded
    (CertifiedTableWire.sound CertifiedTableWire.correct
      (SessionReductionWire.input_table decoded) hit)

/-- Once `certifyTable` accepts the rules-only packet, every call on that
packet replies with the unique normal form at every depth that bounds all
rewrite paths from its term under the lifted rules. The bound is on the
rewrite relation, so the request for more depth cannot persist. -/
theorem exportedSessionReduce_complete {ds ns es extra root d rs t budget}
    (decoded : SessionReductionWire.input ds ns es extra root = some ⟨d,rs,t⟩)
    (hit : Executable.certifyTable ds ns es budget = true) (n : UInt64)
    (within : CheckedReduction.Within (TableAmbient.liftRules rs) n.toNat t) :
    SessionReductionWire.Answer d rs t (Executable.sessionReduce ds ns es extra root n) :=
  exportedSessionReduce_correct.completes _ _ _ _ _ _ _ _ decoded
    (CertifiedTableWire.sound CertifiedTableWire.correct
      (SessionReductionWire.input_table decoded) hit) n within

/-- The session variant checker accepts with status 1 only. -/
theorem exportedSessionVariantCheck_correct :
    SessionVariantCheckWire.Correct Executable.sessionVariantCheck :=
  SessionVariantCheckWire.correct

/-- Once `certifyTable` accepts the rules-only packet `ds ns es`, a family
accepted on a call that adds node rows to that packet is a complete set of
variants of the observations the rows denote, with exactly the proposed
substitutions on the variables of the observations. -/
theorem exportedSessionVariantCheck_certified
    {ds ns es extra roots family fuel work d rs q members budget}
    (decoded : SessionVariantCheckWire.input ds ns es extra roots family = some ⟨d,rs,q,members⟩)
    (hit : Executable.certifyTable ds ns es budget = true)
    (accepted : Executable.sessionVariantCheck ds ns es extra roots family fuel work = #[#[1]]) :
    ∃ rows, MaudeOperations.VariantReply (Rewriting.ruleRoot (TableAmbient.liftRules rs)) q [] rows ∧
      rows.length = members.length ∧
      ∀ pair ∈ members.zip rows, ∀ v, Rewriting.Observed q v →
        pair.2.subst.image v = pair.1.image v := by
  obtain ⟨_,can,_⟩ := CertifiedTableWire.sound CertifiedTableWire.correct
    (SessionVariantCheckWire.input_table decoded) hit
  exact exportedSessionVariantCheck_correct.accepted _ _ _ _ _ _ _ _ _ _ _ _ decoded accepted can

/-- On a canonical presentation the session variant checker accepts closed
families only, and a rejection names a clause of closedness that fails and
the member that violates it. On a range-restricted canonical presentation
there is a depth from which a call without a work limit never reports an
exhausted budget and accepts every closed family.

Known weak clause: that depth is only said to exist (`∃ k : Nat`), while the
argument is a 64-bit word, so the clause is empty if the depth exceeds
`2^64`. The depth that is proved to suffice (`VariantCertificate.threshold`)
is one more than the largest rewrite height among the terms the checker
normalizes, and those include the narrowing successors that the installed
unifier enumerates. Naming it here would pin the narrower, the reference
reducer and the unifier (about 260 further definitions), so it stays
existential. Acceptance and rejection are unaffected: they are exact at every
depth. -/
theorem exportedSessionVariantCheck_decides :
    SessionVariantCheckWire.Decides Executable.sessionVariantCheck :=
  SessionVariantCheckWire.decides

/-- Once `certifyTable` accepts the rules-only packet `ds ns es`, there is a
depth from which a call without a work limit replies with status 1 exactly
when the family is closed, and never with status 3. The depth is existential
for the reason given at `exportedSessionVariantCheck_decides`. -/
theorem exportedSessionVariantCheck_complete
    {ds ns es extra roots family d rs q members budget}
    (decoded : SessionVariantCheckWire.input ds ns es extra roots family = some ⟨d,rs,q,members⟩)
    (hit : Executable.certifyTable ds ns es budget = true) :
    ∃ k : Nat, ∀ fuel : UInt64, k ≤ fuel.toNat →
      Executable.sessionVariantCheck ds ns es extra roots family fuel 0 ≠ #[#[3]] ∧
      (Executable.sessionVariantCheck ds ns es extra roots family fuel 0 = #[#[1]] ↔
        VariantCertificate.Closed (Rewriting.ruleRoot (TableAmbient.liftRules rs)) q members) := by
  obtain ⟨bound,can,_⟩ := CertifiedTableWire.sound CertifiedTableWire.correct
    (SessionVariantCheckWire.input_table decoded) hit
  have decision := exportedSessionVariantCheck_decides _ _ _ _ _ _ _ _ _ _ decoded
  obtain ⟨k,enough⟩ := decision.accepts bound can
  exact ⟨k,fun fuel large => ⟨(enough fuel large).1,decision.closed fuel 0 can,(enough fuel large).2⟩⟩

/-- Floor: on a sorted table of constructor definitions the checked reducer
never declines. Every input gets its normal form, at every depth. -/
theorem exportedDefinitionReduce_ambient {ds ns es root n d t rs}
    (h : TableWire.input ds ns es #[root] = some ⟨d,rs,[t]⟩) (cls : ConstantDefinitions.Presentation rs)
    (typed : ∀ r ∈ rs, HasSort r.rhs r.lhs.rootSort) :
    GeneralReductionWire.Answer d rs t (Executable.checkedReduce ds ns es root n) := by
  have sorted := (DefinitionCertificate.sorted_iff cls).mpr typed
  have ok := (ConstantDefinitions.accepts_iff rs).mpr cls
  rcases CheckedReductionWire.correct.valid _ _ _ _ n _ _ _ h with ⟨u,packet,reply⟩ | ⟨_,reject,_⟩
  · exact ⟨u,packet,reply,fun extra => SignatureExtension.reduction extra rs (ConstantDefinitions.bound ok) t u reply⟩
  · simp [CheckedReductionWire.definitions,ok,sorted] at reject

/-- Floor: on a sorted table of constructor-pattern projections the checked
reducer never declines, including on kind-level contexts. -/
theorem exportedDestructorReduce_ambient {ds ns es root n d t rs}
    (h : TableWire.input ds ns es #[root] = some ⟨d,rs,[t]⟩) (cls : DestructorTable.Presentation rs)
    (typed : ∀ r ∈ rs, HasSort r.rhs r.lhs.rootSort) :
    GeneralReductionWire.Answer d rs t (Executable.checkedReduce ds ns es root n) := by
  have sorted := cls.sorted_iff.mpr typed
  rcases CheckedReductionWire.correct.valid _ _ _ _ n _ _ _ h with ⟨u,packet,reply⟩ | ⟨_,_,reject,_⟩
  · exact ⟨u,packet,reply,fun extra => SignatureExtension.reduction extra rs (TableDecrease.bound cls.decreasing) t u reply⟩
  · simp [CheckedReductionWire.destructors,(DestructorTable.accepts_iff rs).mpr cls,sorted] at reject

/-- The packet dictionary may contain only the query's symbols. Every reply
other than the decline word still covers caller solutions involving other
symbols. The hypothesis is one the caller observes. -/
theorem exportedTotalUnify_ambient {ds ns es d p}
    (decoded : TotalUnifyWire.input ds ns es = some ⟨d,p⟩)
    (answered : Executable.totalUnify ds ns es ≠ #[#[0]]) :
    ∃ answers, TotalUnifyWire.Packet.Decodes p (Executable.totalUnify ds ns es) answers ∧
      ∀ extra : Signature, (Outcome.complete (answers.map (SignatureExtension.liftSubst extra))).CorrectIn
        (SignatureExtension.query extra p) [] := by
  obtain ⟨answers,ok,hp | ⟨declined,_⟩⟩ := exportedTotalUnify_correct.valid _ _ _ _ _ decoded
  · exact ⟨answers,hp,fun extra => SignatureExtension.correctIn extra p [] ok⟩
  · exact (answered declined).elim

/-- A decodable query without solutions is never declined: its reply is the
bare status row of the empty family. -/
theorem exportedTotalUnify_unsatisfiable {ds ns es d p}
    (decoded : TotalUnifyWire.input ds ns es = some ⟨d,p⟩) (unsolvable : ¬ p.Satisfiable) :
    Executable.totalUnify ds ns es = #[#[1]] := by
  obtain ⟨answers,ok,reply⟩ := exportedTotalUnify_correct.valid _ _ _ _ _ decoded
  have empty : answers = [] := by
    cases answers with
    | nil => rfl
    | cons σ rest => exact (unsolvable ⟨σ,ok.mathematical.sound σ List.mem_cons_self⟩).elim
  subst empty
  rcases reply with hp | ⟨_,σ,hσ,_⟩
  · exact (TotalUnifyWire.Packet.decodes_nil p _).mp hp
  · exact (List.not_mem_nil hσ).elim

end Tamarin

open Lean Meta in
/-- Lean 4.36 compiles constructor indices using a runtime tag read. Check the
    exact primitive and its argument, and reduce the logical function on every
    constructor to check it returns the corresponding tag. -/
private def checkedCtorIndex (env : Environment) (name impl : Name) : MetaM Bool := do
  let some ind := isCtorIdxCore? env name | return false
  unless impl == name.str "_impl" && Compiler.getImplementedBy? env name == some impl &&
      ind.numCtors > 1 && !ind.isUnsafe && !Compiler.LCNF.isRuntimeBuiltinType ind.name do
    return false
  if ← isPropFormerType ind.type then return false
  let casesOn ← getConstInfo (mkCasesOnName ind.name)
  unless casesOn.levelParams.length > ind.levelParams.length do return false
  let some (.defnInfo logical) := env.find? name | return false
  let some (.defnInfo runtime) := env.find? impl | return false
  unless logical.safety == .safe && runtime.safety == .unsafe &&
      logical.levelParams == ind.levelParams && runtime.levelParams == ind.levelParams &&
      logical.type == runtime.type do return false
  let us := ind.levelParams.map mkLevelParam
  forallTelescope logical.type fun args result => do
    unless args.size == ind.numParams + ind.numIndices + 1 && result == mkConst ``Nat do
      return false
    let value := args.back!
    let ty := mkAppN (mkConst ind.name us) args.pop
    unless (← inferType value) == ty do return false
    let tag := mkApp2 (mkConst ``getObjTagNat [← getLevel ty]) ty value
    unless runtime.value == (← mkLambdaFVars args tag) do return false
    for ctorName in ind.ctors do
      let ctor ← getConstInfoCtor ctorName
      let agrees ← forallTelescope ctor.type fun fields target => do
        let constructed := mkAppN (mkConst ctorName us) fields
        let idx := mkApp (mkAppN (mkConst name us) target.getAppArgs) constructed
        withTransparency .all <| isDefEq idx (mkNatLit ctor.cidx)
      unless agrees do return false
    return true

/-!
CI audit of project declarations, including private helpers and
helpers outside the Tamarin namespace. Keep this in the root module so it
sees every specification and runtime import.
Only Lean's standard logical axioms are allowed. In particular, `sorryAx`,
custom solver axioms, and native-evaluation proof shortcuts fail CI verification.
The audit rejects project uses of `implemented_by`, `extern`, value initializers,
and unsafe definitions. Lean's generated constructor tags must pass the checks
above to qualify for the sole exception for `implemented_by` and unsafe code.
Checked `csimp` equalities remain available for compiler optimizations.
The C ABI symbol mapping is pinned for every export. A contract export is
mentioned by a theorem of this file. A proposer export is mentioned by none:
nothing is promised about its output, and it is listed only so that no export
exists without review. Adding an ABI entry requires reviewing its class.
Bundled Init/Std/Lean definitions remain trusted, along with the Lean compiler,
runtime, and Rust/C FFI. This is not a sandbox against malicious metaprograms:
an imported module could redefine this command. `Tests/ExportAudit.lean` repeats
these checks on the compiled modules from outside and rejects such modules.
Only that audit compares the contract with its records: the exports and the
statements of the theorems of this file with `ExportManifest.txt`, and every
definition those statements depend on with `SpecManifest.txt`. This command
checks neither. `Tests/check_audit.py` checks that the two export lists below and
the manifest name the same exports in the same classes.
-/
open Lean in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  -- Exports with a contract: each is mentioned by a theorem of this file.
  let contractExports : List (Name × Name) := [
    (``Tamarin.Executable.checkedReduce, `tamarin_checked_reduce),
    (``Tamarin.Executable.unpackConjunction, `tamarin_unpack_conjunction),
    (``Tamarin.Executable.totalUnify, `tamarin_total_unify),
    (``Tamarin.Executable.totalUnifyExists, `tamarin_total_unify_exists),
    (``Tamarin.Executable.totalMatch, `tamarin_total_match),
    (``Tamarin.Executable.totalMatchExists, `tamarin_total_match_exists),
    (``Tamarin.Executable.pathReduce, `tamarin_path_reduce),
    (``Tamarin.Executable.certifyTable, `tamarin_certify_table),
    (``Tamarin.Executable.sessionReduce, `tamarin_session_reduce),
    (``Tamarin.Executable.sessionVariantCheck, `tamarin_session_variant_check),
    (``Tamarin.Executable.checkedVariants, `tamarin_checked_variants)]
  -- Proposer exports carry no contract. The caller uses their output only as a
  -- proposal that `tamarin_session_variant_check` has to accept, so no theorem of
  -- this file may mention them. Their theorems are in `TamarinProposers.lean`.
  let proposerExports : List (Name × Name) := [
    (``Tamarin.Executable.flatACEqual, `tamarin_flat_ac_equal),
    (``Tamarin.Executable.flatACResidual, `tamarin_flat_ac_residual),
    (``Tamarin.Executable.pairingVariants, `tamarin_pairing_variants),
    (``Tamarin.Executable.acPivot, `tamarin_ac_pivot),
    (``Tamarin.Executable.selectJoinedVariants, `tamarin_select_joined_variants),
    (``Tamarin.Executable.dhExponentImages, `tamarin_dh_exponent_images),
    (``Tamarin.Executable.dhTowerImages, `tamarin_dh_tower_images),
    (``Tamarin.Executable.dhPeerImages, `tamarin_dh_peer_images),
    (``Tamarin.Executable.signedGraphVariants, `tamarin_signed_graph_variants),
    (``Tamarin.Executable.reductionGraph, `tamarin_reduction_graph),
    (``Tamarin.Executable.acSubgroups, `tamarin_ac_subgroups),
    (``Tamarin.Executable.openMatchSelect, `tamarin_open_match_select),
    (``Tamarin.Executable.acBagMatch, `tamarin_ac_bag_match),
    (``Tamarin.Executable.acBagTypedMatch, `tamarin_ac_bag_typed_match),
    (``Tamarin.Executable.matchSizeExcludes, `tamarin_match_size_excludes),
    (``Tamarin.Executable.collectorPossible, `tamarin_collector_possible),
    (``Tamarin.Executable.sortedACMatch, `tamarin_sorted_ac_match),
    (``Tamarin.Executable.flatACMatch, `tamarin_flat_ac_match),
    (``Tamarin.Executable.factorRefutes, `tamarin_factor_refutes),
    (``Tamarin.Executable.variantOverlapAgrees, `tamarin_variant_overlap_agrees),
    (``Tamarin.Executable.checkFactors, `tamarin_check_factors),
    (``Tamarin.Executable.operandRefine, `tamarin_operand_refine),
    (``Tamarin.Executable.maskedOperandUnify, `tamarin_masked_operand_unify),
    (``Tamarin.Executable.operandUnify, `tamarin_operand_unify),
    (``Tamarin.Executable.projectAnswers, `tamarin_project_answers),
    (``Tamarin.Executable.xorBranches, `tamarin_xor_branches),
    (``Tamarin.Executable.xorMatchings, `tamarin_xor_matchings),
    (``Tamarin.Executable.mixedCancellationRows, `tamarin_mixed_cancellation_rows),
    (``Tamarin.Executable.binaryCancellationRows, `tamarin_binary_cancellation_rows),
    (``Tamarin.Executable.xorOdd, `tamarin_xor_odd),
    (``Tamarin.Executable.residualRigid, `tamarin_residual_rigid),
    (``Tamarin.Executable.residualVariable, `tamarin_residual_variable),
    (``Tamarin.Executable.commOrientations, `tamarin_comm_orientations),
    (``Tamarin.Executable.cancelCommon, `tamarin_cancel_common),
    (``Tamarin.Executable.groundVariant, `tamarin_ground_variant),
    (``Tamarin.Executable.reduceRuleSlot, `tamarin_reduce_rule_slot),
    (``Tamarin.Executable.excludeACFactors, `tamarin_exclude_ac_factors),
    (``Tamarin.Executable.excludeRoot, `tamarin_exclude_root),
    (``Tamarin.Executable.constructorVariant, `tamarin_constructor_variant),
    (``Tamarin.Executable.generalVariants, `tamarin_general_variants)]
  let expectedExports := contractExports ++ proposerExports
  for (name, symbol) in expectedExports do
    unless getExportNameFor? env name == some symbol do
      throwError "Required verified export {name} must map to {symbol}"
  -- A theorem of this module is a contract statement. None may speak about a
  -- proposer, and every contract export needs one.
  let mut stated : NameSet := {}
  for (name, info) in env.constants.map₂.toList do
    if let .thmInfo t := info then
      for used in t.type.getUsedConstants do
        if proposerExports.any (·.1 == used) then
          throwError "contract theorem {name} mentions the proposer export {used}"
        stated := stated.insert used
  for (name, symbol) in contractExports do
    unless stated.contains name do
      throwError "contract export {name} ({symbol}) is mentioned by no theorem of this module"
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    let fromTrustedModule := match env.getModuleIdxFor? name with
      | none => false
      | some idx =>
        let root := moduleNames[idx.toNat]!.getRoot
        root == `Init || root == `Std || root == `Lean
    if !fromTrustedModule || (`Tamarin).isPrefixOf (privateToUserName name) then
      checked := checked + 1
      if let some symbol := getExportNameFor? env name then
        unless expectedExports.contains (name, symbol) do
          throwError "Unapproved project export {name} maps to {symbol}"
      if let some replacement := Compiler.getImplementedBy? env name then
        unless ← Elab.Command.liftTermElabM <| checkedCtorIndex env name replacement do
          throwError "{name} has unchecked implemented_by replacement {replacement}"
      if isExtern env name then
        throwError "{name} has unchecked extern implementation"
      if let some initializer := getInitFnNameFor? env name then
        throwError "{name} has unchecked runtime initializer {initializer}"
      if info.isUnsafe then
        unless ← Elab.Command.liftTermElabM <| checkedCtorIndex env name.getPrefix name do
          throwError "{name} is an unsafe project declaration"
      for ax in ← collectAxioms name do
        unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
          throwError "{name} depends on unapproved axiom {ax}"
  if checked == 0 then
    throwError "No Tamarin declarations found by the axiom audit"
  logInfo m!"Axiom and executable-replacement audit passed for {checked} project declarations"
