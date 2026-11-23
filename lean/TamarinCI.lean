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
import Tamarin.UnifierNames
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
export, one of the ten exports whose reply the Rust backend uses as the
answer, or states a property of the specification itself:

* `totalUnify`, `totalUnifyExists`, `nameUnifiers`, `unpackConjunction`,
  `totalMatch`, `totalMatchExists`;
* `certifyTable`, `sessionReduce`, `pathReduce`;
* `sessionVariantCheck`.

A statement here says what a reply means in terms of the decoded packet and
the rewrite relation. No statement names a search, a classifier or a
reference procedure, so declining is limited only where a semantic condition
or a concrete packet does it. The remaining exports are proposers and carry
no contract. Their theorems, and the coverage statements that were stated
through reference procedures, are in `TamarinProposers.lean`, which is not
pinned.
-/

namespace Tamarin

/-! An export that can be interrupted receives the caller's `poll`. When the
first reply is `false` it is the search under the default instance, about
which the library's theorems speak (`Interrupt.run_quiet`). -/

private theorem totalUnify_quiet {poll : Unit → Bool} (quiet : poll () = false) :
    Executable.totalUnify poll = TotalUnifyWire.run := by
  funext ds ns es
  exact Interrupt.run_quiet quiet _ _

private theorem totalUnifyExists_quiet {poll : Unit → Bool} (quiet : poll () = false) :
    Executable.totalUnifyExists poll = TotalUnifyWire.runExists := by
  funext ds ns es
  exact Interrupt.run_quiet quiet _ _

private theorem pathReduce_quiet {poll : Unit → Bool} (quiet : poll () = false) :
    Executable.pathReduce poll = PathReductionWire.run := by
  funext ds ns es root n
  exact Interrupt.run_quiet quiet _ _

/-- A written term is not the interrupted reply. -/
private theorem emit_answers {d : TotalUnifyWire.Dictionary} (u : Term d.sig) :
    CheckedReductionWire.emit u ≠ #[#[4]] := by
  unfold CheckedReductionWire.emit
  split <;> simp

private theorem session_answers {d : TotalUnifyWire.Dictionary} (u : Term (TableAmbient.sig d)) :
    SessionWire.emit u ≠ #[#[4]] := by
  unfold SessionWire.emit
  split <;> simp

private theorem sessionReduce_quiet {poll : Unit → Bool} (quiet : poll () = false) :
    Executable.sessionReduce poll = SessionReductionWire.run := by
  funext ds ns es extra root n
  exact Interrupt.run_quiet quiet _ _

private theorem sessionVariantCheck_quiet {poll : Unit → Bool} (quiet : poll () = false) :
    Executable.sessionVariantCheck poll = SessionVariantCheckWire.run := by
  funext ds ns es extra roots family fuel work
  exact Interrupt.run_quiet quiet _ _

/-- Every arity-correct query has a complete family on its declared signature,
and the reply is that family fully decoded unless one of its answers adds at
least `2^64 - bound` distinct variables to the query, `bound` being the least
identifier above the variables of the query. Malformed input has the same
decline status. -/
theorem exportedTotalUnify_correct {poll : Unit → Bool} (quiet : poll () = false) :
    TotalUnifyWire.Packet.Correct (Executable.totalUnify poll) :=
  totalUnify_quiet quiet ▸ TotalUnifyWire.Packet.correct

/-- The interrupted reply `#[#[4]]` is given exactly when the caller's `poll`
says stop. It carries no answer. -/
theorem exportedTotalUnify_interrupted (poll : Unit → Bool) (ds ns es) :
    Executable.totalUnify poll ds ns es = #[#[4]] ↔ poll () = true := by
  constructor
  · intro reply
    cases quiet : poll () with
    | true => rfl
    | false =>
      exfalso
      cases decoded : TotalUnifyWire.input ds ns es with
      | none =>
        rw [(exportedTotalUnify_correct quiet).malformed _ _ _ decoded] at reply
        cases reply
      | some packet =>
        obtain ⟨d,p⟩ := packet
        obtain ⟨_,_,⟨rows,shape,_⟩ | ⟨declined,_⟩⟩ := (exportedTotalUnify_correct quiet).valid _ _ _ _ _ decoded
        · rw [reply] at shape
          cases shape
        · rw [declined] at reply
          cases reply
  · exact fun stop => Interrupt.run_stopped stop _ _

/-- The decision export answers 1 exactly when the decoded query has a
unifier, 2 exactly when it has none, and 0 exactly when the packet does not
decode. It never declines a decoded query. -/
theorem exportedTotalUnifyExists_correct {poll : Unit → Bool} (quiet : poll () = false) :
    TotalUnifyWire.ExistsCorrect (Executable.totalUnifyExists poll) :=
  totalUnifyExists_quiet quiet ▸ TotalUnifyWire.existsCorrect

/-- The interrupted reply 4 is given exactly when the caller's `poll` says
stop. It decides nothing. -/
theorem exportedTotalUnifyExists_interrupted (poll : Unit → Bool) (ds ns es) :
    Executable.totalUnifyExists poll ds ns es = 4 ↔ poll () = true := by
  constructor
  · intro reply
    cases quiet : poll () with
    | true => rfl
    | false =>
      exfalso
      cases decoded : TotalUnifyWire.input ds ns es with
      | none =>
        rw [(exportedTotalUnifyExists_correct quiet).malformed _ _ _ decoded] at reply
        cases reply
      | some packet =>
        obtain ⟨d,p⟩ := packet
        rcases (exportedTotalUnifyExists_correct quiet).valid _ _ _ _ _ decoded with ⟨yes,_⟩ | ⟨no,_⟩
        · rw [yes] at reply
          cases reply
        · rw [no] at reply
          cases reply
  · exact fun stop => Interrupt.run_stopped stop _ _

/-- The decision also holds in the caller's entire signature, even when only
the declarations occurring in the terms crossed the wire. -/
theorem exportedTotalUnifyExists_ambient {poll : Unit → Bool} (quiet : poll () = false) {ds ns es d p}
    (decoded : TotalUnifyWire.input ds ns es = some ⟨d,p⟩) (extra : Signature) :
    Executable.totalUnifyExists poll ds ns es = 1 ↔
      ∃ σ, (SignatureExtension.query extra p).Solves σ := by
  obtain ⟨answers,ok,_⟩ := (exportedTotalUnify_correct quiet).valid _ _ _ _ _ decoded
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
  rcases (exportedTotalUnifyExists_correct quiet).valid _ _ _ _ _ decoded with ⟨yes,hit⟩ | ⟨no,miss⟩
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

/-- What `true` means: the packet decodes and its table is certified, that is,
range restricted, a canonical presentation (terminating and confluent modulo
the declared C and AC laws) and with the finite variant property, over the
dictionary of the packet extended by all ambient names.

`false` carries no information in general. It is the reply to a malformed
packet, and the checker may also return it for a table that is certified:
termination, confluence and the finite variant property are undecidable, so
no statement limits declining on every table. It is limited on the class of
`exportedCertifyTable_subterm` and on the three concrete packets below. Which
other user tables are accepted is guarded by the corpus, not here. -/
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

/-- The class the certifier has to accept. A decoded table is certified, at
every budget, when it consists of constructor-pattern rules whose results are
subterms or constants (`SubtermTable.Presentation`): every left side is a
free application whose arguments contain no head of a left side; the rules of
one head either all return the subterm at one common position below the root
of their left side, or all return one closed term without a head of a left
side that has fewer symbols than the left side; and every result has the sort
of its left side. These are the equations of pairing, symmetric and
asymmetric encryption and signatures, and user equations of that shape.

Outside this class and the three packets below, `false` stays unlimited:
termination, confluence and the finite variant property are undecidable, so
no certifier accepts every certified table. -/
theorem exportedCertifyTable_subterm {ds ns es d rs q}
    (decoded : TableWire.input ds ns es #[] = some ⟨d,rs,q⟩)
    (cls : SubtermTable.Presentation rs) (fuel : UInt64) :
    Executable.certifyTable ds ns es fuel = true :=
  CertifiedTableWire.subterm decoded cls fuel

/-- Coverage floors: these three production packets (XOR with the destructor
table, the joint group table, the bilinear pairing table) are accepted at
budget zero. -/
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

/-- On any decoded table a status 1 reply of the single-path reducer is an
irreducible reduct that keeps the sorts of the input. Convergence of the table
is not assumed, so the reply need not be the only normal form. Status 2 is
returned only for a table that is not range restricted or when an irreducible
reduct lost a sort, and status 3 only while some rewrite path is at least as
long as the depth. -/
theorem exportedPathReduce_correct {poll : Unit → Bool} (quiet : poll () = false) :
    PathReductionWire.Correct (Executable.pathReduce poll) :=
  pathReduce_quiet quiet ▸ PathReductionWire.correct

/-- The interrupted reply `#[#[4]]` is given exactly when the caller's `poll`
says stop. It carries no answer. -/
theorem exportedPathReduce_interrupted (poll : Unit → Bool) (ds ns es root n) :
    Executable.pathReduce poll ds ns es root n = #[#[4]] ↔ poll () = true := by
  constructor
  · intro reply
    cases quiet : poll () with
    | true => rfl
    | false =>
      exfalso
      rw [pathReduce_quiet quiet] at reply
      unfold PathReductionWire.run at reply
      repeat' split at reply
      all_goals first
        | exact emit_answers _ reply
        | (simp at reply; done)
  · exact fun stop => Interrupt.run_stopped stop _ _

/-- The session reducer reads the terms of a call from further node rows, over
the table of the rules-only packet and all ambient names. -/
theorem exportedSessionReduce_correct {poll : Unit → Bool} (quiet : poll () = false) :
    SessionReductionWire.Correct (Executable.sessionReduce poll) :=
  sessionReduce_quiet quiet ▸ SessionReductionWire.correct

/-- The interrupted reply `#[#[4]]` is given exactly when the caller's `poll`
says stop. It carries no answer. -/
theorem exportedSessionReduce_interrupted (poll : Unit → Bool) (ds ns es extra root n) :
    Executable.sessionReduce poll ds ns es extra root n = #[#[4]] ↔ poll () = true := by
  constructor
  · intro reply
    cases quiet : poll () with
    | true => rfl
    | false =>
      exfalso
      rw [sessionReduce_quiet quiet] at reply
      unfold SessionReductionWire.run at reply
      repeat' split at reply
      all_goals first
        | exact session_answers _ reply
        | (simp at reply; done)
  · exact fun stop => Interrupt.run_stopped stop _ _

/-- Once `certifyTable` accepts the rules-only packet `ds ns es`, every call
that adds node rows to that packet replies with the unique normal form of the
term the rows denote, or with a request for more depth. The certificate is
the one of the rules-only packet. -/
theorem exportedSessionReduce_certified {poll : Unit → Bool} (quiet : poll () = false)
    {ds ns es extra root n d rs t budget}
    (decoded : SessionReductionWire.input ds ns es extra root = some ⟨d,rs,t⟩)
    (hit : Executable.certifyTable ds ns es budget = true) :
    SessionReductionWire.Answer d rs t (Executable.sessionReduce poll ds ns es extra root n) ∨
      Executable.sessionReduce poll ds ns es extra root n = #[#[3]] :=
  (exportedSessionReduce_correct quiet).valid _ _ _ _ _ _ _ _ _ decoded
    (CertifiedTableWire.sound CertifiedTableWire.correct
      (SessionReductionWire.input_table decoded) hit)

/-- Once `certifyTable` accepts the rules-only packet, every call on that
packet replies with the unique normal form at every depth that bounds all
rewrite paths from its term under the lifted rules. The bound is on the
rewrite relation, so the request for more depth cannot persist. -/
theorem exportedSessionReduce_complete {poll : Unit → Bool} (quiet : poll () = false)
    {ds ns es extra root d rs t budget}
    (decoded : SessionReductionWire.input ds ns es extra root = some ⟨d,rs,t⟩)
    (hit : Executable.certifyTable ds ns es budget = true) (n : UInt64)
    (within : CheckedReduction.Within (TableAmbient.liftRules rs) n.toNat t) :
    SessionReductionWire.Answer d rs t (Executable.sessionReduce poll ds ns es extra root n) :=
  (exportedSessionReduce_correct quiet).completes _ _ _ _ _ _ _ _ decoded
    (CertifiedTableWire.sound CertifiedTableWire.correct
      (SessionReductionWire.input_table decoded) hit) n within

/-- The session variant checker accepts with status 1 only. -/
theorem exportedSessionVariantCheck_correct {poll : Unit → Bool} (quiet : poll () = false) :
    SessionVariantCheckWire.Correct (Executable.sessionVariantCheck poll) :=
  sessionVariantCheck_quiet quiet ▸ SessionVariantCheckWire.correct

/-- The interrupted reply `#[#[4]]` is given exactly when the caller's `poll`
says stop. It decides nothing about the family. -/
theorem exportedSessionVariantCheck_interrupted (poll : Unit → Bool)
    (ds ns es extra roots family fuel work) :
    Executable.sessionVariantCheck poll ds ns es extra roots family fuel work = #[#[4]] ↔
      poll () = true := by
  constructor
  · intro reply
    cases quiet : poll () with
    | true => rfl
    | false =>
      exfalso
      cases decoded : SessionVariantCheckWire.input ds ns es extra roots family with
      | none =>
        rw [(exportedSessionVariantCheck_correct quiet).malformed _ _ _ _ _ _ fuel work decoded] at reply
        cases reply
      | some packet =>
        obtain ⟨d,rs,q,members⟩ := packet
        rcases (exportedSessionVariantCheck_correct quiet).status _ _ _ _ _ _ fuel work _ _ _ _ decoded with
          yes | ⟨reason,index,no⟩ | out
        · rw [yes] at reply
          cases reply
        · rw [no] at reply
          cases reply
        · rw [out] at reply
          cases reply
  · exact fun stop => Interrupt.run_stopped stop _ _

/-- Once `certifyTable` accepts the rules-only packet `ds ns es`, a family
accepted on a call that adds node rows to that packet is a complete set of
variants of the observations the rows denote, with exactly the proposed
substitutions on the variables of the observations. -/
theorem exportedSessionVariantCheck_certified {poll : Unit → Bool} (quiet : poll () = false)
    {ds ns es extra roots family fuel work d rs q members budget}
    (decoded : SessionVariantCheckWire.input ds ns es extra roots family = some ⟨d,rs,q,members⟩)
    (hit : Executable.certifyTable ds ns es budget = true)
    (accepted : Executable.sessionVariantCheck poll ds ns es extra roots family fuel work = #[#[1]]) :
    ∃ rows, MaudeOperations.VariantReply (Rewriting.ruleRoot (TableAmbient.liftRules rs)) q [] rows ∧
      rows.length = members.length ∧
      ∀ pair ∈ members.zip rows, ∀ v, Rewriting.Observed q v →
        pair.2.subst.image v = pair.1.image v := by
  obtain ⟨_,can,_⟩ := CertifiedTableWire.sound CertifiedTableWire.correct
    (SessionVariantCheckWire.input_table decoded) hit
  exact (exportedSessionVariantCheck_correct quiet).accepted _ _ _ _ _ _ _ _ _ _ _ _ decoded accepted can

/-- On a canonical presentation the session variant checker accepts closed
families only, and a rejection names a clause of closedness that fails and
the member that violates it. A reply with status 3 is limited: a term the
check has to normalize has a rewrite path at least as long as the depth, or
the work limit is nonzero and below the number of positions at which the
narrowing layers of the members look for steps (`exhausts`).

The terms a check has to normalize (`VariantCertificate.Demand`) are the
terms of the query, their instances by the members, and the values of the
most general narrowing successors of the members. All of this is stated
through the rewrite relation and subsumption modulo the declared laws: no
unifier, narrower or reducer is named. -/
theorem exportedSessionVariantCheck_decides {poll : Unit → Bool} (quiet : poll () = false) :
    SessionVariantCheckWire.Decides (Executable.sessionVariantCheck poll) :=
  sessionVariantCheck_quiet quiet ▸ SessionVariantCheckWire.decides

/-- Once `certifyTable` accepts the rules-only packet `ds ns es`, a call
whose depth exceeds every rewrite path from the terms the check has to
normalize, and whose work limit is zero or covers the narrowing layers of the
members, never replies with status 3, and replies with status 1 exactly when
the family is closed. -/
theorem exportedSessionVariantCheck_complete {poll : Unit → Bool} (quiet : poll () = false)
    {ds ns es extra roots family d rs q members budget}
    (decoded : SessionVariantCheckWire.input ds ns es extra roots family = some ⟨d,rs,q,members⟩)
    (hit : Executable.certifyTable ds ns es budget = true) (fuel work : UInt64)
    (deep : ∀ t, VariantCertificate.Demand (Rewriting.ruleRoot (TableAmbient.liftRules rs)) q members t →
      CheckedReduction.Within (TableAmbient.liftRules rs) fuel.toNat t)
    (funded : work = 0 ∨ ¬VariantCertificate.Overcharged
      (Rewriting.ruleRoot (TableAmbient.liftRules rs)) q members work.toNat) :
    Executable.sessionVariantCheck poll ds ns es extra roots family fuel work ≠ #[#[3]] ∧
      (Executable.sessionVariantCheck poll ds ns es extra roots family fuel work = #[#[1]] ↔
        VariantCertificate.Closed (Rewriting.ruleRoot (TableAmbient.liftRules rs)) q members) := by
  obtain ⟨bound,can,_⟩ := CertifiedTableWire.sound CertifiedTableWire.correct
    (SessionVariantCheckWire.input_table decoded) hit
  have decision := exportedSessionVariantCheck_decides quiet _ _ _ _ _ _ _ _ _ _ decoded
  have open_ : Executable.sessionVariantCheck poll ds ns es extra roots family fuel work ≠ #[#[3]] := by
    intro out
    rcases decision.exhausts fuel work can out with ⟨t,needed,long⟩ | ⟨limited,short⟩
    · exact long (deep t needed)
    · exact funded.elim limited (fun enough => enough short)
  refine ⟨open_,decision.closed fuel work can,fun closed => ?_⟩
  rcases (exportedSessionVariantCheck_correct quiet).status _ _ _ _ _ _ fuel work _ _ _ _ decoded with
    yes | ⟨reason,index,no⟩ | out
  · exact yes
  · exfalso
    obtain ⟨i,_,⟨_,σ,at_i,bad⟩ | ⟨_,bad⟩ | ⟨_,σ,at_i,bad⟩ | ⟨_,bad⟩⟩ :=
      decision.rejects fuel work reason index can no
    · exact bad (closed.normal σ (List.mem_of_getElem? at_i))
    · exact bad closed.start
    · exact bad (closed.step σ (List.mem_of_getElem? at_i))
    · exact bad ⟨bound,(VariantCertificate.nonvar_iff _).mp (VariantCertificate.nonvar_canonical can)⟩
  · exact absurd out open_

/-- The limit on status 3 is not empty: on a range-restricted canonical
presentation one depth bounds every rewrite path from every term a check of
the family has to normalize. -/
theorem variantDemand_bounded {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym]
    [DecidableEq s.ACSym] [DecidableEq s.Atom] {rules : List (Equation s)}
    (bound : ReferenceReduction.Bound rules)
    (canonical : MaudeOperations.CanonicalPresentation (Rewriting.ruleRoot rules)) (q : List (Term s))
    (family : List (Substitution s)) :
    ∃ k : Nat, ∀ t, VariantCertificate.Demand (Rewriting.ruleRoot rules) q family t →
      CheckedReduction.Within rules k t :=
  ⟨_,VariantCertificate.demand_within canonical ((CheckedReduction.rangeBound_iff rules).mpr bound)
    (VariantCertificate.nonvar_canonical canonical) q family⟩

/-- The packet dictionary may contain only the query's symbols. Every reply
other than the decline word still covers caller solutions involving other
symbols. The hypothesis is one the caller observes. -/
theorem exportedTotalUnify_ambient {poll : Unit → Bool} (quiet : poll () = false) {ds ns es d p}
    (decoded : TotalUnifyWire.input ds ns es = some ⟨d,p⟩)
    (answered : Executable.totalUnify poll ds ns es ≠ #[#[0]]) :
    ∃ answers, TotalUnifyWire.Packet.Decodes p (Executable.totalUnify poll ds ns es) answers ∧
      ∀ extra : Signature, (Outcome.complete (answers.map (SignatureExtension.liftSubst extra))).CorrectIn
        (SignatureExtension.query extra p) [] := by
  obtain ⟨answers,ok,hp | ⟨declined,_⟩⟩ := (exportedTotalUnify_correct quiet).valid _ _ _ _ _ decoded
  · exact ⟨answers,hp,fun extra => SignatureExtension.correctIn extra p [] ok⟩
  · exact (answered declined).elim

/-- A decodable query without solutions is never declined: its reply is the
bare status row of the empty family. -/
theorem exportedTotalUnify_unsatisfiable {poll : Unit → Bool} (quiet : poll () = false) {ds ns es d p}
    (decoded : TotalUnifyWire.input ds ns es = some ⟨d,p⟩) (unsolvable : ¬ p.Satisfiable) :
    Executable.totalUnify poll ds ns es = #[#[1]] := by
  obtain ⟨answers,ok,reply⟩ := (exportedTotalUnify_correct quiet).valid _ _ _ _ _ decoded
  have empty : answers = [] := by
    cases answers with
    | nil => rfl
    | cons σ rest => exact (unsolvable ⟨σ,ok.mathematical.sound σ List.mem_cons_self⟩).elim
  subst empty
  rcases reply with hp | ⟨_,σ,hσ,_⟩
  · exact (TotalUnifyWire.Packet.decodes_nil p _).mp hp
  · exact (List.not_mem_nil hσ).elim

/-- The tables of the naming export name the variables that a family of
unifiers adds to its query. A reply of the unifier that decodes to a family
of a query is read through them (`UnifierNames.apply`), and when it can be
read the reading decodes to a family that is the given one, or its members
without a variable of the sort of natural numbers, up to an injective
renaming of the range of each member. Every variable of the range has a
label that no query variable of its sort has. Without a proposal it has the
hint `0` and an index of no query variable, which is above every index of
the query unless the caller settled for less. The export does not see the
reply, and nothing is assumed about what the caller tells it. -/
theorem exportedNameUnifiers_correct : UnifierNames.Correct Executable.nameUnifiers :=
  UnifierNames.correct

/-- The reply of the unifier read through the tables of the naming export is
a complete family of unifiers of the query, with every variable of its range
named apart from the query. The hypothesis is one the caller observes: its
reader succeeded. -/
theorem exportedNameUnifiers_total {poll : Unit → Bool} (quiet : poll () = false) {ds ns es d p}
    (decoded : TotalUnifyWire.input ds ns es = some ⟨d,p⟩)
    (names heads : Array UInt64) (ranges proposal : Array (Array UInt64)) (low : Bool) {named}
    (read : UnifierNames.apply (Executable.nameUnifiers names heads ranges proposal true low) true
      (Executable.totalUnify poll ds ns es) = some named) :
    ∃ answers, UnifierNames.Decodes p named answers ∧
      (Outcome.complete answers).CorrectIn p [] ∧
      (answers ≠ [] → UnifierNames.Labelled names p) ∧
      (∀ σ ∈ answers, UnifierNames.Fresh names p σ) ∧
      (proposal = #[] → ∀ σ ∈ answers, UnifierNames.Unused names p σ) ∧
      (proposal = #[] → low = false → ∀ σ ∈ answers, UnifierNames.Above names p σ) := by
  obtain ⟨raw,ok,hp | ⟨declined,_⟩⟩ := (exportedTotalUnify_correct quiet).valid _ _ _ _ _ decoded
  · obtain ⟨answers,packet,labelled,refines,fresh,unused,above⟩ :=
      exportedNameUnifiers_correct.valid _ _ _ names heads ranges proposal true low _ _ _ raw named
        decoded hp read
    exact ⟨answers,packet,refines.preserves_correct ok.mathematical,labelled,fresh,unused,above⟩
  · rw [declined,UnifierNames.apply_declined] at read
    cases read

/-- For a module without the sort of natural numbers the reading leaves out
the members with a variable of that sort. It still decides every solution
whose images have no such variable: such a solution solves the query exactly
when it is an instance of a member that is read. -/
theorem exportedNameUnifiers_natFree {poll : Unit → Bool} (quiet : poll () = false) {ds ns es d p}
    (decoded : TotalUnifyWire.input ds ns es = some ⟨d,p⟩)
    (names heads : Array UInt64) (ranges proposal : Array (Array UInt64)) (low : Bool) {named}
    (read : UnifierNames.apply (Executable.nameUnifiers names heads ranges proposal false low) false
      (Executable.totalUnify poll ds ns es) = some named) :
    ∃ answers, UnifierNames.Decodes p named answers ∧
      (∀ σ ∈ answers, DomainRestricted p σ) ∧
      (∀ ρ : Substitution d.sig, (∀ v, p.Occurs v → UnavailableSort.marked .nat (ρ.image v) = false) →
        (p.Solves ρ ↔ ∃ σ ∈ answers, Substitution.InstanceOn p.Occurs ρ σ)) ∧
      (answers ≠ [] → UnifierNames.Labelled names p) ∧
      (∀ σ ∈ answers, UnifierNames.Fresh names p σ) ∧
      (proposal = #[] → ∀ σ ∈ answers, UnifierNames.Unused names p σ) ∧
      (proposal = #[] → low = false → ∀ σ ∈ answers, UnifierNames.Above names p σ) := by
  obtain ⟨raw,ok,hp | ⟨declined,_⟩⟩ := (exportedTotalUnify_correct quiet).valid _ _ _ _ _ decoded
  · obtain ⟨answers,packet,labelled,refines,fresh,unused,above⟩ :=
      exportedNameUnifiers_correct.valid _ _ _ names heads ranges proposal false low _ _ _ raw named
        decoded hp read
    refine ⟨answers,packet,refines.domain,fun ρ clean => ?_,labelled,fresh,unused,above⟩
    rw [UnavailableSort.filterNat_iff p ok.mathematical ρ clean]
    exact refines.equivalent ρ
  · rw [declined,UnifierNames.apply_declined] at read
    cases read

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
    (``Tamarin.Executable.unpackConjunction, `tamarin_unpack_conjunction),
    (``Tamarin.Executable.totalUnify, `tamarin_total_unify),
    (``Tamarin.Executable.totalUnifyExists, `tamarin_total_unify_exists),
    (``Tamarin.Executable.nameUnifiers, `tamarin_name_unifiers),
    (``Tamarin.Executable.totalMatch, `tamarin_total_match),
    (``Tamarin.Executable.totalMatchExists, `tamarin_total_match_exists),
    (``Tamarin.Executable.pathReduce, `tamarin_path_reduce),
    (``Tamarin.Executable.certifyTable, `tamarin_certify_table),
    (``Tamarin.Executable.sessionReduce, `tamarin_session_reduce),
    (``Tamarin.Executable.sessionVariantCheck, `tamarin_session_variant_check)]
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
    (``Tamarin.Executable.checkedVariants, `tamarin_checked_variants),
    (``Tamarin.Executable.generalVariants, `tamarin_general_variants),
    (``Tamarin.Executable.foldVariants, `tamarin_fold_variants),
    (``Tamarin.Executable.applyNames, `tamarin_apply_names)]
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
