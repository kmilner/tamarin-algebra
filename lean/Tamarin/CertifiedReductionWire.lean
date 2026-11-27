import Tamarin.CertifiedReduction

/-! Reduction along one rewrite path. On a table accepted by the certifier
every path ends in the same normal form, so nothing else has to be explored.
Status 1 carries that normal form, 3 requests more rewrite depth, and 0
denotes a malformed or unrepresentable packet. The caller is responsible for
having certified the table of the packet. -/
namespace Tamarin.CertifiedReductionWire
open MaudeOperations Rewriting
variable [Interrupt]

/-- Local normalization, which revisits only rewritten subterms. When its
bound runs out, the outermost path is followed instead. -/
def path {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym]
    [DecidableEq s.Atom] (rs : Problem s) (fuel : Nat) (t : Term s) : Option (Term s) :=
  match ReferenceReduction.normalize rs fuel t with
  | some u => some u
  | none => ReferenceReduction.follow rs fuel t

def run (ds : Array UInt64) (ns : Array (Array UInt64)) (pairs : Array UInt64) (root fuel : UInt64) :
    Array (Array UInt64) :=
  match TableWire.input ds ns pairs #[root] with
  | some ⟨_,rs,[t]⟩ =>
    match path rs fuel.toNat t with
    | some u => CheckedReductionWire.emit u
    | none => #[#[3]]
  | _ => #[#[0]]

/-- Following first steps takes the path of the checked reducer's first branch. -/
theorem follow_eq {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym]
    [DecidableEq s.Atom] (rs : Problem s) (k : Nat) (t : Term s) :
    ReferenceReduction.follow rs k t = CheckedReduction.choose rs k t := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    rw [ReferenceReduction.follow_succ]
    change _ = (match ReferenceReduction.successors rs t with
      | [] => some t | x :: _ => CheckedReduction.choose rs k x)
    cases ReferenceReduction.successors rs t with
    | nil => rfl
    | cons x xs => exact ih x

omit [Interrupt] in
/-- The path taken is the one the total reference reducer takes. -/
theorem choose_exact {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym]
    [DecidableEq s.Atom] {rs : Problem s} (bound : ReferenceReduction.Bound rs)
    (can : CanonicalPresentation (ruleRoot rs)) (k : Nat) (t u : Term s)
    (ok : CheckedReduction.choose rs k t = some u) :
    u = (ReferenceReduction.reducer rs bound can).reduce t := by
  induction k generalizing t with
  | zero => contradiction
  | succ k ih =>
    rw [show (ReferenceReduction.reducer rs bound can).reduce t = _ from
      reducerOfSteps_eq can (ReferenceReduction.finder rs bound) t]
    cases e : ReferenceReduction.successors rs t with
    | nil =>
      have stopped : (ReferenceReduction.finder rs bound).next t = none := by simp [ReferenceReduction.finder,e]
      rw [stopped]
      change (match ReferenceReduction.successors rs t with | [] => some t | x :: _ => CheckedReduction.choose rs k x) = some u at ok
      simpa [e] using ok.symm
    | cons x xs =>
      have step : (ReferenceReduction.finder rs bound).next t = some x := by simp [ReferenceReduction.finder,e]
      rw [step]
      apply ih
      change (match ReferenceReduction.successors rs t with | [] => some t | x :: _ => CheckedReduction.choose rs k x) = some u at ok
      simpa [e] using ok

/-- With a certified table every reply is the unique normal form or a request
for more depth. On a canonical table every depth that bounds all rewrite paths
from the term produces the normal form: the request for more depth cannot be
made at such a depth. The bound is on the rewrite relation, not on any search. -/
structure Correct (kernel : CheckedReductionWire.Kernel) : Prop where
  malformed : ∀ ds ns es root n, TableWire.input ds ns es #[root] = none → kernel ds ns es root n = #[#[0]]
  valid : ∀ ds ns es root n d t rs, TableWire.input ds ns es #[root] = some ⟨d,rs,[t]⟩ →
    CertifiedTableWire.Certified rs →
    GeneralReductionWire.Answer d rs t (kernel ds ns es root n) ∨ kernel ds ns es root n = #[#[3]]
  completes : ∀ ds ns es root d t rs, TableWire.input ds ns es #[root] = some ⟨d,rs,[t]⟩ →
    ReferenceReduction.Bound rs → CanonicalPresentation (ruleRoot rs) → ∀ n : UInt64,
      CheckedReduction.Within rs n.toNat t → GeneralReductionWire.Answer d rs t (kernel ds ns es root n)

/-- Either way the result is an irreducible reduct of the input. -/
theorem path_sound {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym]
    [DecidableEq s.Atom] {rs : Problem s} (bound : ReferenceReduction.Bound rs) {fuel : Nat}
    {t u : Term s} (h : path rs fuel t = some u) :
    Reduces (ruleRoot rs) t u ∧ Normal (ruleRoot rs) u := by
  unfold path at h
  split at h
  · next v found =>
    cases h
    exact ReferenceReduction.normalize_sound bound fuel t _ found
  · rw [follow_eq] at h
    exact CheckedReduction.chosen bound fuel t u h

/-- Enough depth for the outermost path is enough for `path`. -/
theorem path_some {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym]
    [DecidableEq s.Atom] {rs : Problem s} {fuel : Nat} {t u : Term s}
    (h : CheckedReduction.choose rs fuel t = some u) : ∃ v, path rs fuel t = some v := by
  unfold path
  split
  · exact ⟨_,rfl⟩
  · exact ⟨u,by rw [follow_eq]; exact h⟩

/-- On a canonical presentation the path ends in the unique normal form. -/
theorem path_reply {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym]
    [DecidableEq s.Atom] {rs : Problem s} (bound : ReferenceReduction.Bound rs)
    (can : CanonicalPresentation (ruleRoot rs)) {k : Nat} {t u : Term s}
    (found : path rs k t = some u) : ReductionReply (ruleRoot rs) t u := by
  obtain ⟨red,normal⟩ := path_sound bound found
  let reference := (ReferenceReduction.reducer rs bound can).correct t
  obtain ⟨_,left,right⟩ := can.confluent reference.normalForm.1 red
  have same : EquivB ((ReferenceReduction.reducer rs bound can).reduce t) u :=
    (normal_reduces_equiv left reference.normalForm.2.1).trans (normal_reduces_equiv right normal).symm
  exact ⟨⟨red,normal,fun k hk => Term.checkSort_sound _ _ (SortClash.check_equiv same k ▸
      Term.checkSort_complete (reference.normalForm.2.2 k hk))⟩,
      fun other form => (reference.unique other form).trans same⟩

/-- On a canonical presentation every depth beyond the rewrite height of the
term ends the path. -/
theorem path_completes {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym]
    [DecidableEq s.ACSym] [DecidableEq s.Atom] {rs : Problem s} (bound : ReferenceReduction.Bound rs)
    (can : CanonicalPresentation (ruleRoot rs)) (t : Term s) (n : Nat)
    (enough : ReductionHeight.height bound can.terminating t < n) : ∃ u, path rs n t = some u := by
  have settled := CheckedReduction.settled_of_height bound can n t enough
  have some_ : ∃ u, CheckedReduction.choose rs n t = some u := by
    cases found : CheckedReduction.choose rs n t with
    | some u => exact ⟨u,rfl⟩
    | none =>
      rcases CheckedReduction.decides_settled bound settled with ⟨u,ok⟩ | clash
      · simp [CheckedReduction.run,found] at ok
      · simp [CheckedReduction.ambiguous,found] at clash
  obtain ⟨w,chosen⟩ := some_
  exact path_some chosen

private theorem answer {ds ns es root} {d : TotalUnifyWire.Dictionary} {t u : Term d.sig} {rs : Problem d.sig}
    (decoded : TableWire.input ds ns es #[root] = some ⟨d,rs,[t]⟩)
    (bound : ReferenceReduction.Bound rs) (can : CanonicalPresentation (ruleRoot rs)) (k : Nat)
    (found : path rs k t = some u) :
    GeneralReductionWire.Answer d rs t (CheckedReductionWire.emit u) := by
  have reply := path_reply bound can found
  exact ⟨u,CheckedReductionWire.decodes_emit decoded bound reply,reply,
    fun extra => SignatureExtension.reduction extra rs bound t u reply⟩

theorem correct : Correct run where
  malformed := fun _ _ _ _ _ h => by simp [run,h]
  valid := by
    intro ds ns es root n d t rs decoded ⟨scope,can,_⟩
    obtain ⟨bound,localCan⟩ := SignatureExtension.reflect_canonical TableAmbient.atoms rs scope can
    cases found : path rs n.toNat t with
    | none => exact .inr (by simp [run,decoded,found])
    | some u =>
      have out : run ds ns es root n = CheckedReductionWire.emit u := by simp [run,decoded,found]
      exact .inl (out ▸ answer decoded bound localCan _ found)
  completes := by
    intro ds ns es root d t rs decoded bound can n tree
    obtain ⟨_,chosen⟩ := CheckedReduction.choose_of_within bound _ _ tree
    obtain ⟨u,found⟩ := path_some chosen
    have out : run ds ns es root n = CheckedReductionWire.emit u := by simp [run,decoded,found]
    exact out ▸ answer decoded bound can _ found

end Tamarin.CertifiedReductionWire

/-! The same single path on a table that is only range restricted. Status 1
carries an irreducible reduct of the input that keeps every sort of the input.
Nothing says it is the only one: the caller assumes convergence. Status 2
reports a table that is not range restricted or a reduct that lost a sort,
status 3 requests more depth, and status 0 denotes a malformed packet. -/
namespace Tamarin.PathReductionWire
open MaudeOperations Rewriting
variable [Interrupt]

def run (ds : Array UInt64) (ns : Array (Array UInt64)) (pairs : Array UInt64) (root fuel : UInt64) :
    Array (Array UInt64) :=
  match TableWire.input ds ns pairs #[root] with
  | some ⟨_,rs,[t]⟩ =>
    if CheckedReduction.rangeBound rs then
      match CertifiedReductionWire.path rs fuel.toNat t with
      | some u => if CheckedReduction.sorts t u then CheckedReductionWire.emit u else #[#[2]]
      | none => #[#[3]]
    else #[#[2]]
  | _ => #[#[0]]

/-- A reply with status 1 is an irreducible reduct with the sorts of the
input, over the decoded signature and over every extension of it. No
convergence of the table is assumed and no uniqueness is claimed. The other
replies have causes in the table and the rewrite relation, not in the search:
status 2 means that the table is not range restricted or that some irreducible
reduct lost a sort of the input, and status 3 that some rewrite path from the
term has at least as many steps as the depth. -/
structure Correct (kernel : CheckedReductionWire.Kernel) : Prop where
  malformed : ∀ ds ns es root n, TableWire.input ds ns es #[root] = none → kernel ds ns es root n = #[#[0]]
  valid : ∀ ds ns es root n d t rs, TableWire.input ds ns es #[root] = some ⟨d,rs,[t]⟩ →
    (∃ u, CheckedReductionWire.Decodes d (kernel ds ns es root n) u ∧ NormalForm (ruleRoot rs) t u ∧
      ∀ extra : Signature, NormalForm (ruleRoot (SignatureExtension.query extra rs))
        (SignatureExtension.embed extra t) (SignatureExtension.embed extra u)) ∨
    (kernel ds ns es root n = #[#[2]] ∧ (¬ ReferenceReduction.Bound rs ∨
      ∃ u, Reduces (ruleRoot rs) t u ∧ Normal (ruleRoot rs) u ∧ ¬ ∀ k, HasSort t k → HasSort u k)) ∨
    (kernel ds ns es root n = #[#[3]] ∧ ReferenceReduction.Bound rs ∧
      ¬ CheckedReduction.Within rs n.toNat t)

theorem correct : Correct run where
  malformed := fun _ _ _ _ _ h => by simp [run,h]
  valid := by
    intro ds ns es root n d t rs decoded
    cases ranged : CheckedReduction.rangeBound rs with
    | false => exact .inr (.inl ⟨by simp [run,decoded,ranged],
        .inl fun h => by simp [(CheckedReduction.rangeBound_iff _).mpr h] at ranged⟩)
    | true =>
      have bound := (CheckedReduction.rangeBound_iff _).mp ranged
      cases found : CertifiedReductionWire.path rs n.toNat t with
      | none =>
        refine .inr (.inr ⟨by simp [run,decoded,ranged,found],bound,fun tree => ?_⟩)
        obtain ⟨_,chosen⟩ := CheckedReduction.choose_of_within bound _ _ tree
        obtain ⟨_,some_⟩ := CertifiedReductionWire.path_some chosen
        simp [found] at some_
      | some u =>
        obtain ⟨red,normal⟩ := CertifiedReductionWire.path_sound bound found
        cases kept : CheckedReduction.sorts t u with
        | false => exact .inr (.inl ⟨by simp [run,decoded,ranged,found,kept],
            .inr ⟨u,red,normal,fun same => by simp [(CheckedReduction.sorts_iff ..).mpr same] at kept⟩⟩)
        | true =>
          have form : NormalForm (ruleRoot rs) t u := ⟨red,normal,(CheckedReduction.sorts_iff ..).mp kept⟩
          have out : run ds ns es root n = CheckedReductionWire.emit u := by
            simp [run,decoded,ranged,found,kept]
          exact .inl ⟨u,out ▸ CheckedReductionWire.decodes_reduct decoded bound red,form,
            fun extra => SignatureExtension.normalForm extra rs bound t u form⟩

end Tamarin.PathReductionWire
