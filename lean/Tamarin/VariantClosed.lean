import Tamarin.VariantCertificate

/-! The families the variant certificate checker accepts, stated without
reference to how the checker computes. A family is closed when every member
is normal on the observed variables, some member subsumes the normalized
query, and every normalized one-step narrowing successor of a member is
subsumed by a member. Normal forms, rewrite steps and subsumption are the
relations of the rewrite presentation, not the functions that compute them.

On a canonical presentation the checker accepts exactly the closed families,
once its depth exceeds the rewrite height of the terms it normalizes. Below
that depth it may report an exhausted budget, and a rejection names a clause
of closedness that fails. -/
namespace Tamarin.VariantCertificate
open Rewriting VariantJoin MaudeOperations ReferenceVariantFrontier TupleNarrowingFrontier
variable {s : Signature}

/-- The values are normal forms of the instantiated query. -/
def Completed (R : Root s) (q : List (Term s)) (σ : Substitution s) (values : List (Term s)) : Prop :=
  Aligned (fun t u => NormalForm R (σ.apply t) u) q values

/-- One substitution turns the images of the first substitution on the
observed variables, and its values, into those of the second one. -/
def Subsumed (q : List (Term s)) (σ : Substitution s) (values : List (Term s))
    (τ : Substitution s) (others : List (Term s)) : Prop :=
  ∃ θ : Substitution s, (∀ v, Observed q v → EquivB (τ.image v) (θ.apply (σ.image v))) ∧
    Aligned (fun u w => EquivB u (θ.apply w)) others values

/-- Exactly one entry takes a rewrite step. -/
inductive OneStep (R : Root s) : List (Term s) → List (Term s) → Prop
  | here {t u : Term s} (ts : List (Term s)) : StepModulo R t u → OneStep R (t :: ts) (u :: ts)
  | later (t : Term s) {ts us : List (Term s)} : OneStep R ts us → OneStep R (t :: ts) (t :: us)

/-- The substitution is normal on the observed variables. -/
def NormalMember (R : Root s) (q : List (Term s)) (σ : Substitution s) : Prop :=
  ∀ v, Observed q v → Normal R (σ.image v)

/-- Some member subsumes the normalized query. -/
def Starts (R : Root s) (q : List (Term s)) (family : List (Substitution s)) : Prop :=
  ∃ σ ∈ family, ∃ values first, Completed R q σ values ∧ Completed R q .identity first ∧
    Subsumed q σ values .identity first

/-- Every normalized one-step narrowing successor of the member is subsumed
by a member. A narrowing successor instantiates the member, keeping its
images normal, and rewrites one of the instantiated values once. -/
def Folds (R : Root s) (q : List (Term s)) (family : List (Substitution s)) (σ : Substitution s) : Prop :=
  ∀ values, Completed R q σ values → ∀ τ : Substitution s,
    (∀ v, Observed q v → Normal R (τ.apply (σ.image v))) →
    ∀ raw, OneStep R (values.map τ.apply) raw → ∀ next, Aligned (NormalForm R) raw next →
    ∃ σ' ∈ family, ∃ values', Completed R q σ' values' ∧ Subsumed q σ' values' (τ.compose σ) next

/-- The families the checker has to accept. -/
structure Closed (R : Root s) (q : List (Term s)) (family : List (Substitution s)) : Prop where
  normal : ∀ σ ∈ family, NormalMember R q σ
  start : Starts R q family
  step : ∀ σ ∈ family, Folds R q family σ

/-- A narrowing successor of a member: an instance of the member that keeps
its images normal, with one rewrite step in one of the instantiated values. -/
def Successor (R : Root s) (q : List (Term s)) (σ : Substitution s) (values : List (Term s))
    (τ : Substitution s) (raw : List (Term s)) : Prop :=
  (∀ v, Observed q v → Normal R (τ.apply (σ.image v))) ∧ OneStep R (values.map τ.apply) raw

/-- No successor of the member is properly more general: a successor of
which this one is an instance is an instance of this one. -/
def MostGeneral (R : Root s) (q : List (Term s)) (σ : Substitution s) (values : List (Term s))
    (τ : Substitution s) (raw : List (Term s)) : Prop :=
  ∀ τ' raw', Successor R q σ values τ' raw' →
    Subsumed q (τ'.compose σ) raw' (τ.compose σ) raw →
    Subsumed q (τ.compose σ) raw (τ'.compose σ) raw'

/-- The terms a check has to normalize: the query, the instantiated queries,
and the values of the most general narrowing successors of the members. -/
inductive Demand (R : Root s) (q : List (Term s)) (family : List (Substitution s)) : Term s → Prop
  | query {t : Term s} : t ∈ q → Demand R q family t
  | member {σ : Substitution s} {t : Term s} : σ ∈ family → t ∈ q → Demand R q family (σ.apply t)
  | successor {σ τ : Substitution s} {values raw : List (Term s)} {t : Term s} : σ ∈ family →
      Completed R q σ values → Successor R q σ values τ raw → MostGeneral R q σ values τ raw →
      t ∈ raw → Demand R q family t

/-- The positions at which the narrowing layer of a member with these values
looks for steps: the positions of the values that are not variables, in the
slots whose query term is not a variable. -/
def Charge (q values : List (Term s)) : Nat :=
  ((q.zip values).map fun e => if idle e.1 then 0 else sites e.2).sum

/-- The work limit is below the positions of the narrowing layers of the
members, added up. -/
def Overcharged (R : Root s) (q : List (Term s)) (family : List (Substitution s)) (work : Nat) : Prop :=
  ∃ rows : List (List (Term s)), Aligned (Completed R q) family rows ∧ work < (rows.map (Charge q)).sum

variable {n : Nat} {rules : List (Equation s)} {query : Fin n → Term s}

theorem completed_ofFn {R : Root s} {σ : Substitution s} {values : Fin n → Term s} :
    Completed R (List.ofFn query) σ (List.ofFn values) ↔
      ∀ i, NormalForm R (σ.apply (query i)) (values i) :=
  ⟨VariantSaturation.atFn (rel := fun t u => NormalForm R (σ.apply t) u) query values,
    alignedFn (rel := fun t u => NormalForm R (σ.apply t) u) query values⟩

theorem subsumed_ofFn {σ τ : Substitution s} {a b : Fin n → Term s} :
    Subsumed (List.ofFn query) σ (List.ofFn a) τ (List.ofFn b) ↔
      ((⟨σ,a⟩ : Point s n).row (keysOf query)).Subsumes ((⟨τ,b⟩ : Point s n).row (keysOf query)) := by
  constructor
  · rintro ⟨θ,inputs,values⟩
    exact ⟨θ,fun i => inputs i.val ((observed query i.val).mp i.property),
      VariantSaturation.atFn (rel := fun u w => EquivB u (θ.apply w)) b a values⟩
  · rintro ⟨θ,fit⟩
    exact ⟨θ,fun v hv => fit.inputs ⟨v,(observed query v).mpr hv⟩,alignedFn (rel := fun u w => EquivB u (θ.apply w)) b a fit.values⟩

theorem oneStep_ofFn {R : Root s} {a : Fin n → Term s} {raw : List (Term s)}
    (h : OneStep R (List.ofFn a) raw) : ∃ b, raw = List.ofFn b ∧ ∀ i, Reduces R (a i) (b i) := by
  induction n generalizing raw with
  | zero => simp at h; cases h
  | succ n ih =>
    rw [List.ofFn_succ] at h
    cases h with
    | here ts step =>
      exact ⟨Fin.cases _ (fun i => a i.succ),by simp [List.ofFn_succ],
        Fin.cases (.step step) (fun _ => .basis (.refl _))⟩
    | later t rest =>
      obtain ⟨b,rfl,each⟩ := ih rest
      exact ⟨Fin.cases (a 0) b,by simp [List.ofFn_succ],Fin.cases (.basis (.refl _)) each⟩

theorem oneStep_replace {R : Root s} (a : Fin n → Term s) (j : Fin n) {u : Term s}
    (step : StepModulo R (a j) u) : OneStep R (List.ofFn a) (List.ofFn (replace a j u)) := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ]
    cases j using Fin.cases with
    | zero =>
      have rest : (fun i : Fin n => replace a 0 u i.succ) = fun i => a i.succ := by
        funext i
        simp [replace,Fin.succ_ne_zero]
      rw [rest]
      simpa [replace] using OneStep.here (List.ofFn fun i => a i.succ) step
    | succ k =>
      have head : replace a k.succ u 0 = a 0 := by
        simp [replace,(Fin.succ_ne_zero k).symm]
      have rest : (fun i : Fin n => replace a k.succ u i.succ) =
          replace (fun i => a i.succ) k u := by
        funext i
        simp [replace,Fin.succ_inj]
      rw [head,rest]
      exact .later _ (ih (fun i => a i.succ) k step)

section
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]
variable [Interrupt]

omit [Interrupt] in
/-- An irreducible reduct is a normal form: on a canonical presentation it
keeps the sorts of its source. -/
theorem normalForm_of_reduces (bound : ReferenceReduction.Bound rules)
    (canonical : CanonicalPresentation (ruleRoot rules)) {t u : Term s}
    (red : Reduces (ruleRoot rules) t u) (normal : Normal (ruleRoot rules) u) :
    NormalForm (ruleRoot rules) t u := by
  let reference := (ReferenceReduction.reducer rules bound canonical).correct t
  obtain ⟨_,left,right⟩ := canonical.confluent reference.normalForm.1 red
  have same : EquivB ((ReferenceReduction.reducer rules bound canonical).reduce t) u :=
    (normal_reduces_equiv left reference.normalForm.2.1).trans (normal_reduces_equiv right normal).symm
  exact ⟨red,normal,fun k hk => Term.checkSort_sound _ _ (SortClash.check_equiv same k ▸
    Term.checkSort_complete (reference.normalForm.2.2 k hk))⟩

/-- An accepted family is closed. -/
theorem accepted_closed (canonical : CanonicalPresentation (ruleRoot rules)) {q : List (Term s)}
    {family : List (Substitution s)} {fuel work : Nat}
    (h : check rules q family fuel work = .accepted) : Closed (ruleRoot rules) q family := by
  obtain ⟨members,built,vars,formed,hits⟩ := accepted_cover canonical h
  have bound : ReferenceReduction.Bound rules := by
    unfold check at h
    split at h
    · next hb => exact (CheckedReduction.rangeBound_iff rules).mp hb
    · contradiction
  let query := fun i : Fin q.length => q[i.val]
  let keys := keysOf query
  let r := ReferenceReduction.reducer rules bound canonical
  have list : List.ofFn query = q := List.ofFn_getElem
  have source (p) (hp : p ∈ members) : p.assignment ∈ family := by
    obtain ⟨σ,hσ,made⟩ := mapM_some_source _ built p hp
    exact (member_form made).1 ▸ hσ
  have target (σ) (hσ : σ ∈ family) : ∃ p ∈ members, p.assignment = σ := by
    obtain ⟨p,hp,made⟩ := mapM_some_mem _ built σ hσ
    exact ⟨p,hp,(member_form made).1⟩
  rw [← list]
  refine ⟨fun σ hσ v hv => ?_,?_,fun σ hσ values done τ live raw step next forms => ?_⟩
  · obtain ⟨p,hp,rfl⟩ := target σ hσ
    exact (formed p hp).1 ⟨v,(observed query v).mpr hv⟩
  · obtain ⟨p,hp,δ,fit⟩ := hits .identity vars (fun i => r.reduce (query i))
      (fun i => by simpa using (r.correct (query i)).normalForm)
    exact ⟨p.assignment,source p hp,List.ofFn p.value,List.ofFn fun i => r.reduce (query i),
      completed_ofFn.mpr (formed p hp).2,
      completed_ofFn.mpr (fun i => by simpa using (r.correct (query i)).normalForm),
      subsumed_ofFn.mpr ⟨δ,fit⟩⟩
  · obtain ⟨value,rfl,nf⟩ := read_aligned query values done
    rw [List.map_ofFn] at step
    obtain ⟨b,rfl,reduces⟩ := oneStep_ofFn step
    obtain ⟨out,rfl,ends⟩ := read_aligned b next forms
    let c : Point s q.length := ⟨τ.compose σ,out⟩
    let ρ := (c.row keys).project (fun k => c.assignment.sorted k.val)
    have on_keys (k : Key keys) : ρ.image k.val = (τ.compose σ).image k.val :=
      (c.row keys).project_key (fun k => c.assignment.sorted k.val) k
    have normal : Normalized (ruleRoot rules) ρ := by
      intro v
      change Normal (ruleRoot rules) (if h : v ∈ keys then (c.row keys).input ⟨v,h⟩ else .var v)
      split
      · next key => exact live v ((observed query v).mp key)
      · exact vars v
    have forms' (i) : NormalForm (ruleRoot rules) (ρ.apply (query i)) (out i) := by
      have same : ρ.apply (query i) = τ.apply (σ.apply (query i)) := by
        rw [← Substitution.apply_compose]
        exact Term.subst_eq_of_agree _ _ _ fun v hv =>
          on_keys ⟨v,(observed query v).mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,hv⟩⟩
      rw [same]
      exact normalForm_of_reduces bound canonical
        (((SpecializedFresh.reduces_subst rules τ (nf i).1).trans (reduces i)).trans (ends i).1)
        (ends i).2.1
    obtain ⟨p,hp,δ,fit⟩ := hits ρ normal out forms'
    refine ⟨p.assignment,source p hp,List.ofFn p.value,completed_ofFn.mpr (formed p hp).2,
      subsumed_ofFn.mpr ⟨δ,fun k => ?_,fit.values⟩⟩
    have input := fit.inputs k
    rwa [on_keys k] at input

omit [Interrupt] in
theorem mapM_ofFn_some {α β : Type} (f : α → Option β) {n : Nat} {g : Fin n → α} {k : Fin n → β}
    (h : ∀ i, f (g i) = some (k i)) : (List.ofFn g).mapM f = some (List.ofFn k) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.ofFn_succ,h 0,ih (fun i => h i.succ)]

omit [Interrupt] in
theorem mapM_map_some {α β : Type} (f : α → Option β) (g : α → β) {xs : List α}
    (h : ∀ x ∈ xs, f x = some (g x)) : xs.mapM f = some (xs.map g) := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    simp [h a List.mem_cons_self,ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

omit [Interrupt] in
theorem every_of_all {α : Type} {f : α → Option Bool} {xs : List α}
    (h : ∀ x ∈ xs, f x = some true) : every f xs = some true := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    unfold every
    rw [h a List.mem_cons_self]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

omit [Interrupt] in
theorem every_decided {α : Type} {f : α → Option Bool} {xs : List α}
    (h : ∀ x ∈ xs, f x ≠ none) : every f xs ≠ none := by
  induction xs with
  | nil => simp [every]
  | cons a as ih =>
    unfold every
    split
    · exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    · exact h a List.mem_cons_self

omit [Interrupt] in
theorem every_false {α : Type} {f : α → Option Bool} {xs : List α}
    (h : every f xs = some false) : ∃ x ∈ xs, f x = some false := by
  induction xs with
  | nil => simp [every] at h
  | cons a as ih =>
    unfold every at h
    split at h
    · obtain ⟨x,hx,bad⟩ := ih h
      exact ⟨x,List.mem_cons_of_mem _ hx,bad⟩
    · exact ⟨a,List.mem_cons_self,h⟩

omit [Interrupt] in
theorem le_foldr_max {xs : List Nat} {x : Nat} (h : x ∈ xs) : x ≤ xs.foldr max 0 := by
  induction xs with
  | nil => exact nomatch h
  | cons a as ih =>
    rcases List.mem_cons.mp h with rfl | later
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih later) (Nat.le_max_right _ _)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] [Interrupt] in
/-- A row keeps subsuming another when the values of both are exchanged for
equal ones. -/
theorem subsumes_congr {keys : List Variable} {σ τ : Substitution s} {a a' b b' : Fin n → Term s}
    (h : ((⟨σ,a⟩ : Point s n).row keys).Subsumes ((⟨τ,b⟩ : Point s n).row keys))
    (left : ∀ i, EquivB (a i) (a' i)) (right : ∀ i, EquivB (b i) (b' i)) :
    ((⟨σ,a'⟩ : Point s n).row keys).Subsumes ((⟨τ,b'⟩ : Point s n).row keys) := by
  obtain ⟨θ,fit⟩ := h
  exact ⟨θ,fit.inputs,fun i => (right i).symm.trans ((fit.values i).trans ((left i).subst θ.image))⟩

/-- The complete matcher finds a substitution whenever one row subsumes another. -/
theorem instanceOf_complete {keys : List Variable} {g t : Point s n}
    (h : (g.row keys).Subsumes (t.row keys)) : instanceOf (terms keys g) (terms keys t) = true := by
  obtain ⟨θ,fit⟩ := h
  unfold instanceOf
  dsimp only
  rw [ReferenceMatching.first_eq]
  have complete := plain_match (ReferenceMatching.matcher s)
    (((terms keys g).zip (terms keys t)).map fun e => (⟨e.1,e.2⟩ : Equation s)) trivial
  have nonempty := complete.exists_match_iff.mp ⟨θ,fun e he => by
    obtain ⟨pair,member,rfl⟩ := List.mem_map.mp he
    rw [zip_terms] at member
    rcases List.mem_append.mp member with key | slot
    · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp key
      exact (fit.inputs ⟨v,hv⟩).symm
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp slot
      exact (fit.values i).symm⟩
  change ReferenceMatching.solve _ _ ≠ [] at nonempty
  cases found : ReferenceMatching.solve
    (((terms keys g).zip (terms keys t)).map fun e => (⟨e.1,e.2⟩ : Equation s))
    (patternVariables (((terms keys g).zip (terms keys t)).map fun e => (⟨e.1,e.2⟩ : Equation s))) with
  | nil => exact absurd found nonempty
  | cons => rfl

theorem covered_complete {keys : List Variable} {members : List (Point s n)} {m c : Point s n}
    (hm : m ∈ members) (h : (m.row keys).Subsumes (c.row keys)) :
    covered (members.map (terms keys)) (terms keys c) = true :=
  Bool.or_eq_true_iff.mpr (.inr (List.any_eq_true.mpr
    ⟨_,List.mem_map_of_mem hm,instanceOf_complete h⟩))

theorem quiet_normal (bound : ReferenceReduction.Bound rules) {t : Term s}
    (h : quiet rules t = true) : Normal (ruleRoot rules) t := by
  intro u step
  obtain ⟨v,hv,_⟩ := (ReferenceReduction.exactSteps rules bound _ _).mpr step
  rw [quiet_eq] at h
  rw [List.isEmpty_iff.mp h] at hv
  exact List.not_mem_nil hv

/-- The first rewrite path ends once the depth exceeds the rewrite height. -/
theorem follow_some (bound : ReferenceReduction.Bound rules)
    (canonical : CanonicalPresentation (ruleRoot rules)) {fuel : Nat} {t : Term s}
    (enough : ReductionHeight.height bound canonical.terminating t < fuel) :
    ReferenceReduction.follow rules fuel t =
      some ((ReferenceReduction.reducer rules bound canonical).reduce t) := by
  obtain ⟨u,found⟩ := CheckedReduction.choose_of_within bound fuel t
    (CheckedReduction.settled_of_height bound canonical fuel t enough).1
  rw [← CertifiedReductionWire.follow_eq] at found
  rw [found,follow_reduce bound canonical found]

theorem settle_some (bound : ReferenceReduction.Bound rules)
    (canonical : CanonicalPresentation (ruleRoot rules)) {fuel : Nat} {raw : Fin n → Term s}
    (enough : ∀ i, ReductionHeight.height bound canonical.terminating (raw i) < fuel) :
    settle rules fuel raw =
      some (List.ofFn fun i => (ReferenceReduction.reducer rules bound canonical).reduce (raw i)) :=
  mapM_ofFn_some _ fun i => follow_some bound canonical (enough i)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] [Interrupt] in
theorem mapM_none {α β : Type} (f : α → Option β) {xs : List α} (h : xs.mapM f = none) :
    ∃ x ∈ xs, f x = none := by
  induction xs with
  | nil => simp at h
  | cons a as ih =>
    cases ha : f a with
    | none => exact ⟨a,List.mem_cons_self,ha⟩
    | some b =>
      cases tail : as.mapM f with
      | none =>
        obtain ⟨x,hx,bad⟩ := ih tail
        exact ⟨x,List.mem_cons_of_mem _ hx,bad⟩
      | some bs => simp [ha,tail] at h

/-- A layer whose ordered scan settles is settled the same way. -/
theorem closedAt_of_strict {keys : List Variable}
    {branches : Point s n → Fin n → List (RootNarrowing.Branch s)} {fuel : Nat}
    {rows : List (List (Term s))} {p : Point s n} {value : Bool}
    (h : strictAt rules query keys branches fuel rows p = some value) :
    closedAt rules query keys branches fuel rows p = some value := by
  unfold closedAt
  rw [h]

/-- A layer that fails has a successor that was normalized and is not an
instance of a row. -/
theorem closedAt_false {keys : List Variable}
    {branches : Point s n → Fin n → List (RootNarrowing.Branch s)} {fuel : Nat}
    {rows : List (List (Term s))} {p : Point s n}
    (h : closedAt rules query keys branches fuel rows p = some false) :
    ∃ j b, idle (query j) = false ∧ b ∈ branches p j ∧
      childOk rules keys fuel rows p j b = some false := by
  unfold closedAt at h
  split at h
  · unfold rescue at h
    dsimp only at h
    split at h
    · next bad =>
      obtain ⟨e,he,eq⟩ := List.any_eq_true.mp bad
      obtain ⟨⟨j,b⟩,hl,rfl⟩ := List.mem_map.mp he
      obtain ⟨live,hb⟩ := mem_layer.mp hl
      exact ⟨j,b,live,hb,by simpa using eq⟩
    · split at h <;> cases h
  · unfold strictAt at h
    obtain ⟨j,_,slot⟩ := every_false h
    split at slot
    · cases slot
    · next live =>
      obtain ⟨b,hb,child⟩ := every_false slot
      exact ⟨j,b,by simpa using live,hb,child⟩

/-- A layer that the depth leaves open has no successor that fails, and a
successor whose normal form the depth does not reach and that is an instance
of no successor that passed. -/
theorem closedAt_none {keys : List Variable}
    {branches : Point s n → Fin n → List (RootNarrowing.Branch s)} {fuel : Nat}
    {rows : List (List (Term s))} {p : Point s n}
    (h : closedAt rules query keys branches fuel rows p = none) :
    (∀ j b, idle (query j) = false → b ∈ branches p j →
      childOk rules keys fuel rows p j b ≠ some false) ∧
    ∃ j b, idle (query j) = false ∧ b ∈ branches p j ∧ childOk rules keys fuel rows p j b = none ∧
      ∀ j0 b0, idle (query j0) = false → b0 ∈ branches p j0 →
        childOk rules keys fuel rows p j0 b0 = some true →
        (keys.map (b0.subst.compose p.assignment).image).all (quiet rules) = true →
        instanceOf (terms keys (successor p j0 b0)) (terms keys (successor p j b)) = false := by
  unfold closedAt at h
  split at h
  · unfold rescue at h
    dsimp only at h
    split at h
    · cases h
    · next clean =>
      split at h
      · cases h
      · next open_ =>
        refine ⟨fun j b live hb bad => clean (List.any_eq_true.mpr ⟨((j,b),some false),
          List.mem_map.mpr ⟨(j,b),mem_layer.mpr ⟨live,hb⟩,by rw [bad]⟩,rfl⟩),?_⟩
        simp only [List.all_eq_true,Classical.not_forall] at open_
        obtain ⟨e,he,miss⟩ := open_
        obtain ⟨made,pending⟩ := List.mem_filter.mp he
        obtain ⟨⟨j,b⟩,hl,rfl⟩ := List.mem_map.mp made
        obtain ⟨live,hb⟩ := mem_layer.mp hl
        refine ⟨j,b,live,hb,by simpa using pending,fun j0 b0 live0 hb0 ok quiet_ => ?_⟩
        cases found : instanceOf (terms keys (successor p j0 b0)) (terms keys (successor p j b)) with
        | false => rfl
        | true =>
          exfalso
          apply miss
          apply List.any_eq_true.mpr
          refine ⟨_,List.mem_map.mpr ⟨((j0,b0),childOk rules keys fuel rows p j0 b0),
            List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(j0,b0),mem_layer.mpr ⟨live0,hb0⟩,rfl⟩,?_⟩,rfl⟩,found⟩
          simp [ok,quiet_]
  · next other differs => exact absurd h (differs · )

/-- The member the checker builds for a substitution once the depth suffices. -/
def reference (r : VerifiedReducer (ruleRoot rules)) (query : Fin n → Term s) (σ : Substitution s) :
    Point s n :=
  ⟨σ,fun i => r.reduce (σ.apply (query i))⟩

/-- The terms the closure test normalizes: the query, the instantiated
queries, and the values of the narrowing successors of every member. -/
def demand (bound : ReferenceReduction.Bound rules) (canonical : CanonicalPresentation (ruleRoot rules))
    (vars : Normalized (ruleRoot rules) Substitution.identity) (query : Fin n → Term s)
    (family : List (Substitution s)) : List (Term s) :=
  let r := ReferenceReduction.reducer rules bound canonical
  let narrow := TableNarrowing.checking bound vars query
  List.ofFn query ++ family.flatMap (fun σ => List.ofFn fun i => σ.apply (query i)) ++
    family.flatMap fun σ => (List.finRange n).flatMap fun j =>
      (narrow.branches (reference r query σ) j).flatMap fun b =>
        List.ofFn (replace (fun i => b.subst.apply ((reference r query σ).value i)) j b.value)

/-- One more than the largest rewrite height among the terms the closure
test normalizes. -/
noncomputable def depth (bound : ReferenceReduction.Bound rules)
    (canonical : CanonicalPresentation (ruleRoot rules))
    (vars : Normalized (ruleRoot rules) Substitution.identity) (query : Fin n → Term s)
    (family : List (Substitution s)) : Nat :=
  1 + ((demand bound canonical vars query family).map
    (ReductionHeight.height bound canonical.terminating)).foldr max 0

theorem depth_bound (bound : ReferenceReduction.Bound rules)
    (canonical : CanonicalPresentation (ruleRoot rules))
    (vars : Normalized (ruleRoot rules) Substitution.identity) {family : List (Substitution s)}
    {t : Term s} (h : t ∈ demand bound canonical vars query family) :
    ReductionHeight.height bound canonical.terminating t < depth bound canonical vars query family := by
  have := le_foldr_max (List.mem_map_of_mem (f := ReductionHeight.height bound canonical.terminating) h)
  unfold depth
  omega

theorem member_some (bound : ReferenceReduction.Bound rules)
    (canonical : CanonicalPresentation (ruleRoot rules)) {fuel : Nat} {σ : Substitution s}
    (enough : ∀ i, ReductionHeight.height bound canonical.terminating (σ.apply (query i)) < fuel) :
    member rules query fuel σ =
      some (reference (ReferenceReduction.reducer rules bound canonical) query σ) := by
  unfold member
  rw [settle_some bound canonical enough,Option.map_some,frozen_ofFn]
  rfl

omit [Interrupt] in
theorem reference_formed (bound : ReferenceReduction.Bound rules)
    (canonical : CanonicalPresentation (ruleRoot rules)) {σ : Substitution s}
    (normal : NormalMember (ruleRoot rules) (List.ofFn query) σ) :
    Formed rules query (reference (ReferenceReduction.reducer rules bound canonical) query σ) :=
  ⟨fun i => normal i.val ((observed query i.val).mp i.property),
    fun _ => ((ReferenceReduction.reducer rules bound canonical).correct _).normalForm⟩

/-- The closure test at a sufficient depth and without a work limit, on the
members of a closed family. -/
theorem saturated_closed (bound : ReferenceReduction.Bound rules)
    (canonical : CanonicalPresentation (ruleRoot rules))
    (vars : Normalized (ruleRoot rules) Substitution.identity) {family : List (Substitution s)}
    {fuel : Nat} (enough : depth bound canonical vars query family ≤ fuel)
    (closed : Closed (ruleRoot rules) (List.ofFn query) family) :
    saturated rules bound vars query fuel 0
      (family.map (reference (ReferenceReduction.reducer rules bound canonical) query)) = .accepted := by
  let r := ReferenceReduction.reducer rules bound canonical
  let keys := keysOf query
  let narrow := TableNarrowing.checking bound vars query
  let members := family.map (reference r query)
  have high {t : Term s} (h : t ∈ demand bound canonical vars query family) :
      ReductionHeight.height bound canonical.terminating t < fuel :=
    Nat.lt_of_lt_of_le (depth_bound bound canonical vars h) enough
  -- A member that subsumes, by any of its normal forms, also does by the reference ones.
  have lifted {σ' : Substitution s} (hσ' : σ' ∈ family) {values' : List (Term s)}
      (done : Completed (ruleRoot rules) (List.ofFn query) σ' values') {τ : Substitution s}
      {raw : Fin n → Term s}
      (sub : Subsumed (List.ofFn query) σ' values' τ (List.ofFn fun i => r.reduce (raw i))) :
      covered (members.map (terms keys))
        (keys.map τ.image ++ List.ofFn fun i => r.reduce (raw i)) = true := by
    obtain ⟨a,rfl,nf⟩ := read_aligned query values' done
    have same := subsumes_congr (subsumed_ofFn.mp sub)
      (a' := (reference r query σ').value) (b' := fun i => r.reduce (raw i))
      (fun i => (r.correct _).unique _ (nf i)) (fun _ => .refl _)
    exact covered_complete (c := ⟨τ,fun i => r.reduce (raw i)⟩)
      (List.mem_map_of_mem (f := reference r query) hσ') same
  unfold saturated
  dsimp only
  rw [settle_some bound canonical (fun i => high (List.mem_append_left _
    (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩))))]
  dsimp only
  have seed : covered (members.map (terms keys))
      (keys.map (Substitution.identity (sig := s)).image ++ List.ofFn fun i => r.reduce (query i)) = true := by
    obtain ⟨σ,hσ,values,first,done,plain,sub⟩ := closed.start
    obtain ⟨b,rfl,nf⟩ := read_aligned query first plain
    obtain ⟨a,rfl,_⟩ := read_aligned query values done
    have moved : Subsumed (List.ofFn query) σ (List.ofFn a) .identity (List.ofFn fun i => r.reduce (query i)) := by
      obtain ⟨θ,inputs,outputs⟩ := sub
      refine ⟨θ,inputs,alignedFn (rel := fun u w => EquivB u (θ.apply w)) _ _ fun i => ?_⟩
      have at_i := VariantSaturation.atFn (rel := fun u w => EquivB u (θ.apply w)) b a outputs i
      have form := nf i
      rw [Substitution.apply_identity] at form
      exact ((r.correct _).unique _ form).symm.trans at_i
    exact lifted hσ done moved
  rw [ite_eq_left_of_eq_true _ _ (eq_true seed)]
  have layers : ∀ p ∈ members, closedAt rules query keys narrow.branches fuel (members.map (terms keys)) p =
      some true := by
    intro p hp
    obtain ⟨σ,hσ,rfl⟩ := List.mem_map.mp hp
    have formed := reference_formed bound canonical (closed.normal σ hσ)
    apply closedAt_of_strict
    apply every_of_all
    intro j _
    split
    · rfl
    · apply every_of_all
      intro b hb
      unfold childOk
      dsimp only
      split
      · next quiet_ =>
        have inside (i : Fin n) : replace (fun i => b.subst.apply ((reference r query σ).value i)) j b.value i ∈
            demand bound canonical vars query family :=
          List.mem_append_right _ (List.mem_flatMap.mpr ⟨σ,hσ,List.mem_flatMap.mpr
            ⟨j,List.mem_finRange j,List.mem_flatMap.mpr ⟨b,hb,List.mem_ofFn.mpr ⟨i,rfl⟩⟩⟩⟩)
        rw [settle_some bound canonical (fun i => high (inside i)),Option.map_some]
        have live : ∀ v, Observed (List.ofFn query) v → Normal (ruleRoot rules) (b.subst.apply (σ.image v)) := by
          intro v hv
          have key := (observed query v).mpr hv
          exact quiet_normal bound (List.all_eq_true.mp quiet_ _
            (List.mem_map_of_mem (f := (b.subst.compose (reference r query σ).assignment).image) key))
        have step := narrow.genuine _ (sound_member vars _ formed) j b hb
        obtain ⟨σ',hσ',values',done,sub⟩ := closed.step σ hσ (List.ofFn (reference r query σ).value)
          (completed_ofFn.mpr formed.2) b.subst live
          (List.ofFn (replace (fun i => b.subst.apply ((reference r query σ).value i)) j b.value))
          (by rw [List.map_ofFn]; exact oneStep_replace _ j step)
          (List.ofFn fun i => r.reduce
            (replace (fun i => b.subst.apply ((reference r query σ).value i)) j b.value i))
          (alignedFn (rel := NormalForm (ruleRoot rules)) _ _ fun i => (r.correct _).normalForm)
        exact congrArg some (lifted hσ' done sub)
      · rfl
  have all : ∀ (limit : Nat) (todo : List (Point s n)) (index : Nat), (∀ p ∈ todo, p ∈ members) →
      closure rules query keys narrow.branches fuel 0 limit (members.map (terms keys)) todo index =
        .accepted := by
    intro limit todo
    induction todo with
    | nil => intros; rfl
    | cons p rest ih =>
      intro index sub
      simp only [closure,bne_self_eq_false,Bool.false_and,Bool.false_eq_true,↓reduceIte,
        layers p (sub p List.mem_cons_self)]
      exact ih _ (fun x hx => sub x (List.mem_cons_of_mem _ hx))
  exact all _ members 0 (fun _ h => h)

/-- The depth above which the checker decides a family. -/
noncomputable def threshold (canonical : CanonicalPresentation (ruleRoot rules))
    (hb : CheckedReduction.rangeBound rules = true)
    (hv : rules.all (fun r => CheckedVariants.nonvar r.lhs) = true) (q : List (Term s))
    (family : List (Substitution s)) : Nat :=
  depth ((CheckedReduction.rangeBound_iff rules).mp hb) canonical (CheckedVariants.varsNormal rules hv)
    (fun i : Fin q.length => q[i.val]) family

/-- A closed family is accepted at every depth from the threshold on, when no
work limit is set. -/
theorem closed_accepted (canonical : CanonicalPresentation (ruleRoot rules))
    (hb : CheckedReduction.rangeBound rules = true)
    (hv : rules.all (fun r => CheckedVariants.nonvar r.lhs) = true) {q : List (Term s)}
    {family : List (Substitution s)} {fuel : Nat} (enough : threshold canonical hb hv q family ≤ fuel)
    (closed : Closed (ruleRoot rules) q family) : check rules q family fuel 0 = .accepted := by
  let bound := (CheckedReduction.rangeBound_iff rules).mp hb
  let vars := CheckedVariants.varsNormal rules hv
  let query := fun i : Fin q.length => q[i.val]
  let r := ReferenceReduction.reducer rules bound canonical
  have list : List.ofFn query = q := List.ofFn_getElem
  have closed' : Closed (ruleRoot rules) (List.ofFn query) family := list.symm ▸ closed
  have built : family.mapM (member rules query fuel) = some (family.map (reference r query)) :=
    mapM_map_some _ _ fun σ hσ => member_some bound canonical fun i =>
      Nat.lt_of_lt_of_le (depth_bound bound canonical vars (List.mem_append_left _
        (List.mem_append_right _ (List.mem_flatMap.mpr ⟨σ,hσ,List.mem_ofFn.mpr ⟨i,rfl⟩⟩)))) enough
  have normal : (family.map (reference r query)).findIdx?
      (fun p => !normalOn rules (keysOf query) p.assignment) = none := by
    apply List.findIdx?_eq_none_iff.mpr
    intro p hp
    obtain ⟨σ,hσ,rfl⟩ := List.mem_map.mp hp
    rw [normalOn_eq (rules := rules) (query := query),
      (admissible_iff bound _).mpr (reference_formed bound canonical (closed'.normal σ hσ)).1]
    rfl
  unfold check
  simp only [hb,hv,dite_true]
  rw [built]
  dsimp only
  rw [normal]
  dsimp only
  split
  · rfl
  · exact saturated_closed bound canonical vars enough closed'

omit [Interrupt] in
theorem mapM_some_index {α β : Type} (f : α → Option β) {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) {i : Nat} {y : β} (at_i : ys[i]? = some y) :
    ∃ x, xs[i]? = some x ∧ f x = some y := by
  induction xs generalizing ys i with
  | nil =>
    simp at h
    subst ys
    simp at at_i
  | cons a as ih =>
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases tail : as.mapM f with
      | none => simp [ha,tail] at h
      | some bs =>
        simp [ha,tail] at h
        subst ys
        cases i with
        | zero =>
          simp at at_i
          subst y
          exact ⟨a,rfl,ha⟩
        | succ i => exact ih tail (by simpa using at_i)

theorem closure_rejected {keys : List Variable}
    {branches : Point s n → Fin n → List (RootNarrowing.Branch s)}
    {fuel work limit : Nat} {rows : List (List (Term s))} {todo : List (Point s n)} {index reason i : Nat}
    (h : closure rules query keys branches fuel work limit rows todo index = .rejected reason i) :
    reason = 3 ∧ index ≤ i ∧ ∃ p, todo[i - index]? = some p ∧
      closedAt rules query keys branches fuel rows p = some false := by
  induction todo generalizing index with
  | nil => simp [closure] at h
  | cons p rest ih =>
    simp only [closure] at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · obtain ⟨three,le,q,found,bad⟩ := ih h
        refine ⟨three,by omega,q,?_,bad⟩
        have shift : i - index = (i - (index + 1)) + 1 := by omega
        rw [shift,List.getElem?_cons_succ]
        exact found
      · next bad =>
        cases h
        exact ⟨rfl,Nat.le_refl _,p,by simp,bad⟩

/-- A member covers a tuple that it subsumes by any normal forms of its
instantiated query. -/
theorem covered_of_subsumed (bound : ReferenceReduction.Bound rules)
    (canonical : CanonicalPresentation (ruleRoot rules)) {members : List (Point s n)} {m : Point s n}
    (hm : m ∈ members) (formed : Formed rules query m) {values : List (Term s)}
    (done : Completed (ruleRoot rules) (List.ofFn query) m.assignment values) {τ : Substitution s}
    {out : Fin n → Term s} (sub : Subsumed (List.ofFn query) m.assignment values τ (List.ofFn out)) :
    covered (members.map (terms (keysOf query))) ((keysOf query).map τ.image ++ List.ofFn out) = true := by
  let r := ReferenceReduction.reducer rules bound canonical
  obtain ⟨a,rfl,nf⟩ := read_aligned query values done
  have same := subsumes_congr (subsumed_ofFn.mp sub) (a' := m.value) (b' := out)
    (fun i => ((r.correct _).unique _ (nf i)).trans ((r.correct _).unique _ (formed.2 i)).symm)
    (fun _ => .refl _)
  exact covered_complete (c := ⟨τ,out⟩) hm same

/-- What the checker has computed when it reaches the closure test on all
members. -/
theorem reaches_closure (canonical : CanonicalPresentation (ruleRoot rules)) {q : List (Term s)}
    {family : List (Substitution s)} {fuel work reason i : Nat}
    (h : check rules q family fuel work = .rejected reason i) (late : reason = 2 ∨ reason = 3) :
    ∃ (bound : ReferenceReduction.Bound rules) (vars : Normalized (ruleRoot rules) Substitution.identity)
      (members : List (Point s q.length)),
      family.mapM (member rules (fun i : Fin q.length => q[i.val]) fuel) = some members ∧
      (∀ p ∈ members, Formed rules (fun i : Fin q.length => q[i.val]) p) ∧
      saturated rules bound vars (fun i : Fin q.length => q[i.val]) fuel work members = .rejected reason i := by
  unfold check at h
  split at h
  · next hb =>
    split at h
    · next hv =>
      dsimp only at h
      let bound := (CheckedReduction.rangeBound_iff rules).mp hb
      let query := fun i : Fin q.length => q[i.val]
      let r := ReferenceReduction.reducer rules bound canonical
      split at h
      · contradiction
      · next members built =>
        split at h
        · cases h
          omega
        · next normal =>
          have formed (p) (hp : p ∈ members) : Formed rules query p := by
            obtain ⟨σ,_,made⟩ := mapM_some_source _ built p hp
            obtain ⟨rfl,values⟩ := member_form made
            have none_ := List.findIdx?_eq_none_iff.mp normal p hp
            rw [normalOn_eq (query := query)] at none_
            exact ⟨(admissible_iff bound p).mp (by simpa using none_),
              fun i => follow_reduce bound canonical (values i) ▸ (r.correct _).normalForm⟩
          split at h
          · contradiction
          · exact ⟨bound,_,members,built,formed,h⟩
    · cases h
      omega
  · cases h
    omega

/-- A rejection for the first reason names a member that is not normal. -/
theorem rejected_normal {q : List (Term s)} {family : List (Substitution s)} {fuel work i : Nat}
    (h : check rules q family fuel work = .rejected 1 i) :
    ∃ σ, family[i]? = some σ ∧ ¬NormalMember (ruleRoot rules) q σ := by
  unfold check at h
  split at h
  · next hb =>
    split at h
    · dsimp only at h
      let bound := (CheckedReduction.rangeBound_iff rules).mp hb
      let query := fun i : Fin q.length => q[i.val]
      have list : List.ofFn query = q := List.ofFn_getElem
      split at h
      · contradiction
      · next members built =>
        split at h
        · next index found =>
          cases h
          have bad := List.of_findIdx?_eq_some found
          split at bad
          · next p at_i =>
            obtain ⟨σ,hσ,made⟩ := mapM_some_index _ built at_i
            obtain rfl := (member_form made).1
            refine ⟨_,hσ,fun normal => ?_⟩
            have ok := (admissible_iff (query := query) bound p).mpr fun k =>
              normal k.val (by
                simpa only [query,List.ofFn_getElem] using (observed query k.val).mp k.property)
            rw [normalOn_eq (rules := rules) (query := query),ok] at bad
            exact absurd bad (by simp)
          · contradiction
        · split at h
          · contradiction
          · unfold saturated at h
            dsimp only at h
            split at h
            · contradiction
            · split at h
              · exact absurd (closure_rejected h).1 (by decide)
              · cases h
    · cases h
  · cases h

/-- A rejection for the second reason means that no member subsumes the
normalized query. -/
theorem rejected_start (canonical : CanonicalPresentation (ruleRoot rules)) {q : List (Term s)}
    {family : List (Substitution s)} {fuel work i : Nat}
    (h : check rules q family fuel work = .rejected 2 i) : ¬Starts (ruleRoot rules) q family := by
  obtain ⟨bound,vars,members,built,formed,verdict⟩ := reaches_closure canonical h (.inl rfl)
  let query := fun i : Fin q.length => q[i.val]
  let r := ReferenceReduction.reducer rules bound canonical
  have list : List.ofFn query = q := List.ofFn_getElem
  rw [← list]
  rintro ⟨σ,hσ,values,first,done,plain,sub⟩
  obtain ⟨m,hm,made⟩ := mapM_some_mem _ built σ hσ
  obtain rfl := (member_form made).1
  unfold saturated at verdict
  dsimp only at verdict
  split at verdict
  · contradiction
  · next computed seeded =>
    obtain ⟨k,rfl,each⟩ := mapM_ofFn _ seeded
    obtain ⟨b,rfl,nf⟩ := read_aligned query first plain
    have moved : Subsumed (List.ofFn query) m.assignment values .identity (List.ofFn k) := by
      obtain ⟨θ,inputs,outputs⟩ := sub
      obtain ⟨a,rfl,_⟩ := read_aligned query values done
      refine ⟨θ,inputs,alignedFn (rel := fun u w => EquivB u (θ.apply w)) _ _ fun i => ?_⟩
      have at_i := VariantSaturation.atFn (rel := fun u w => EquivB u (θ.apply w)) b a outputs i
      have form := nf i
      rw [Substitution.apply_identity] at form
      rw [follow_reduce bound canonical (each i)]
      exact ((r.correct _).unique _ form).symm.trans at_i
    rw [covered_of_subsumed bound canonical hm (formed m hm) done moved] at verdict
    exact absurd (closure_rejected verdict).1 (by decide)

/-- A rejection for the third reason names a member with a normalized
narrowing successor that no member subsumes. -/
theorem rejected_step (canonical : CanonicalPresentation (ruleRoot rules)) {q : List (Term s)}
    {family : List (Substitution s)} {fuel work i : Nat}
    (h : check rules q family fuel work = .rejected 3 i) :
    ∃ σ, family[i]? = some σ ∧ ¬Folds (ruleRoot rules) q family σ := by
  obtain ⟨bound,vars,members,built,formed,verdict⟩ := reaches_closure canonical h (.inr rfl)
  let query := fun i : Fin q.length => q[i.val]
  let keys := keysOf query
  let r := ReferenceReduction.reducer rules bound canonical
  let narrow := TableNarrowing.checking bound vars query
  have list : List.ofFn query = q := List.ofFn_getElem
  unfold saturated at verdict
  dsimp only at verdict
  split at verdict
  · contradiction
  · split at verdict
    · obtain ⟨_,_,p,at_i,bad⟩ := closure_rejected verdict
      rw [Nat.sub_zero] at at_i
      have hp : p ∈ members := List.mem_of_getElem? at_i
      obtain ⟨σ,hσ,made⟩ := mapM_some_index _ built at_i
      obtain rfl := (member_form made).1
      refine ⟨_,hσ,?_⟩
      intro folds_
      have folds : Folds (ruleRoot rules) (List.ofFn query) family p.assignment := by
        simpa only [query,List.ofFn_getElem] using folds_
      obtain ⟨j,b,_,hb,child⟩ := closedAt_false bad
      · unfold childOk at child
        dsimp only at child
        split at child
        · next quiet_ =>
          obtain ⟨values,made',miss⟩ := Option.map_eq_some_iff.mp child
          obtain ⟨k,rfl,each⟩ := mapM_ofFn _ made'
          have live : ∀ v, Observed (List.ofFn query) v →
              Normal (ruleRoot rules) (b.subst.apply (p.assignment.image v)) := by
            intro v hv
            have key := (observed query v).mpr hv
            exact quiet_normal bound (List.all_eq_true.mp quiet_ _
              (List.mem_map_of_mem (f := (b.subst.compose p.assignment).image) key))
          have step := narrow.genuine _ (sound_member vars _ (formed p hp)) j b hb
          obtain ⟨σ',hσ',values',done,sub⟩ := folds (List.ofFn p.value)
            (completed_ofFn.mpr (formed p hp).2) b.subst live
            (List.ofFn (replace (fun i => b.subst.apply (p.value i)) j b.value))
            (by rw [List.map_ofFn]; exact oneStep_replace _ j step)
            (List.ofFn k)
            (alignedFn (rel := NormalForm (ruleRoot rules)) _ _ fun i =>
              follow_reduce bound canonical (each i) ▸ (r.correct _).normalForm)
          obtain ⟨m,hm,made''⟩ := mapM_some_mem _ built σ' hσ'
          obtain rfl := (member_form made'').1
          rw [covered_of_subsumed bound canonical hm (formed m hm) done sub] at miss
          exact absurd miss (by simp)
        · cases child
    · cases verdict

/-- A rejection for the fourth reason means that the table has a variable
left side or an unbound right-side variable. -/
theorem rejected_table {q : List (Term s)} {family : List (Substitution s)} {fuel work i : Nat}
    (h : check rules q family fuel work = .rejected 4 i) :
    ¬(CheckedReduction.rangeBound rules = true ∧ rules.all (fun r => CheckedVariants.nonvar r.lhs) = true) := by
  rintro ⟨hb,hv⟩
  unfold check at h
  simp only [hb,hv,dite_true] at h
  split at h
  · contradiction
  · split at h
    · cases h
    · split at h
      · contradiction
      · unfold saturated at h
        dsimp only at h
        split at h
        · contradiction
        · split at h
          · exact absurd (closure_rejected h).1 (by decide)
          · cases h

/-- From the threshold on, and without a work limit, the checker decides. -/
theorem decided (canonical : CanonicalPresentation (ruleRoot rules))
    (hb : CheckedReduction.rangeBound rules = true)
    (hv : rules.all (fun r => CheckedVariants.nonvar r.lhs) = true) {q : List (Term s)}
    {family : List (Substitution s)} {fuel : Nat} (enough : threshold canonical hb hv q family ≤ fuel) :
    check rules q family fuel 0 ≠ .exhausted := by
  let bound := (CheckedReduction.rangeBound_iff rules).mp hb
  let vars := CheckedVariants.varsNormal rules hv
  let query := fun i : Fin q.length => q[i.val]
  let keys := keysOf query
  let r := ReferenceReduction.reducer rules bound canonical
  let narrow := TableNarrowing.checking bound vars query
  have high {t : Term s} (h : t ∈ demand bound canonical vars query family) :
      ReductionHeight.height bound canonical.terminating t < fuel :=
    Nat.lt_of_lt_of_le (depth_bound bound canonical vars h) enough
  have built : family.mapM (member rules query fuel) = some (family.map (reference r query)) :=
    mapM_map_some _ _ fun σ hσ => member_some bound canonical fun i =>
      high (List.mem_append_left _
        (List.mem_append_right _ (List.mem_flatMap.mpr ⟨σ,hσ,List.mem_ofFn.mpr ⟨i,rfl⟩⟩)))
  unfold check
  simp only [hb,hv,dite_true]
  rw [built]
  dsimp only
  split
  · exact fun bad => nomatch bad
  · split
    · exact fun bad => nomatch bad
    · unfold saturated
      dsimp only
      rw [settle_some bound canonical (fun i => high (List.mem_append_left _
        (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩))))]
      dsimp only
      split
      · have layers : ∀ p ∈ family.map (reference r query),
            closedAt rules query keys narrow.branches fuel
              ((family.map (reference r query)).map (terms keys)) p ≠ none := by
          intro p hp
          obtain ⟨σ,hσ,rfl⟩ := List.mem_map.mp hp
          suffices strict : strictAt rules query keys narrow.branches fuel
              ((family.map (reference r query)).map (terms keys)) (reference r query σ) ≠ none by
            cases value : strictAt rules query keys narrow.branches fuel
                ((family.map (reference r query)).map (terms keys)) (reference r query σ) with
            | none => exact absurd value strict
            | some v => rw [closedAt_of_strict value]; exact fun bad => nomatch bad
          apply every_decided
          intro j _
          split
          · exact fun bad => nomatch bad
          · apply every_decided
            intro b hb
            unfold childOk
            dsimp only
            split
            · rw [settle_some bound canonical (fun i => high (List.mem_append_right _
                (List.mem_flatMap.mpr ⟨σ,hσ,List.mem_flatMap.mpr ⟨j,List.mem_finRange j,
                  List.mem_flatMap.mpr ⟨b,hb,List.mem_ofFn.mpr ⟨i,rfl⟩⟩⟩⟩)))]
              exact fun bad => nomatch bad
            · exact fun bad => nomatch bad
        have all : ∀ (limit : Nat) (todo : List (Point s q.length)) (index : Nat),
            (∀ p ∈ todo, p ∈ family.map (reference r query)) →
            closure rules query keys narrow.branches fuel 0 limit
              ((family.map (reference r query)).map (terms keys)) todo index ≠ .exhausted := by
          intro limit todo
          induction todo with
          | nil => exact fun _ _ bad => nomatch bad
          | cons p rest ih =>
            intro index sub
            simp only [closure,bne_self_eq_false,Bool.false_and,Bool.false_eq_true,↓reduceIte]
            split
            · next none_ => exact absurd none_ (layers p (sub p List.mem_cons_self))
            · exact ih _ (fun x hx => sub x (List.mem_cons_of_mem _ hx))
            · exact fun bad => nomatch bad
        exact all _ _ 0 (fun _ h => h)
      · exact fun bad => nomatch bad

/-- The checker rejects for one of four reasons. -/
theorem rejected_reason {q : List (Term s)} {family : List (Substitution s)} {fuel work reason i : Nat}
    (h : check rules q family fuel work = .rejected reason i) :
    reason = 1 ∨ reason = 2 ∨ reason = 3 ∨ reason = 4 := by
  unfold check at h
  split at h
  · split at h
    · dsimp only at h
      split at h
      · contradiction
      · split at h
        · cases h; exact .inl rfl
        · split at h
          · contradiction
          · unfold saturated at h
            dsimp only at h
            split at h
            · contradiction
            · split at h
              · exact .inr (.inr (.inl (closure_rejected h).1))
              · cases h; exact .inr (.inl rfl)
    · cases h; exact .inr (.inr (.inr rfl))
  · cases h; exact .inr (.inr (.inr rfl))

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] [Interrupt] in
theorem nonvar_iff (rules : List (Equation s)) :
    rules.all (fun r => CheckedVariants.nonvar r.lhs) = true ↔ ∀ r ∈ rules, ∀ v, r.lhs ≠ .var v := by
  rw [List.all_eq_true]
  constructor
  · intro h r hr v eq
    have ok := h r hr
    rw [eq] at ok
    cases ok
  · intro h r hr
    cases eq : r.lhs with
    | var v => exact absurd eq (h r hr v)
    | atom _ => rfl
    | free _ _ => rfl
    | comm _ _ _ => rfl
    | ac _ _ _ => rfl

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] [Interrupt] in
/-- On a canonical presentation no left side is a variable. -/
theorem nonvar_canonical (canonical : CanonicalPresentation (ruleRoot rules)) :
    rules.all (fun r => CheckedVariants.nonvar r.lhs) = true := by
  apply (nonvar_iff rules).mpr
  intro r hr v eq
  apply TableNarrowing.variablesNormal canonical v (Substitution.identity.apply r.rhs)
  exact ⟨_,_,.refl _,.root ⟨r,hr,.identity,by rw [eq]; rfl,rfl⟩,.refl _⟩

/-- A rejection names a clause of closedness that fails: a member that is
not normal, the absence of a member that subsumes the normalized query, a
member with a successor that no member subsumes, or a table that is not
range restricted or has a variable left side. -/
theorem rejected_cases (canonical : CanonicalPresentation (ruleRoot rules)) {q : List (Term s)}
    {family : List (Substitution s)} {fuel work reason i : Nat}
    (h : check rules q family fuel work = .rejected reason i) :
    (reason = 1 ∧ ∃ σ, family[i]? = some σ ∧ ¬NormalMember (ruleRoot rules) q σ) ∨
    (reason = 2 ∧ ¬Starts (ruleRoot rules) q family) ∨
    (reason = 3 ∧ ∃ σ, family[i]? = some σ ∧ ¬Folds (ruleRoot rules) q family σ) ∨
    (reason = 4 ∧ ¬(ReferenceReduction.Bound rules ∧ ∀ r ∈ rules, ∀ v, r.lhs ≠ .var v)) := by
  rcases rejected_reason h with rfl | rfl | rfl | rfl
  · exact .inl ⟨rfl,rejected_normal h⟩
  · exact .inr (.inl ⟨rfl,rejected_start canonical h⟩)
  · exact .inr (.inr (.inl ⟨rfl,rejected_step canonical h⟩))
  · exact .inr (.inr (.inr ⟨rfl,fun ⟨bound,nonvar⟩ => rejected_table h
      ⟨(CheckedReduction.rangeBound_iff rules).mpr bound,(nonvar_iff rules).mpr nonvar⟩⟩))

/-- On a range-restricted canonical presentation there is a depth from which
the checker, without a work limit, never reports an exhausted budget and
accepts exactly the closed families. -/
theorem decides (bound : ReferenceReduction.Bound rules)
    (canonical : CanonicalPresentation (ruleRoot rules)) (q : List (Term s))
    (family : List (Substitution s)) :
    ∃ k : Nat, ∀ fuel, k ≤ fuel → check rules q family fuel 0 ≠ .exhausted ∧
      (check rules q family fuel 0 = .accepted ↔ Closed (ruleRoot rules) q family) := by
  have hb := (CheckedReduction.rangeBound_iff rules).mpr bound
  have hv := nonvar_canonical canonical
  exact ⟨threshold canonical hb hv q family,fun fuel enough =>
    ⟨decided canonical hb hv enough,accepted_closed canonical,closed_accepted canonical hb hv enough⟩⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] [Interrupt] in
/-- The slot of the step and its result. -/
theorem oneStep_slot {R : Root s} {a : Fin n → Term s} {raw : List (Term s)}
    (h : OneStep R (List.ofFn a) raw) :
    ∃ j u, StepModulo R (a j) u ∧ raw = List.ofFn (replace a j u) := by
  induction n generalizing raw with
  | zero => simp at h; cases h
  | succ n ih =>
    rw [List.ofFn_succ] at h
    cases h with
    | here ts step =>
      refine ⟨0,_,step,?_⟩
      rw [List.ofFn_succ]
      simp [replace,Fin.succ_ne_zero]
    | later t rest =>
      obtain ⟨j,u,step,rfl⟩ := ih rest
      refine ⟨j.succ,u,step,?_⟩
      rw [List.ofFn_succ]
      have head : replace a j.succ u 0 = a 0 := by simp [replace,(Fin.succ_ne_zero j).symm]
      have tail : (fun i : Fin n => replace a j.succ u i.succ) = replace (fun i => a i.succ) j u := by
        funext i
        simp [replace,Fin.succ_inj]
      rw [head,tail]

omit [Interrupt] in
theorem filter_length_lt {α : Type} {f g : α → Bool} {xs : List α}
    (imp : ∀ x ∈ xs, f x = true → g x = true) {a : α} (ha : a ∈ xs) (ga : g a = true)
    (fa : f a = false) : (xs.filter f).length < (xs.filter g).length := by
  induction xs with
  | nil => exact nomatch ha
  | cons x xs ih =>
    have le : (xs.filter f).length ≤ (xs.filter g).length := by
      clear ih ha
      induction xs with
      | nil => simp
      | cons y ys ih2 =>
        have rest := ih2 fun z hz => imp z (by simp [List.mem_cons] at hz ⊢; rcases hz with rfl | hz <;> simp [*])
        have at_y := imp y (List.mem_cons_of_mem _ List.mem_cons_self)
        cases fy : f y <;> cases gy : g y <;> simp [fy,gy] <;> simp [fy,gy] at at_y <;> omega
    rcases List.mem_cons.mp ha with rfl | later
    · simp [ga,fa]
      omega
    · have shorter := ih (fun z hz => imp z (List.mem_cons_of_mem _ hz)) later
      have at_x := imp x List.mem_cons_self
      cases fx : f x <;> cases gx : g x <;> simp [fx,gx] <;> simp [fx,gx] at at_x <;> omega

theorem follow_none {fuel : Nat} {t : Term s} (bound : ReferenceReduction.Bound rules)
    (h : ReferenceReduction.follow rules fuel t = none) : ¬CheckedReduction.Within rules fuel t := by
  intro tree
  obtain ⟨u,found⟩ := CheckedReduction.choose_of_within bound fuel t tree
  rw [← CertifiedReductionWire.follow_eq,h] at found
  cases found

theorem settle_none {fuel : Nat} {raw : Fin n → Term s} (bound : ReferenceReduction.Bound rules)
    (h : settle rules fuel raw = none) : ∃ i, ¬CheckedReduction.Within rules fuel (raw i) := by
  obtain ⟨t,ht,bad⟩ := mapM_none _ h
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
  exact ⟨i,follow_none bound bad⟩

/-- Among the successors of a member whose normal forms the depth does not
reach and that are instances of no successor that passed, one is most
general. -/
theorem pending_general (bound : ReferenceReduction.Bound rules)
    (vars : Normalized (ruleRoot rules) Substitution.identity) {fuel : Nat}
    {rows : List (List (Term s))} {p : Point s n} (formed : Formed rules query p)
    (clean : ∀ j b, idle (query j) = false →
      b ∈ (TableNarrowing.checking bound vars query).branches p j →
      childOk rules (keysOf query) fuel rows p j b ≠ some false) (k : Nat) :
    ∀ j b, idle (query j) = false → b ∈ (TableNarrowing.checking bound vars query).branches p j →
      childOk rules (keysOf query) fuel rows p j b = none →
      (∀ j0 b0, idle (query j0) = false →
        b0 ∈ (TableNarrowing.checking bound vars query).branches p j0 →
        childOk rules (keysOf query) fuel rows p j0 b0 = some true →
        ((keysOf query).map (b0.subst.compose p.assignment).image).all (quiet rules) = true →
        instanceOf (terms (keysOf query) (successor p j0 b0))
          (terms (keysOf query) (successor p j b)) = false) →
      ((layer query (TableNarrowing.checking bound vars query).branches p).filter fun e =>
        instanceOf (terms (keysOf query) (successor p e.1 e.2)) (terms (keysOf query) (successor p j b)) &&
          !instanceOf (terms (keysOf query) (successor p j b))
            (terms (keysOf query) (successor p e.1 e.2))).length = k →
      ∃ j' b', idle (query j') = false ∧
        b' ∈ (TableNarrowing.checking bound vars query).branches p j' ∧
        childOk rules (keysOf query) fuel rows p j' b' = none ∧
        MostGeneral (ruleRoot rules) (List.ofFn query) p.assignment (List.ofFn p.value) b'.subst
          (List.ofFn (successor p j' b').value) := by
  classical
  let keys := keysOf query
  let narrow := TableNarrowing.checking bound vars query
  have sound := sound_member vars p formed
  induction k using Nat.strongRecOn with
  | ind k smaller =>
    intro j b live hb pending alone rank
    by_cases general : MostGeneral (ruleRoot rules) (List.ofFn query) p.assignment (List.ofFn p.value)
        b.subst (List.ofFn (successor p j b).value)
    · exact ⟨j,b,live,hb,pending,general⟩
    · unfold MostGeneral at general
      simp only [Classical.not_forall] at general
      obtain ⟨τ,raw,⟨normal,step⟩,above,below⟩ := general
      rw [List.map_ofFn] at step
      obtain ⟨j1,u,step1,rfl⟩ := oneStep_slot step
      have above' := subsumed_ofFn.mp above
      have below' : ¬((successor p j b).row keys).Subsumes
          ((⟨τ.compose p.assignment,replace (τ.apply ∘ p.value) j1 u⟩ : Point s n).row keys) :=
        fun sub => below (subsumed_ofFn.mpr sub)
      have hn (i : Key keys) : Normal (ruleRoot rules) (τ.apply ((p.row keys).input i)) :=
        normal i.val ((observed query i.val).mp i.property)
      obtain ⟨_,hm,η,fit⟩ := expand_covers keys p (narrow.branches p) (narrow.lifts p sound) τ hn j1 u step1
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hm
      obtain ⟨j2,_,hj⟩ := List.mem_flatMap.mp hc
      obtain ⟨b2,hb2,rfl⟩ := List.mem_map.mp hj
      have over : ((successor p j2 b2).row keys).Subsumes
          ((⟨τ.compose p.assignment,replace (τ.apply ∘ p.value) j1 u⟩ : Point s n).row keys) := ⟨η,fit⟩
      have covers := over.trans above'
      have strict : ¬((successor p j b).row keys).Subsumes ((successor p j2 b2).row keys) :=
        fun sub => below' (sub.trans over)
      have live2 (i : Key keys) : Normal (ruleRoot rules) ((successor p j2 b2).assignment.image i.val) :=
        normal_of_instance ((normal_equiv _ (fit.inputs i)).mp (hn i))
      have moving : idle (query j2) = false := by
        cases still : idle (query j2) with
        | false => rfl
        | true => exact absurd live2 (idle_reducible vars narrow formed still hb2)
      have quiet2 : (keys.map (b2.subst.compose p.assignment).image).all (quiet rules) = true := by
        have ok := (admissible_iff (query := query) bound (successor p j2 b2)).mpr live2
        rw [← normalOn_eq (rules := rules) (query := query)] at ok
        simpa [normalOn,List.all_map] using ok
      have hit := instanceOf_complete covers
      cases outcome : childOk rules keys fuel rows p j2 b2 with
      | some value =>
        cases value with
        | false => exact absurd outcome (clean j2 b2 moving hb2)
        | true =>
          rw [alone j2 b2 moving hb2 outcome quiet2] at hit
          cases hit
      | none =>
        apply smaller _ (rank ▸ ?_) j2 b2 moving hb2 outcome ?_ rfl
        · apply filter_length_lt (a := (j2,b2))
          · intro e _ both
            simp only [Bool.and_eq_true,Bool.not_eq_true'] at both ⊢
            refine ⟨instanceOf_complete ((instanceOf_sound both.1).trans covers),?_⟩
            cases back : instanceOf (terms keys (successor p j b)) (terms keys (successor p e.1 e.2)) with
            | false => rfl
            | true => exact absurd ((instanceOf_sound back).trans (instanceOf_sound both.1)) strict
          · exact mem_layer.mpr ⟨moving,hb2⟩
          · simp only [Bool.and_eq_true,Bool.not_eq_true']
            refine ⟨hit,?_⟩
            cases back : instanceOf (terms keys (successor p j b)) (terms keys (successor p j2 b2)) with
            | false => rfl
            | true => exact absurd (instanceOf_sound back) strict
          · simp
        · intro j0 b0 live0 hb0 ok quiet0
          cases found : instanceOf (terms keys (successor p j0 b0)) (terms keys (successor p j2 b2)) with
          | false => rfl
          | true =>
            have through := instanceOf_complete ((instanceOf_sound found).trans covers)
            rw [alone j0 b0 live0 hb0 ok quiet0] at through
            cases through

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] [Interrupt] in
theorem admitted_short {work : Nat} {charges : List Nat} {spent : Nat}
    (h : admitted work spent charges < charges.length) : work < spent + charges.sum := by
  induction charges generalizing spent with
  | nil => simp at h
  | cons c cs ih =>
    unfold admitted at h
    split at h
    · simp only [List.sum_cons]
      omega
    · have rest := ih (spent := spent + c) (by simp only [List.length_cons] at h; omega)
      simp only [List.sum_cons]
      omega

theorem closure_exhausted {keys : List Variable}
    {branches : Point s n → Fin n → List (RootNarrowing.Branch s)}
    {fuel work limit : Nat} {rows : List (List (Term s))} {todo : List (Point s n)} {index : Nat}
    (h : closure rules query keys branches fuel work limit rows todo index = .exhausted) :
    (work ≠ 0 ∧ limit < index + todo.length) ∨
      ∃ p ∈ todo, closedAt rules query keys branches fuel rows p = none := by
  induction todo generalizing index with
  | nil => simp [closure] at h
  | cons p rest ih =>
    simp only [closure] at h
    split at h
    · next stop =>
      simp only [Bool.and_eq_true,bne_iff_ne,ne_eq,decide_eq_true_eq] at stop
      exact .inl ⟨stop.1,by simp only [List.length_cons]; omega⟩
    · split at h
      · next open_ => exact .inr ⟨p,List.mem_cons_self,open_⟩
      · rcases ih h with ⟨limited,short⟩ | ⟨x,hx,open_⟩
        · exact .inl ⟨limited,by simp only [List.length_cons]; omega⟩
        · exact .inr ⟨x,List.mem_cons_of_mem _ hx,open_⟩
      · cases h

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] [Interrupt] in
theorem charge_eq (p : Point s n) : charge query p = Charge (List.ofFn query) (List.ofFn p.value) := by
  unfold charge Charge
  have listed : (List.ofFn fun i => (query i,p.value i)) =
      (List.finRange n).map fun i => (query i,p.value i) := by
    apply List.ext_getElem <;> simp
  rw [List.zip_eq_zipWith,zipWith_ofFn,listed,List.map_map]
  rfl

/-- Why the closure test reports an exhausted budget: a term it has to
normalize has a rewrite path as long as the depth, or the work limit is below
the positions of the narrowing layers. -/
theorem saturated_exhausted (bound : ReferenceReduction.Bound rules)
    (vars : Normalized (ruleRoot rules) Substitution.identity) {family : List (Substitution s)}
    {fuel work : Nat} {members : List (Point s n)} (formed : ∀ p ∈ members, Formed rules query p)
    (source : ∀ p ∈ members, p.assignment ∈ family)
    (rows : Aligned (Completed (ruleRoot rules) (List.ofFn query)) family
      (members.map fun p => List.ofFn p.value))
    (h : saturated rules bound vars query fuel work members = .exhausted) :
    (∃ t, Demand (ruleRoot rules) (List.ofFn query) family t ∧ ¬CheckedReduction.Within rules fuel t) ∨
      (work ≠ 0 ∧ Overcharged (ruleRoot rules) (List.ofFn query) family work) := by
  let keys := keysOf query
  let narrow := TableNarrowing.checking bound vars query
  unfold saturated at h
  dsimp only at h
  split at h
  · next open_ =>
    obtain ⟨i,long⟩ := settle_none bound open_
    exact .inl ⟨_,.query (List.mem_ofFn.mpr ⟨i,rfl⟩),long⟩
  · split at h
    · rcases closure_exhausted h with ⟨limited,short⟩ | ⟨p,hp,open_⟩
      · refine .inr ⟨limited,_,rows,?_⟩
        have total := admitted_short (work := work) (spent := 0)
          (charges := members.map (charge query)) (by simpa using short)
        rw [List.map_map]
        have same : (Charge (List.ofFn query) ∘ fun p : Point s n => List.ofFn p.value) = charge query := by
          funext p
          exact (charge_eq p).symm
        rw [same]
        omega
      · obtain ⟨clean,j,b,live,hb,pending,alone⟩ := closedAt_none open_
        obtain ⟨j',b',_,hb',pending',general⟩ := pending_general bound vars (formed p hp) clean _
          j b live hb pending alone rfl
        unfold childOk at pending'
        dsimp only at pending'
        split at pending'
        · next quiet_ =>
          have open' : settle rules fuel (successor p j' b').value = none := by
            cases made : settle rules fuel (successor p j' b').value with
            | none => rfl
            | some values => rw [made] at pending'; cases pending'
          obtain ⟨i,long⟩ := settle_none bound open'
          have normal : ∀ v, Observed (List.ofFn query) v →
              Normal (ruleRoot rules) (b'.subst.apply (p.assignment.image v)) := by
            intro v hv
            have key := (observed query v).mpr hv
            exact quiet_normal bound (List.all_eq_true.mp quiet_ _
              (List.mem_map_of_mem (f := (b'.subst.compose p.assignment).image) key))
          have step := narrow.genuine _ (sound_member vars _ (formed p hp)) j' b' hb'
          exact .inl ⟨_,.successor (source p hp) (completed_ofFn.mpr (formed p hp).2)
            ⟨normal,by rw [List.map_ofFn]; exact oneStep_replace _ j' step⟩ general
            (List.mem_ofFn.mpr ⟨i,rfl⟩),long⟩
        · cases pending'
    · cases h

theorem member_rows {family : List (Substitution s)} {fuel : Nat} {members : List (Point s n)}
    (built : family.mapM (member rules query fuel) = some members)
    (formed : ∀ p ∈ members, Formed rules query p) :
    Aligned (Completed (ruleRoot rules) (List.ofFn query)) family
      (members.map fun p => List.ofFn p.value) := by
  induction family generalizing members with
  | nil =>
    simp at built
    subst members
    trivial
  | cons σ rest ih =>
    cases head : member rules query fuel σ with
    | none => simp [head] at built
    | some m =>
      cases tail : rest.mapM (member rules query fuel) with
      | none => simp [head,tail] at built
      | some ms =>
        simp [head,tail] at built
        subst members
        refine ⟨?_,ih tail fun p hp => formed p (List.mem_cons_of_mem _ hp)⟩
        have at_m := (formed m List.mem_cons_self).2
        rw [(member_form head).1] at at_m
        exact completed_ofFn.mpr at_m

/-- Why the checker reports an exhausted budget. On a canonical presentation
a term that a check has to normalize (the query, an instantiated query, or a
value of a most general narrowing successor of a member) has a rewrite path
as long as the depth, or the work limit is nonzero and below the positions of
the narrowing layers of the members. -/
theorem exhausted_cases (canonical : CanonicalPresentation (ruleRoot rules)) {q : List (Term s)}
    {family : List (Substitution s)} {fuel work : Nat}
    (h : check rules q family fuel work = .exhausted) :
    (∃ t, Demand (ruleRoot rules) q family t ∧ ¬CheckedReduction.Within rules fuel t) ∨
      (work ≠ 0 ∧ Overcharged (ruleRoot rules) q family work) := by
  let query := fun i : Fin q.length => q[i.val]
  have list : List.ofFn query = q := List.ofFn_getElem
  rw [← list]
  unfold check at h
  split at h
  · next hb =>
    split at h
    · next hv =>
      dsimp only at h
      let bound := (CheckedReduction.rangeBound_iff rules).mp hb
      let r := ReferenceReduction.reducer rules bound canonical
      split at h
      · next open_ =>
        obtain ⟨σ,hσ,bad⟩ := mapM_none _ open_
        have unsettled : settle rules fuel (fun i => σ.apply (query i)) = none := by
          unfold member at bad
          cases made : settle rules fuel (fun i => σ.apply (query i)) with
          | none => rfl
          | some values => rw [made] at bad; cases bad
        obtain ⟨i,long⟩ := settle_none bound unsettled
        exact .inl ⟨_,.member hσ (List.mem_ofFn.mpr ⟨i,rfl⟩),long⟩
      · next members built =>
        split at h
        · cases h
        · next normal =>
          have formed (p) (hp : p ∈ members) : Formed rules query p := by
            obtain ⟨σ,_,made⟩ := mapM_some_source _ built p hp
            obtain ⟨rfl,values⟩ := member_form made
            have none_ := List.findIdx?_eq_none_iff.mp normal p hp
            rw [normalOn_eq (query := query)] at none_
            exact ⟨(admissible_iff bound p).mp (by simpa using none_),
              fun i => follow_reduce bound canonical (values i) ▸ (r.correct _).normalForm⟩
          have source (p) (hp : p ∈ members) : p.assignment ∈ family := by
            obtain ⟨σ,hσ,made⟩ := mapM_some_source _ built p hp
            exact (member_form made).1 ▸ hσ
          have rows := member_rows built formed
          split at h
          · cases h
          · exact saturated_exhausted bound _ formed source rows h
    · cases h
  · cases h

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] [Interrupt] in
theorem stepModulo_source {R : Root s} {a a' u : Term s} (same : EquivB a' a)
    (step : StepModulo R a u) : StepModulo R a' u := by
  obtain ⟨l,r,start,one,finish⟩ := step
  exact ⟨l,r,same.trans start,one,finish⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] [Interrupt] in
theorem replace_equiv {x y : Fin n → Term s} (same : ∀ i, EquivB (x i) (y i)) (j : Fin n) (u : Term s)
    (i : Fin n) : EquivB (replace x j u i) (replace y j u i) := by
  unfold replace
  split
  · exact .refl _
  · exact same i

/-- The terms a check has to normalize have bounded rewrite paths: every
most general successor of a member is, up to the declared laws, one of the
finitely many that a complete narrowing layer lists. So the clause that
limits an exhausted budget is not empty. -/
theorem demand_within (canonical : CanonicalPresentation (ruleRoot rules))
    (hb : CheckedReduction.rangeBound rules = true)
    (hv : rules.all (fun r => CheckedVariants.nonvar r.lhs) = true) (q : List (Term s))
    (family : List (Substitution s)) (t : Term s) (needed : Demand (ruleRoot rules) q family t) :
    CheckedReduction.Within rules (threshold canonical hb hv q family) t := by
  let bound := (CheckedReduction.rangeBound_iff rules).mp hb
  let vars := CheckedVariants.varsNormal rules hv
  let query := fun i : Fin q.length => q[i.val]
  let keys := keysOf query
  let r := ReferenceReduction.reducer rules bound canonical
  let narrow := TableNarrowing.checking bound vars query
  let height := ReductionHeight.height bound canonical.terminating
  have list : List.ofFn query = q := List.ofFn_getElem
  suffices low : height t < depth bound canonical vars query family from
    (CheckedReduction.settled_of_height bound canonical _ t low).1
  rw [← list] at needed
  cases needed with
  | query ht => exact depth_bound bound canonical vars (List.mem_append_left _ (List.mem_append_left _ ht))
  | member hσ ht =>
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
    exact depth_bound bound canonical vars (List.mem_append_left _
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_,hσ,List.mem_ofFn.mpr ⟨i,rfl⟩⟩)))
  | @successor σ τ values raw _ hσ done next general ht =>
    obtain ⟨a,rfl,nf⟩ := read_aligned query values done
    obtain ⟨normal,step⟩ := next
    rw [List.map_ofFn] at step
    obtain ⟨j,u,step1,rfl⟩ := oneStep_slot step
    let p := reference r query σ
    have same (i) : EquivB (a i) (p.value i) := (r.correct _).unique _ (nf i)
    have formed : Formed rules query p := reference_formed bound canonical fun v hv =>
      normal_of_instance (normal v hv)
    have sound := sound_member vars p formed
    have hn (i : Key keys) : Normal (ruleRoot rules) (τ.apply ((p.row keys).input i)) :=
      normal i.val ((observed query i.val).mp i.property)
    obtain ⟨_,hm,η,fit⟩ := expand_covers keys p (narrow.branches p) (narrow.lifts p sound) τ hn j u
      (stepModulo_source ((same j).symm.subst τ.image) step1)
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hm
    obtain ⟨j2,_,hj⟩ := List.mem_flatMap.mp hc
    obtain ⟨b2,hb2,rfl⟩ := List.mem_map.mp hj
    have other : Successor (ruleRoot rules) (List.ofFn query) σ (List.ofFn a) b2.subst
        (List.ofFn (replace (b2.subst.apply ∘ a) j2 b2.value)) := by
      refine ⟨fun v hv => ?_,?_⟩
      · have key := (observed query v).mpr hv
        exact normal_of_instance ((normal_equiv _ (fit.inputs ⟨v,key⟩)).mp (normal v hv))
      · rw [List.map_ofFn]
        exact oneStep_replace _ j2 (stepModulo_source ((same j2).subst b2.subst.image)
          (narrow.genuine p sound j2 b2 hb2))
    have above : Subsumed (List.ofFn query) (b2.subst.compose σ)
        (List.ofFn (replace (b2.subst.apply ∘ a) j2 b2.value)) (τ.compose σ)
        (List.ofFn (replace (τ.apply ∘ a) j u)) := by
      refine subsumed_ofFn.mpr ⟨η,fit.inputs,fun i => ?_⟩
      exact (replace_equiv (fun i => (same i).subst τ.image) j u i).trans ((fit.values i).trans
        ((replace_equiv (fun i => (same i).subst b2.subst.image) j2 b2.value i).subst η.image).symm)
    obtain ⟨θ,_,back⟩ := subsumed_ofFn.mp (general _ _ other above)
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
    have grows : height (replace (τ.apply ∘ a) j u i) ≤ height (θ.apply (replace (τ.apply ∘ a) j u i)) :=
      ReductionHeight.le_rank bound canonical.terminating (fun t => height (θ.apply t))
        (fun st => ReductionHeight.step bound _ (SpecializedFresh.stepModulo_subst rules θ st)) _
    have moved : height (θ.apply (replace (τ.apply ∘ a) j u i)) =
        height ((successor p j2 b2).value i) :=
      (ReductionHeight.equiv bound canonical.terminating (back i)).symm.trans
        (ReductionHeight.equiv bound canonical.terminating
          (replace_equiv (fun i => (same i).subst b2.subst.image) j2 b2.value i))
    have listed : (successor p j2 b2).value i ∈ demand bound canonical vars query family :=
      List.mem_append_right _ (List.mem_flatMap.mpr ⟨σ,hσ,List.mem_flatMap.mpr
        ⟨j2,List.mem_finRange j2,List.mem_flatMap.mpr ⟨b2,hb2,List.mem_ofFn.mpr ⟨i,rfl⟩⟩⟩⟩)
    exact Nat.lt_of_le_of_lt (Nat.le_trans grows (Nat.le_of_eq moved))
      (depth_bound bound canonical vars listed)

end
end Tamarin.VariantCertificate
