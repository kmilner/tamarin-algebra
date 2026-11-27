import Tamarin.MaudeUnifyBridge
import Tamarin.MixedUnification

/-!
# The port as a verified unifier

A problem is turned into dag equations over one slot per variable, in order
of first occurrence; the ranks of the symbols follow their first occurrence
too. The answers of the port become substitutions whose new variables are
numbered from the first number above the avoided and problem variables. When
the port runs out of fuel, the given fallback unifier answers instead.
-/
namespace Tamarin.MaudeUnify
open Cancellation


variable {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

/-- The list without repetitions, keeping first occurrences. -/
def nub {α : Type} [DecidableEq α] (l : List α) : List α :=
  (l.foldl (fun acc x => if x ∈ acc then acc else x :: acc) []).reverse

theorem mem_nub {α : Type} [DecidableEq α] (l : List α) (x : α) : x ∈ nub l ↔ x ∈ l := by
  have gen : ∀ (l acc : List α), x ∈ l.foldl (fun acc x => if x ∈ acc then acc else x :: acc) acc ↔
      x ∈ acc ∨ x ∈ l := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons y ys ih =>
      intro acc
      simp only [List.foldl_cons]
      rw [ih]
      by_cases h : y ∈ acc
      · rw [ite_eq_left h]
        constructor
        · rintro (h' | h')
          · exact .inl h'
          · exact .inr (List.mem_cons_of_mem _ h')
        · rintro (h' | h')
          · exact .inl h'
          · rcases List.mem_cons.mp h' with rfl | h'
            · exact .inl h
            · exact .inr h'
      · rw [ite_eq_right h]
        simp only [List.mem_cons]
        constructor
        · rintro ((h' | h') | h')
          · exact .inr (.inl h')
          · exact .inl h'
          · exact .inr (.inr h')
        · rintro (h' | h' | h')
          · exact .inl (.inr h')
          · exact .inl (.inl h')
          · exact .inr h'
  unfold nub
  rw [List.mem_reverse, gen]
  simp

/-- A top symbol. -/
inductive Head (s : Signature) where
  | atom (a : s.Atom)
  | free (f : s.FreeSym)
  | comm (f : s.CSym)
  | ac (f : s.ACSym)

instance : DecidableEq (Head s) := fun a b =>
  match a, b with
  | .atom x, .atom y => if h : x = y then .isTrue (h ▸ rfl) else .isFalse fun e => h (by cases e; rfl)
  | .free x, .free y => if h : x = y then .isTrue (h ▸ rfl) else .isFalse fun e => h (by cases e; rfl)
  | .comm x, .comm y => if h : x = y then .isTrue (h ▸ rfl) else .isFalse fun e => h (by cases e; rfl)
  | .ac x, .ac y => if h : x = y then .isTrue (h ▸ rfl) else .isFalse fun e => h (by cases e; rfl)
  | .atom _, .free _ | .atom _, .comm _ | .atom _, .ac _ | .free _, .atom _ | .free _, .comm _
  | .free _, .ac _ | .comm _, .atom _ | .comm _, .free _ | .comm _, .ac _ | .ac _, .atom _
  | .ac _, .free _ | .ac _, .comm _ => .isFalse fun e => by cases e

/-- The top symbols of a term, outermost first, left to right. -/
def headsIn : Term s → List (Head s)
  | .var _ => []
  | .atom a => [.atom a]
  | .free f xs => .free f :: (List.ofFn fun i => headsIn (xs i)).flatten
  | .comm f a b => .comm f :: (headsIn a ++ headsIn b)
  | .ac f a b => .ac f :: (headsIn a ++ headsIn b)

/-- Maude's index of a sort, for the orientation of variable bindings. -/
def sortIndex : Option SortId → Nat
  | none => 0
  | some .msg => 1
  | some .node => 2
  | some .pub => 3
  | some .fresh => 4
  | some .nat => 5

/-- The position of the first pair with the key, or the default. -/
def lookupRank {α : Type} [DecidableEq α] (table : List (α × Nat)) (a : α) (dflt : Nat) : Nat :=
  match table.find? (·.1 = a) with
  | some (_, i) => i
  | none => dflt

/-- The ranks of a problem: symbols by first occurrence and arity, variable
symbols by sort, original variables by number and new ones after them. The
tables are built once per problem. -/
def ranksOf (hs : List (Head s)) (vs : List Variable) : Ranks s :=
  let numbered := hs.zipIdx
  let atoms := numbered.filterMap fun (h, i) => match h with | .atom a => some (a, i) | _ => none
  let frees := numbered.filterMap fun (h, i) => match h with
    | .free f => some (f, (s.arity f <<< 24) ||| i) | _ => none
  let comms := numbered.filterMap fun (h, i) => match h with
    | .comm f => some (f, (2 <<< 24) ||| i) | _ => none
  let acs := numbered.filterMap fun (h, i) => match h with
    | .ac f => some (f, (2 <<< 24) ||| i) | _ => none
  let names := (vs.map (·.id)).toArray
  { atom := fun a => lookupRank atoms a hs.length
    atomArg := fun _ => 0
    free := fun f => lookupRank frees f ((s.arity f <<< 24) ||| hs.length)
    comm := fun f => lookupRank comms f ((2 <<< 24) ||| hs.length)
    ac := fun f => lookupRank acs f ((2 <<< 24) ||| hs.length)
    varSym := fun o => 1000 + match o with | none => 9 | some x => sortIndex (some x)
    name := fun i => names.getD i (1000000000 + (i - vs.length))
    sortIndex := sortIndex }

/-- The variables of a problem in order of first occurrence. -/
def varsOf (p : Problem s) : List Variable := nub p.variables

/-- The symbols of a problem in order of first occurrence. -/
def headsOf (p : Problem s) : List (Head s) := nub (p.flatMap fun e => headsIn e.lhs ++ headsIn e.rhs)

/-- The sort of each slot. -/
def sortsOf (vs : List Variable) : List SortId := vs.map (·.sort)

/-- The dag equations of a problem. -/
def dagsOf (r : Ranks s) (vs : List Variable) (p : Problem s) : List (Dag s × Dag s) :=
  let sortOf := fun i => (sortsOf vs)[i]?
  p.map fun e => (Dag.ofTerm r sortOf vs.idxOf e.lhs, Dag.ofTerm r sortOf vs.idxOf e.rhs)

/-- The new variable for output number `j` of an answer. -/
def outVar (base : Nat) (ans : Answer s) (j : Nat) : Variable := ⟨base + j, ans.sortAt j⟩

/-- The image of a variable under an answer. -/
def answerImage (vs : List Variable) (base : Nat) (ans : Answer s) (v : Variable) : Term s :=
  Dag.eval (fun j => .var (outVar base ans j)) (ans.image (vs.idxOf v))

theorem fit_dagsOf (r : Ranks s) (vs : List Variable) (p : Problem s) (hv : ∀ v, p.Occurs v → v ∈ vs) :
    ∀ q ∈ dagsOf r vs p, q.1.Fit (sortsOf vs).length ∧ q.2.Fit (sortsOf vs).length := by
  intro q hq
  simp only [dagsOf, List.mem_map] at hq
  obtain ⟨e, he, rfl⟩ := hq
  have side : ∀ t : Term s, (∀ v, t.Occurs v → p.Occurs v) →
      (Dag.ofTerm r (fun i => (sortsOf vs)[i]?) vs.idxOf t).Fit (sortsOf vs).length := by
    intro t ht
    obtain ⟨w, below⟩ := Dag.ofTerm_fit r (fun i => (sortsOf vs)[i]?) vs.idxOf t
    refine ⟨w, fun j hj => ?_⟩
    obtain ⟨v, o, rfl⟩ := below j hj
    rw [sortsOf, List.length_map]
    exact List.idxOf_lt_length_of_mem (hv v (ht v o))
  exact ⟨side _ fun v o => ⟨e, he, .inl o⟩, side _ fun v o => ⟨e, he, .inr o⟩⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem varsOf_occurs (p : Problem s) (v : Variable) : v ∈ varsOf p ↔ p.Occurs v := by
  rw [varsOf, mem_nub, Problem.mem_variables]

/-- Evaluating the dag of a problem side under slot values `ρ` agrees with
substituting the values of the slots of the variables. -/
theorem eval_side (r : Ranks s) (vs : List Variable) (ρ : Nat → Term s) (t : Term s) (σ : Variable → Term s)
    (agree : ∀ v, t.Occurs v → EquivB (ρ (vs.idxOf v)) (σ v)) :
    EquivB (Dag.eval ρ (Dag.ofTerm r (fun i => (sortsOf vs)[i]?) vs.idxOf t)) (t.subst σ) :=
  (Dag.eval_ofTerm r _ vs.idxOf ρ t).trans (Term.subst_equiv _ _ t agree)

/-- The port on a problem with the ranks `r` and the variables of the problem
in the slots of their positions in `vs`: `none` when it gave up. -/
def portSolveWith [Interrupt] (r : Ranks s) (vs : List Variable) (k : Nat) (p : Problem s)
    (hv : ∀ v, p.Occurs v → v ∈ vs) (avoid : List Variable) : Option (List (Substitution s)) :=
  let base := VariablePermutation.freshBound (avoid ++ vs)
  match h : unify r k (sortsOf vs) (dagsOf r vs p) with
  | .ok answers => some (Interrupt.map (fun ⟨ans, ha⟩ =>
      Substitution.fromBindings (vs.map fun v => (v, answerImage vs base ans v)) (by
        intro v t hm
        obtain rfl := Interrupt.eq_never ‹Interrupt›
        obtain ⟨w, hw, e⟩ := List.mem_map.mp hm
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
        have hi : vs.idxOf w < (sortsOf vs).length := by
          rw [sortsOf, List.length_map]; exact List.idxOf_lt_length_of_mem hw
        have := (unify_sound r k (sortsOf vs) (dagsOf r vs p) (fit_dagsOf r vs p hv) h ha).2.1
          (fun j => .var (outVar base ans j)) (fun j => .var _) (vs.idxOf w) hi
        simpa [sortsOf, List.getElem_idxOf, answerImage] using this)) answers.attach)
  | .fail => some []
  | .gaveUp => none

/-- The port on a problem: `none` when it gave up. -/
def portSolve [Interrupt] (k : Nat) (p : Problem s) (avoid : List Variable) : Option (List (Substitution s)) :=
  portSolveWith (ranksOf (headsOf p) (varsOf p)) (varsOf p) k p (fun v o => (varsOf_occurs p v).mpr o) avoid

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
/-- The substitution of an answer. -/
theorem portSolve_image (vs : List Variable) (base : Nat) (ans : Answer s) (hs) (v : Variable) :
    (Substitution.fromBindings (vs.map fun v => (v, answerImage vs base ans v)) hs).image v =
      if v ∈ vs then answerImage vs base ans v else .var v :=
  Substitution.lookupBinding_tabulate vs _ v

/-- With any ranks and any list `vs` of exactly the variables of the problem,
the port's answers form a complete set of unifiers, leave variables outside
the problem alone and introduce only variables outside `avoid`. -/
theorem portSolveWith_spec (r : Ranks s) (vs : List Variable) (k : Nat) (p : Problem s)
    (occ : ∀ v, p.Occurs v → v ∈ vs) (back : ∀ v ∈ vs, p.Occurs v) (avoid : List Variable)
    {l : List (Substitution s)} (h : portSolveWith r vs k p occ avoid = some l) :
    CompleteSet p l ∧ ∀ σ ∈ l, DomainRestricted p σ ∧ FreshFor p avoid σ := by
  unfold portSolveWith at h
  simp only at h
  have fit := fit_dagsOf r vs p occ
  have idx : ∀ v, p.Occurs v → vs.idxOf v < (sortsOf vs).length := fun v o => by
    rw [sortsOf, List.length_map]; exact List.idxOf_lt_length_of_mem (occ v o)
  -- the dag equations of a solution
  have dagSol : ∀ (ρ : Nat → Term s) (σ : Variable → Term s),
      (∀ v, p.Occurs v → EquivB (ρ (vs.idxOf v)) (σ v)) →
      ∀ e ∈ p, EquivB (e.lhs.subst σ) (e.rhs.subst σ) →
        EquivB (Dag.eval ρ (Dag.ofTerm r (fun i => (sortsOf vs)[i]?) vs.idxOf e.lhs))
          (Dag.eval ρ (Dag.ofTerm r (fun i => (sortsOf vs)[i]?) vs.idxOf e.rhs)) := by
    intro ρ σ ag e he eq
    exact ((eval_side _ _ ρ e.lhs σ fun v o => ag v ⟨e, he, .inl o⟩).trans eq).trans
      (eval_side _ _ ρ e.rhs σ fun v o => ag v ⟨e, he, .inr o⟩).symm
  -- the slot values of a substitution
  let slotsOf : Substitution s → Nat → Term s := fun ρ i => ρ.image (vs.getD i ⟨0, .msg⟩)
  have slots_at : ∀ ρ v, v ∈ vs → slotsOf ρ (vs.idxOf v) = ρ.image v := by
    intro ρ v hv
    simp only [slotsOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hv),
      List.getElem_idxOf, Option.getD_some]
  have slots_sorted : ∀ ρ : Substitution s, ∀ i (hi : i < (sortsOf vs).length),
      HasSort (slotsOf ρ i) (sortsOf vs)[i] := by
    intro ρ i hi
    have hi' : i < vs.length := by simpa [sortsOf] using hi
    simp only [slotsOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some, sortsOf,
      List.getElem_map]
    exact ρ.sorted _
  have slots_solve : ∀ ρ : Substitution s, p.Solves ρ →
      ∀ q ∈ dagsOf r vs p, EquivB (Dag.eval (slotsOf ρ) q.1) (Dag.eval (slotsOf ρ) q.2) := by
    intro ρ sol q hq
    simp only [dagsOf, List.mem_map] at hq
    obtain ⟨e, he, rfl⟩ := hq
    exact dagSol (slotsOf ρ) ρ.image (fun v o => by rw [slots_at ρ v (occ v o)]; exact .refl _) e he (sol e he)
  split at h
  · next answers hu =>
    simp only [Option.some.injEq] at h
    subst h
    have base_gt : ∀ w ∈ avoid, w.id < VariablePermutation.freshBound (avoid ++ vs) := fun w hw =>
      VariablePermutation.lt_freshBound _ w (List.mem_append_left _ hw)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · -- soundness
      intro σ hσ e he
      obtain ⟨⟨ans, ha⟩, _, rfl⟩ := List.mem_map.mp hσ
      obtain ⟨sound, _, _, _⟩ := unify_sound _ k _ _ fit hu ha
      obtain ⟨ρ, eqs, agree⟩ := sound fun j => .var (outVar (VariablePermutation.freshBound (avoid ++ vs)) ans j)
      have ag : ∀ σ' : Variable → Term s, (∀ v, p.Occurs v →
          σ' v = answerImage vs (VariablePermutation.freshBound (avoid ++ vs)) ans v) →
          ∀ v, p.Occurs v → EquivB (ρ (vs.idxOf v)) (σ' v) := by
        intro σ' hσ' v o
        rw [hσ' v o]
        exact agree _ (idx v o)
      have im : ∀ v, p.Occurs v → Substitution.lookupBinding (vs.map fun v =>
          (v, answerImage vs (VariablePermutation.freshBound (avoid ++ vs)) ans v)) v =
          answerImage vs (VariablePermutation.freshBound (avoid ++ vs)) ans v := by
        intro v o
        rw [Substitution.lookupBinding_tabulate, ite_eq_left (occ v o)]
      have qe := eqs _ (List.mem_map.mpr ⟨e, he, rfl⟩)
      simp only at qe
      exact ((eval_side _ _ ρ e.lhs _ fun v o => ag _ (fun w ow => im w ow) v ⟨e, he, .inl o⟩).symm.trans qe).trans
        (eval_side _ _ ρ e.rhs _ fun v o => ag _ (fun w ow => im w ow) v ⟨e, he, .inr o⟩)
    · -- coverage
      intro ρs sol
      have c := unify_complete r k _ _ fit (slotsOf ρs) (slots_solve ρs sol) (slots_sorted ρs)
      rw [hu] at c
      obtain ⟨ans, ha, δ, hδ, inst⟩ := c
      obtain ⟨_, _, _, vars, wf⟩ := unify_sound _ k _ _ fit hu ha
      let base := VariablePermutation.freshBound (avoid ++ vs)
      let outs := (List.range ans.sorts.length).map (outVar base ans)
      let δ' := Substitution.fromBindings (outs.map fun w => (w, δ (w.id - base))) (by
        intro v t hm
        obtain ⟨w, hw, e⟩ := List.mem_map.mp hm
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hw
        simpa [outVar] using hδ j)
      refine ⟨_, List.mem_map.mpr ⟨⟨ans, ha⟩, List.mem_attach _ _, rfl⟩, δ', fun v o => ?_⟩
      show EquivB (ρs.image v) (δ'.apply (Substitution.lookupBinding _ v))
      rw [Substitution.lookupBinding_tabulate, ite_eq_left (occ v o), ← slots_at ρs v (occ v o)]
      refine (inst _ (idx v o)).trans ?_
      unfold answerImage Substitution.apply
      rw [Dag.eval_subst _ _ _ (wf _ (idx v o))]
      have e2 : Dag.eval (fun i => Term.subst δ'.image (Term.var (outVar base ans i))) (ans.image (vs.idxOf v)) =
          Dag.eval δ (ans.image (vs.idxOf v)) := by
        apply Dag.eval_congr
        intro j hj
        have hj' := vars _ (idx v o) j hj
        show Substitution.lookupBinding _ _ = _
        rw [Substitution.lookupBinding_tabulate, ite_eq_left (List.mem_map.mpr ⟨j, List.mem_range.mpr hj', rfl⟩)]
        simp [outVar]
      rw [e2]
      exact .refl _
    · -- domain and freshness
      intro σ hσ
      obtain ⟨⟨ans, ha⟩, _, rfl⟩ := List.mem_map.mp hσ
      obtain ⟨_, _, _, vars, wf⟩ := unify_sound _ k _ _ fit hu ha
      refine ⟨fun v no => ?_, fun v o w ow _ => ?_⟩
      · rw [portSolve_image, ite_eq_right fun hv => no (back v hv)]
      · rw [portSolve_image, ite_eq_left (occ v o)] at ow
        obtain ⟨j, _, oj⟩ := Dag.eval_occurs _ _ (wf _ (idx v o)) ow
        simp only [Term.Occurs] at oj
        subst oj
        intro hw
        have := base_gt _ hw
        simp only [outVar] at this
        omega
  · next hu =>
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨(complete_empty_iff p).mpr fun ⟨ρs, sol⟩ => ?_, fun σ hσ => by cases hσ⟩
    have c := unify_complete r k _ _ fit (slotsOf ρs) (slots_solve ρs sol) (slots_sorted ρs)
    rw [hu] at c
    exact c
  · cases h

/-- The port's answers form a complete set of unifiers, leave variables
outside the problem alone and introduce only variables outside `avoid`. -/
theorem portSolve_spec (k : Nat) (p : Problem s) (avoid : List Variable) {l : List (Substitution s)}
    (h : portSolve k p avoid = some l) :
    CompleteSet p l ∧ ∀ σ ∈ l, DomainRestricted p σ ∧ FreshFor p avoid σ :=
  portSolveWith_spec _ _ k p _ (fun v hv => (varsOf_occurs p v).mp hv) avoid h

/-- The fuel of the port. -/
def fuel : Nat := 100000

/-- The port, with a fallback unifier for the problems it gives up on. A port
that was told to stop does not start the fallback: the caller discards what
an interrupted search returns, so the empty list stands for that outcome. -/
def withFallback [Interrupt] (k : Nat) (fallback : VerifiedUnifier s (fun _ => True)) :
    VerifiedUnifier s (fun _ => True) where
  solve p h avoid :=
    match portSolve k p avoid with
    | some answers => answers
    | none => Interrupt.guard [] fun _ => fallback.solve p h avoid
  correct p h avoid := by
    obtain rfl := Interrupt.eq_never ‹Interrupt›
    split
    · next answers e => exact (portSolve_spec k p avoid e).1
    · exact fallback.correct p h avoid
  domain p h avoid σ hσ := by
    obtain rfl := Interrupt.eq_never ‹Interrupt›
    split at hσ
    · next answers e => exact ((portSolve_spec k p avoid e).2 σ hσ).1
    · exact fallback.domain p h avoid σ hσ
  fresh p h avoid σ hσ := by
    obtain rfl := Interrupt.eq_never ‹Interrupt›
    split at hσ
    · next answers e => exact ((portSolve_spec k p avoid e).2 σ hσ).2
    · exact fallback.fresh p h avoid σ hσ

section
variable [Interrupt]

/-- The unifier of root narrowing: the root clash check, then the port, then
the mixed unifier when the port gives up. -/
def verified : VerifiedUnifier s (fun _ => True) :=
  NarrowingClash.rootUnifier (withFallback fuel (MixedUnification.verified (s := s)))

end

end Tamarin.MaudeUnify
