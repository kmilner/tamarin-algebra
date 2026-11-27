import Tamarin.ForcedOperandClasses
import Tamarin.ACReferenceBranch
import Tamarin.TermEquality

/-! Equalities between operands that the products of a problem force. The
occurrence rows of the equations at one AC head are linear equations over the
operand multiplicities. Two operands whose difference lies in the span of
these rows are equal under every unifier, so their equation is added before
the search. Free factoring then decomposes it, and the homogeneous search no
longer enumerates the sums that it collapses. Only systems with at least
`floor` distinct operands are examined. -/
namespace Tamarin.ForcedOperands
open ACForcedEquations ACBasis
variable {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym]
  [DecidableEq s.Atom]

def headOf : Term s → Option s.ACSym
  | .ac f _ _ => some f
  | _ => none

/-- The AC symbols at the root of a side. -/
def heads (p : Problem s) : List s.ACSym :=
  (p.flatMap fun e => (headOf e.lhs).toList ++ (headOf e.rhs).toList).eraseDups

private def atHead (f : s.ACSym) (e : Equation s) : Bool :=
  headOf e.lhs == some f || headOf e.rhs == some f

/-- Fewer distinct operands than this are left to the search. Its family then
lists the instances that the enumeration of Maude lists, which a forced
equality would merge into one unifier. -/
def floor : Nat := 8

/-- The forced equalities among the operands of the products at one head. An
equality relates an operand to the first operand of its class. -/
private def atSymbol (p : Problem s) (f : s.ACSym) : List {e : Equation s // Forced p [e]} :=
  let selected := p.filter (atHead f)
  if selected.length < 2 then [] else
  -- Fewer operand occurrences than the floor: fewer distinct operands as well.
  if (selected.map fun e => (ACRepresentation.flatten f e.lhs).length +
      (ACRepresentation.flatten f e.rhs).length).sum < floor then [] else
  let batch := OperandBatch.Reference.layout f selected
  if batch.1.length < floor then [] else
  match returned : ForcedCoordinates.run (ForcedOperandClasses.incidenceRows batch.2.val) with
  | none => []
  | some labels =>
    let used := OperandBatch.used batch.2.val
    (List.finRange batch.1.length).filterMap fun j =>
      if lt : labels[j] < batch.1.length then
        let i : Fin batch.1.length := ⟨labels[j], lt⟩
        if ok : i ≠ j ∧ labels[i] = labels[j] ∧ i ∈ used ∧ j ∈ used then
          some ⟨⟨batch.1.get i, batch.1.get j⟩,
            ForcedOperandClasses.forced_of_labels f batch.1.get batch.2.val selected p
              batch.2.property (fun _ h => (List.mem_filter.mp h).1) labels returned i j ok.2.2.1 ok.2.2.2 ok.2.1⟩
        else none
      else none

private def stated (p : Problem s) (e : Equation s) : Bool :=
  p.any fun d => (d.lhs == e.lhs && d.rhs == e.rhs) || (d.lhs == e.rhs && d.rhs == e.lhs)

/-- The forced equalities that the problem does not state. -/
def added (p : Problem s) : {extra : Problem s // Forced p extra} :=
  if p.length < 2 then ⟨[], Forced.of_each fun _ h => nomatch h⟩ else
  let found := ((heads p).flatMap (atSymbol p)).filter fun e => !stated p e.val
  ⟨found.map (·.val), Forced.of_each fun e he => by
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp he
    exact x.property⟩

/-- The operands of the products at the root, counted without telling the
product symbols apart. -/
def leaves : Term s → Nat
  | .ac _ a b => leaves a + leaves b
  | _ => 1

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem leaves_pos (t : Term s) : 0 < leaves t := by
  induction t with
  | ac g a b ia ib => simp only [leaves]; omega
  | _ => simp [leaves]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] in
theorem flatten_length_le (f : s.ACSym) (t : Term s) :
    (ACRepresentation.flatten f t).length ≤ leaves t := by
  induction t with
  | ac g a b ia ib =>
    unfold ACRepresentation.flatten
    split
    · simp only [List.length_append, leaves]; omega
    · simp only [List.length_singleton, leaves]
      have := leaves_pos a
      omega
  | _ => simp [ACRepresentation.flatten, leaves]

private theorem sum_filter_le {α : Type} (g : α → Nat) (q : α → Bool) (l : List α) :
    ((l.filter q).map g).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons]
    split <;> simp <;> omega

private theorem sum_map_le {α : Type} (g h : α → Nat) (l : List α) (le : ∀ x ∈ l, g x ≤ h x) :
    (l.map g).sum ≤ (l.map h).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    have := le x List.mem_cons_self
    have := ih fun y hy => le y (List.mem_cons_of_mem _ hy)
    omega

/-- A problem whose products have fewer operands than `floor` in all forces
nothing. -/
theorem added_small (p : Problem s) (h : (p.map fun e => leaves e.lhs + leaves e.rhs).sum < floor) :
    (added p).val = [] := by
  unfold added
  split
  · rfl
  · have none : (heads p).flatMap (atSymbol p) = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro f _
      unfold atSymbol
      dsimp only
      split
      · rfl
      · have le : ((p.filter (atHead f)).map fun e => (ACRepresentation.flatten f e.lhs).length +
            (ACRepresentation.flatten f e.rhs).length).sum ≤ (p.map fun e => leaves e.lhs + leaves e.rhs).sum := by
          have sub := sum_filter_le (fun e => leaves e.lhs + leaves e.rhs) (atHead f) p
          refine Nat.le_trans (sum_map_le _ _ _ fun e _ => ?_) sub
          exact Nat.add_le_add (flatten_length_le f e.lhs) (flatten_length_le f e.rhs)
        simp only [show ((p.filter (atHead f)).map fun e => (ACRepresentation.flatten f e.lhs).length +
            (ACRepresentation.flatten f e.rhs).length).sum < floor from Nat.lt_of_le_of_lt le h, ↓reduceIte]
    simp [none]

/-- Solve the problem directly when its products force no equality, and
otherwise with the forced equalities added. The second solver is built only
when it is used. -/
def unifier (direct : VerifiedUnifier s (fun _ => True))
    (again : Unit → VerifiedUnifier s (fun _ => True)) : VerifiedUnifier s (fun _ => True) where
  solve p _ avoid :=
    if (added p).val.isEmpty then direct.solve p trivial avoid
    else (again ()).solve ((added p).val ++ p) trivial avoid
  correct p _ avoid := by
    split
    · exact direct.correct p trivial avoid
    · exact ((added p).property.prepend.correctIn avoid (.complete _)
        ⟨(again ()).correct _ _ _, (again ()).domain _ _ _, (again ()).fresh _ _ _⟩).mathematical
  domain p _ avoid := by
    split
    · exact direct.domain p trivial avoid
    · exact ((added p).property.prepend.correctIn avoid (.complete _)
        ⟨(again ()).correct _ _ _, (again ()).domain _ _ _, (again ()).fresh _ _ _⟩).domain
  fresh p _ avoid := by
    split
    · exact direct.fresh p trivial avoid
    · exact ((added p).property.prepend.correctIn avoid (.complete _)
        ⟨(again ()).correct _ _ _, (again ()).domain _ _ _, (again ()).fresh _ _ _⟩).fresh

/-- An answer comes from the direct solver, or from the other one on the
problem with forced equalities added. -/
theorem solve_cases (direct : VerifiedUnifier s (fun _ => True))
    (again : Unit → VerifiedUnifier s (fun _ => True)) (p : Problem s)
    (avoid : List Variable) (σ : Substitution s)
    (mem : σ ∈ (unifier direct again).solve p trivial avoid) :
    σ ∈ direct.solve p trivial avoid ∨
      ∃ extra, Forced p extra ∧ σ ∈ (again ()).solve (extra ++ p) trivial avoid := by
  change σ ∈ (if (added p).val.isEmpty then direct.solve p trivial avoid
    else (again ()).solve ((added p).val ++ p) trivial avoid) at mem
  split at mem
  · exact .inl mem
  · exact .inr ⟨_, (added p).property, mem⟩

end Tamarin.ForcedOperands
