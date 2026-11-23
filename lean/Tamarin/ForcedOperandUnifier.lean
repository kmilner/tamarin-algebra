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

private def headOf : Term s → Option s.ACSym
  | .ac f _ _ => some f
  | _ => none

/-- The AC symbols at the root of a side. -/
private def heads (p : Problem s) : List s.ACSym :=
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
