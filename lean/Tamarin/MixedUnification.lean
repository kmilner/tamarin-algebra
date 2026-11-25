import Tamarin.MixedTotal
import Tamarin.NarrowingClash
import Tamarin.FreeFactoring
import Tamarin.DistinctAnswers
import Tamarin.ForcedOperandUnifier

namespace Tamarin.MixedUnification
variable {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]
variable [Interrupt]

open ComponentEncoding (SlotPair)

private def pairs : List (Term s) → List (SlotPair s)
  | [] => []
  | x :: xs => xs.map (fun y => (x,y)) ++ pairs xs

/-- Reopen the original equations when a terminal branch forces previously
distinct source slots to agree. Each recursive call removes the forced pairs
from a finite source inventory. Internal Hilbert-basis witnesses never enter it. -/
private def drive (p : Problem s) (todo : List (SlotPair s)) : RigidBranches.Certified p := by
  apply RigidBranches.refineWith p
  intro child
  match ComponentEncoding.branch child todo with
  | none => exact ⟨none,by simp⟩
  | some stage =>
    let visit (zs : {i // i ∈ stage.reopen}) :=
      have lt : (todo.filter (!zs.val.contains ·)).length < todo.length := by
        obtain ⟨z,hz⟩ := List.exists_mem_of_ne_nil _ (stage.nonempty _ zs.property)
        exact List.length_filter_lt_length_iff_exists.mpr
          ⟨z,stage.subset _ zs.property hz,by simpa using hz⟩
      drive (zs.val.map (fun z => ⟨z.1,z.2⟩) ++ child) (todo.filter (!zs.val.contains ·))
    match RigidBranches.collect (fun z => (visit z).val) stage.reopen.attach with
    | none => exact ⟨none,by simp⟩
    | some joined =>
      refine ⟨some (stage.rows ++ joined.val),?_⟩
      rintro _ ⟨⟩
      constructor
      · intro θ hm e he
        rcases List.mem_append.mp hm with left | right
        · exact stage.sound θ left e he
        · obtain ⟨z,_,ans,hs,mem⟩ := joined.property.2 θ right
          exact ((visit z).property ans hs).sound θ mem e (List.mem_append_right _ he)
      · intro ρ sol
        rcases stage.covers ρ sol with ⟨θ,hθ,μ,agree⟩ | ⟨zs,hz,eq⟩
        · exact ⟨θ,List.mem_append_left _ hθ,μ,agree⟩
        · let i := (⟨zs,hz⟩ : {t // t ∈ stage.reopen})
          obtain ⟨ans,hs,sub⟩ := joined.property.1 i (List.mem_attach ..)
          have extended : Problem.Solves (zs.map (fun z => (⟨z.1,z.2⟩ : Equation s)) ++ child) ρ := by
            intro e he
            rcases List.mem_append.mp he with he | he
            · obtain ⟨z,mem,rfl⟩ := List.mem_map.mp he
              exact eq z mem
            · exact sol e he
          obtain ⟨θ,hθ,μ,agree⟩ := ((visit i).property ans hs).covers ρ extended
          refine ⟨θ,List.mem_append_right _ (sub hθ),μ,?_⟩
          rintro v ⟨e,he,hv⟩
          exact agree v ⟨e,List.mem_append_right _ he,hv⟩
termination_by todo.length
decreasing_by exact lt

/-- Reuse the directly reconstructible answers and the component search before
enumerating source partitions. Every path returns a complete raw family. -/
def solve (p : Problem s) : List (UnifierSorts.Template s) :=
  match reconstruct? p with
  | some rows => rows
  | none =>
    match (drive p (pairs (inventory p))).val with
    | some rows => rows
    | none => Total.solve p

theorem complete (p : Problem s) : UnifierSorts.CompleteTemplates p (solve p) := by
  unfold solve
  split
  next h => exact reconstruct_correct h
  next =>
    split
    next h => exact (drive p _).property _ h
    next => exact Total.correct p

/-- The solver of a residual of free factoring. -/
def residual : VerifiedUnifier s (fun _ => True) :=
  NarrowingClash.unifier (UnifierSorts.unifier solve complete)

/-- The residual solver behind the equalities that the products force. A
residual that forces none is solved as it is. Otherwise the forced equalities
are added and factored, and their residual is examined again, at most the
given number of times. -/
def forcing : Nat → VerifiedUnifier s (fun _ => True)
  | 0 => residual
  | k + 1 => ForcedOperands.unifier residual fun _ => FreeFactoring.unifier (forcing k)

/-- Rounds of forced equalities. A round is spent only when the previous one
has added an equality. -/
def rounds : Nat := 4

/-- The ordinary unification reference accepts every arity-correct input.
Equations whose roots clash are rejected first. Free factoring then binds
variables and decomposes free heads, the equalities that the products of the
residual force are added and factored in turn, the residual is checked for
impossible equations at every depth, and only then reaches the component search.
Answers that agree on every query variable are returned once. -/
def verified : VerifiedUnifier s (fun _ => True) :=
  NarrowingClash.rootUnifier (DistinctAnswers.unifier (FreeFactoring.unifier (forcing rounds)))

omit [Interrupt] in
private theorem wrapped_solve (inner : VerifiedUnifier s (fun _ => True)) (p : Problem s)
    (avoid : List Variable) :
    (NarrowingClash.rootUnifier (DistinctAnswers.unifier (FreeFactoring.unifier inner))).solve
        p trivial avoid =
      if p.any NarrowingClash.quick then [] else DistinctAnswers.distinct p
        (FreeFactoring.solve inner p avoid) := rfl

theorem verified_solve (p : Problem s) (avoid : List Variable) :
    (verified (s := s)).solve p trivial avoid =
      if p.any NarrowingClash.quick then [] else DistinctAnswers.distinct p
        (FreeFactoring.solve (forcing rounds) p avoid) := wrapped_solve _ p avoid

/-- The residual solver answers the empty problem with one substitution that
moves no variable. -/
theorem forcing_empty (avoid : List Variable) :
    ∃ σ, (forcing (s := s) rounds).solve [] trivial avoid = [σ] ∧ ∀ v, σ.image v = .var v := by
  obtain ⟨x, hx⟩ := reconstruct_empty (s := s)
  have rows : solve (s := s) [] = [x] := by
    unfold solve
    rw [hx]
  obtain ⟨σ, hσ, img⟩ := UnifierSorts.solve_nil x avoid
  refine ⟨σ, ?_, img⟩
  have none : (ForcedOperands.added (s := s) []).val = [] := by
    unfold ForcedOperands.added
    simp
  simp only [rounds, forcing, ForcedOperands.unifier, none, List.isEmpty_nil, ↓reduceIte, residual,
    NarrowingClash.unifier, List.any_nil, Bool.false_eq_true, UnifierSorts.unifier, rows, hσ]

/-- Compatibility entry point for callers of the formerly partial reference. -/
def solve? (p : Problem s) : Option (List (UnifierSorts.Template s)) := some (solve p)

theorem solve_correct {p : Problem s} {rows} (hr : solve? p = some rows) :
    UnifierSorts.CompleteTemplates p rows := Option.some.inj hr ▸ complete p

theorem completes_singleDefinition (p : Problem s) (_h : SingleDefinition (purify p).constraints) :
    (solve? p).isSome := rfl

theorem completes_constructorFrontiers (p : Problem s)
    (_closed : ∀ c ∈ (RigidBranches.refineProblem p).val, ComponentEncoding.ConstructorFrontier c) :
    (solve? p).isSome := rfl

/-- Refine a complete raw answer with all admissible sorts and fresh caller names. -/
def unify? (p : Problem s) (avoid : List Variable) : Option (List (Substitution s)) :=
  some (verified.solve p trivial avoid)

theorem unify_correct {p : Problem s} {avoid answers} (h : unify? p avoid = some answers) :
    (Outcome.complete answers).CorrectIn p avoid := by
  cases Option.some.inj h
  exact ⟨verified.correct p trivial avoid, verified.domain p trivial avoid,
    verified.fresh p trivial avoid⟩

end Tamarin.MixedUnification
