import Tamarin.ACEquationExtensions
import Tamarin.GuessedMatching

/-! The one-remainder rules that narrowing has to try. The extension of an
AC-headed rule is left out when it is an instance of a rule of the table: a
rule with an operand variable of its own, such as `x * y * inv(x) = y`,
already matches every product that its extension matches, and the extension
of `x * inv(x) = one` is an instance of that rule. Maude leaves such
extensions out in the same way. The instance is found by a guessed
substitution that is tested, so a miss only keeps a redundant extension. -/
namespace Tamarin.ACEquationExtensions
open Rewriting ACSubproductReduction ConstructorVariants ContextualReduction
variable {s : Signature}

/-- The one-remainder rule of every AC-headed rule. -/
def additions (rules : List (Equation s)) : List (Equation s) :=
  rules.filterMap fun r => match head r.lhs with
    | .ac f => some (pattern f (remainder f r) r true)
    | _ => none

theorem extended_eq (rules : List (Equation s)) : extended rules = rules ++ additions rules := rfl

private theorem step_mono {R S : Root s} (root : ∀ a b, R a b → S a b) {a b} (st : Step R a b) :
    Step S a b := by
  induction st with
  | root h => exact .root (root _ _ h)
  | free f xs i _ ih => exact .free f xs i ih
  | comm_left f t _ ih => exact .comm_left f t ih
  | comm_right f t _ ih => exact .comm_right f t ih
  | ac_left f t _ ih => exact .ac_left f t ih
  | ac_right f t _ ih => exact .ac_right f t ih

section
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

/-- Whether a tested substitution turns the rule into the equation. -/
def covers (r e : Equation s) : Bool :=
  (GuessedMatching.find [(r.lhs,e.lhs),(r.rhs,e.rhs)]).isSome

/-- The table with the extensions that are not instances of one of its rules. -/
def needed (rules : List (Equation s)) : List (Equation s) :=
  rules ++ (additions rules).filter fun e => !rules.any fun r => covers r e

theorem needed_sub {rules : List (Equation s)} {r : Equation s} (h : r ∈ needed rules) :
    r ∈ extended rules := by
  rw [extended_eq]
  rcases List.mem_append.mp h with base | extra
  · exact List.mem_append_left _ base
  · exact List.mem_append_right _ (List.mem_filter.mp extra).1

theorem needed_bound {rules : List (Equation s)} (base : ReferenceReduction.Bound rules) :
    ReferenceReduction.Bound (needed rules) :=
  fun r hr => bound base r (needed_sub hr)

/-- A step of the smaller table is a step of the original rules. -/
theorem needed_modulo (rules : List (Equation s)) {a b : Term s}
    (h : StepModulo (ruleRoot (needed rules)) a b) : StepModulo (ruleRoot rules) a b := by
  apply (modulo rules a b).mp
  obtain ⟨p,q,before,step,after⟩ := h
  exact ⟨p,q,before,step_mono (fun _ _ ⟨r,hr,σ,l,e⟩ => ⟨r,needed_sub hr,σ,l,e⟩) step,after⟩

/-- Every root step of the extended table is one of the smaller table. -/
theorem atRoot_needed (rules : List (Equation s)) {a b : Term s}
    (h : AtRoot (ruleRoot (extended rules)) a b) : AtRoot (ruleRoot (needed rules)) a b := by
  obtain ⟨_,_,before,⟨e,he,σ,rfl,rfl⟩,after⟩ := h
  rw [extended_eq] at he
  rcases List.mem_append.mp he with base | extra
  · exact ⟨_,_,before,⟨e,List.mem_append_left _ base,σ,rfl,rfl⟩,after⟩
  · by_cases instance_ : rules.any (fun r => covers r e) = true
    · obtain ⟨r,hr,ok⟩ := List.any_eq_true.mp instance_
      obtain ⟨θ,found⟩ := Option.isSome_iff_exists.mp ok
      have fit := GuessedMatching.find_sound found
      have left := fit (r.lhs,e.lhs) List.mem_cons_self
      have right := fit (r.rhs,e.rhs) (List.mem_cons_of_mem _ List.mem_cons_self)
      refine ⟨_,_,before.trans ?_,⟨r,List.mem_append_left _ hr,σ.compose θ,rfl,rfl⟩,?_⟩
      · rw [Substitution.apply_compose]
        exact (left.subst σ.image).symm
      · rw [Substitution.apply_compose]
        exact (right.subst σ.image).trans after
    · exact ⟨_,_,before,⟨e,List.mem_append_right _ (List.mem_filter.mpr ⟨extra,by simpa using instance_⟩),
        σ,rfl,rfl⟩,after⟩

end
end Tamarin.ACEquationExtensions
