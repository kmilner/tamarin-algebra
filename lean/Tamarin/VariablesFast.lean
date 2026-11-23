import Tamarin.VariablePermutation

/-! Collect variables in front of an accumulator. The reference definitions
append the inventories of the arguments at every application, which copies
the lists of a nested term once per level. -/
namespace Tamarin
variable {sig : Signature}

namespace Term

private def collect : Term sig → List Variable → List Variable
  | .var v, acc => v :: acc
  | .atom _, acc => acc
  | .free _ args, acc => Fin.foldr _ (fun i acc => collect (args i) acc) acc
  | .comm _ a b, acc | .ac _ a b, acc => collect a (collect b acc)

private theorem foldr_flatten {n} (g : Fin n → List Variable) (acc : List Variable) :
    Fin.foldr n (fun i acc => g i ++ acc) acc = (List.ofFn g).flatten ++ acc := by
  induction n with
  | zero => simp
  | succ n ih => simp [Fin.foldr_succ, List.ofFn_succ, ih]

private theorem collect_eq (t : Term sig) (acc : List Variable) :
    collect t acc = t.variables ++ acc := by
  induction t generalizing acc with
  | var v => rfl
  | atom => rfl
  | free f args ih =>
    simp only [collect, variables, ih]
    exact foldr_flatten _ acc
  | comm f a b ia ib | ac f a b ia ib => simp [collect, variables, ia, ib]

private def variablesFast (t : Term sig) : List Variable := collect t []

@[csimp] theorem variables_eq_fast : @variables = @variablesFast := by
  funext sig t
  simp [variablesFast, collect_eq]

end Term

namespace Problem

private def variablesFast (p : Problem sig) : List Variable :=
  p.foldr (fun e acc => Term.collect e.lhs (Term.collect e.rhs acc)) []

@[csimp] theorem variables_eq_fast : @variables = @variablesFast := by
  funext sig p
  induction p with
  | nil => rfl
  | cons e es ih =>
    simp only [variablesFast, List.foldr_cons] at ih ⊢
    rw [← ih]
    simp [variables, Term.collect_eq]

end Problem
end Tamarin
