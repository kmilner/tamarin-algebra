import Tamarin.MaudeUnifyAlgorithm

/-!
# Semantics of Maude's unification states

A valuation gives every slot a term. It models a state when every binding
holds modulo B and every pending problem holds modulo B. A state is bounded
when its dags are well formed and only mention existing slots, and its
pending problems have the shapes their theories expect.
-/
namespace Tamarin.MaudeUnify
open Cancellation

variable {s : Signature}

/-! ### Size of terms -/

/-- The number of nodes of a term, which B does not change. -/
def tsize : Term s → Nat
  | .var _ => 1
  | .atom _ => 1
  | .free _ xs => 1 + (List.ofFn fun i => tsize (xs i)).sum
  | .comm _ a b => 1 + tsize a + tsize b
  | .ac _ a b => 1 + tsize a + tsize b

/-! ### Well-formed dags -/

/-- Free nodes have as many arguments as their arity, AC nodes at least two
(Maude's invariant: a product has at least two factors). -/
def Dag.Wf : Dag s → Prop
  | .var _ => True
  | .atom _ => True
  | .free f args => args.length = s.arity f ∧ ∀ d ∈ args, Dag.Wf d
  | .comm _ a b => Dag.Wf a ∧ Dag.Wf b
  | .ac _ args => 2 ≤ args.length ∧ ∀ d ∈ args, Dag.Wf d

/-- A dag mentions only slots below `n`. -/
def Dag.Below (n : Nat) (d : Dag s) : Prop := ∀ j ∈ d.vars, j < n

/-- A dag fit to enter a state of `n` slots. -/
def Dag.Fit (n : Nat) (d : Dag s) : Prop := d.Wf ∧ d.Below n

variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

/-- The shape a pending problem of a theory has. -/
def Pend.Shaped (p : Pend s) : Prop :=
  match p.th with
  | .ac f => (∃ args, p.lhs = .ac f args) ∧ ((∃ args, p.rhs = .ac f args) ∨ ∃ y, p.rhs = .var y)
  | .comm f => (∃ a b, p.lhs = .comm f a b) ∧ ∃ c d, p.rhs = .comm f c d

/-- A bounded state. -/
structure Bounded (st : St s) : Prop where
  sizes : st.sorts.size = st.vals.size
  vals : ∀ i d, st.value i = some d → d.Fit st.vals.size
  pend : ∀ p ∈ st.pending, p.lhs.Fit st.vals.size ∧ p.rhs.Fit st.vals.size ∧ p.Shaped

/-- Every binding of a state holds. -/
def Binds (st : St s) (ρ : Nat → Term s) : Prop :=
  ∀ i d, st.value i = some d → EquivB (ρ i) (Dag.eval ρ d)

/-- A valuation models a state. -/
structure Models (st : St s) (ρ : Nat → Term s) : Prop where
  binds : ∀ i d, st.value i = some d → EquivB (ρ i) (Dag.eval ρ d)
  pend : ∀ p ∈ st.pending, EquivB (Dag.eval ρ p.lhs) (Dag.eval ρ p.rhs)

/-- A valuation models a state except possibly the binding of one slot. -/
structure ModelsExcept (st : St s) (ρ : Nat → Term s) (old : Nat) : Prop where
  binds : ∀ i d, i ≠ old → st.value i = some d → EquivB (ρ i) (Dag.eval ρ d)
  pend : ∀ p ∈ st.pending, EquivB (Dag.eval ρ p.lhs) (Dag.eval ρ p.rhs)

/-- A later state keeps the slots and sorts of an earlier one. -/
def Grows (st st' : St s) : Prop :=
  st.vals.size ≤ st'.vals.size ∧ ∀ i < st.vals.size, st'.sortOf i = st.sortOf i

/-- A valuation that agrees with another on the slots below `n`. -/
def Agree (n : Nat) (ρ ρ' : Nat → Term s) : Prop := ∀ i < n, ρ' i = ρ i

/-- What completeness promises of a computation on a modelled state: if it
succeeds, the result is modelled by an extension of the valuation; it does
not fail. Giving up promises nothing. -/
def Promise (st : St s) (ρ : Nat → Term s) : Res (St s) → Prop
  | .ok st' => ∃ ρ', Agree st.vals.size ρ ρ' ∧ Models st' ρ'
  | .fail => False
  | .gaveUp => True

end Tamarin.MaudeUnify
