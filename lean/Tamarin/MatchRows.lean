import Tamarin.ACSplits
import Tamarin.MaudeOperations
import Tamarin.MatchingFree
import Tamarin.Commutative
import Tamarin.SortClash

/-! Requirement rows shared by the structural reference matcher and the bag
matcher. A row records an image requirement at each pattern-variable
occurrence. Distinct occurrences may constrain the same variable, even across
different equations. -/
namespace Tamarin.ReferenceMatching
open Matching
variable {s : Signature}
abbrev Requirements (s : Signature) := List (Variable × Term s)

def holds (σ : Substitution s) (row : Requirements s) : Prop :=
  ∀ v t, (v,t) ∈ row → EquivB (σ.image v) t

def combine (xs ys : List (Requirements s)) :=
  xs.flatMap fun a => ys.map (a ++ ·)

def together : List (List (Requirements s)) → List (Requirements s)
  | [] => [[]]
  | xs :: rest => combine xs (together rest)

def accepts (σ : Substitution s) (rows : List (Requirements s)) : Prop :=
  ∃ row ∈ rows, holds σ row

theorem mem_combine {xs ys : List (Requirements s)} {row} :
    row ∈ combine xs ys ↔ ∃ a ∈ xs, ∃ b ∈ ys, a ++ b = row := by
  simp [combine]

theorem combine_iff (σ : Substitution s) (xs ys : List (Requirements s)) :
    accepts σ (combine xs ys) ↔ accepts σ xs ∧ accepts σ ys := by
  constructor
  · rintro ⟨_, member, sat⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_combine.mp member
    exact ⟨⟨a,ha,fun v t h => sat v t (List.mem_append_left _ h)⟩,
      ⟨b,hb,fun v t h => sat v t (List.mem_append_right _ h)⟩⟩
  · rintro ⟨⟨a,ha,sa⟩,⟨b,hb,sb⟩⟩
    exact ⟨_, mem_combine.mpr ⟨a, ha, b, hb, rfl⟩,
      fun v t h => (List.mem_append.mp h).elim (sa v t) (sb v t)⟩

theorem together_iff (σ : Substitution s) (xs : List (List (Requirements s))) :
    accepts σ (together xs) ↔ ∀ rows ∈ xs, accepts σ rows := by
  induction xs with
  | nil => simp [accepts, together, holds]
  | cons x xs ih => simp [together, combine_iff, ih]

theorem mentions_combine {xs ys : List (Requirements s)} {row v}
    (member : row ∈ combine xs ys)
    (side : (∀ part ∈ xs, ∃ u, (v, u) ∈ part) ∨ (∀ part ∈ ys, ∃ u, (v, u) ∈ part)) :
    ∃ u, (v, u) ∈ row := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_combine.mp member
  rcases side with left | right
  · obtain ⟨u, hu⟩ := left a ha
    exact ⟨u, List.mem_append_left _ hu⟩
  · obtain ⟨u, hu⟩ := right b hb
    exact ⟨u, List.mem_append_right _ hu⟩

theorem part_of_together (xs : List (List (Requirements s))) {row}
    (member : row ∈ together xs) {ys} (hy : ys ∈ xs) :
    ∃ part ∈ ys, part ⊆ row := by
  induction xs generalizing row with
  | nil => contradiction
  | cons y xs ih =>
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_combine.mp member
    rcases List.mem_cons.mp hy with rfl | hm
    · exact ⟨a, ha, List.subset_append_left ..⟩
    · obtain ⟨v,hv,sub⟩ := ih hb hm
      exact ⟨v, hv, sub.trans (List.subset_append_right ..)⟩

theorem lookup_requirement (row : Requirements s) {v}
    (mentioned : ∃ t, (v, t) ∈ row) : ∃ u, row.lookup v = some u ∧ (v, u) ∈ row := by
  obtain ⟨t, member⟩ := mentioned
  have found : (row.lookup v).isSome := List.lookup_isSome_iff.mpr ⟨(v, t), member, by simp⟩
  obtain ⟨u, lookup⟩ := Option.isSome_iff_exists.mp found
  obtain ⟨_, _, eq, _⟩ := List.lookup_eq_some_iff.mp lookup
  exact ⟨u, lookup, by simp [eq]⟩

theorem mismatch {a b : Term s}
    (ne : (headModel s).eval Head.var a ≠ (headModel s).eval Head.var b) :
    ¬ EquivB a b := fun eq => ne eq.head_eq

def isVariable (v : Variable) : Term s → Bool
  | .var w => v == w
  | _ => false

theorem isVariable_iff (v : Variable) (t : Term s) :
    isVariable v t = true ↔ EquivB (.var v) t := by
  cases t with
  | var w =>
    simp only [isVariable, beq_iff_eq]
    exact ⟨fun h => h ▸ .refl _, fun h => Head.var.inj h.head_eq⟩
  | _ => exact ⟨nofun,fun h => nomatch h.head_eq⟩

end Tamarin.ReferenceMatching
