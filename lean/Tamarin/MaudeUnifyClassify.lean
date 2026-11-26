import Tamarin.MaudeUnifyRows

/-!
# The AC step: classification of subterms
-/
namespace Tamarin.MaudeUnify
open Cancellation


variable {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

/-- The top symbol of a term. -/
def HeadIs (t : Term s) : Top s → Prop
  | .atom a => t = .atom a
  | .free g => ∃ xs, t = .free g xs
  | .comm g => ∃ a b, t = .comm g a b
  | .ac g => ∃ a b, t = .ac g a b

theorem heads_ne {u v : Term s} {K L : Top s} (hu : HeadIs u K) (hv : HeadIs v L) (ne : K.beq L = false) :
    ¬ EquivB u v := by
  intro e
  have h := e.head_eq
  cases K <;> cases L <;> simp only [HeadIs] at hu hv <;>
    (first
      | (obtain rfl := hu; obtain rfl := hv)
      | (obtain ⟨_, rfl⟩ := hu; obtain rfl := hv)
      | (obtain rfl := hu; obtain ⟨_, rfl⟩ := hv)
      | (obtain ⟨_, rfl⟩ := hu; obtain ⟨_, rfl⟩ := hv)
      | (obtain ⟨_, _, rfl⟩ := hu; obtain rfl := hv)
      | (obtain rfl := hu; obtain ⟨_, _, rfl⟩ := hv)
      | (obtain ⟨_, _, rfl⟩ := hu; obtain ⟨_, rfl⟩ := hv)
      | (obtain ⟨_, rfl⟩ := hu; obtain ⟨_, _, rfl⟩ := hv)
      | (obtain ⟨_, _, rfl⟩ := hu; obtain ⟨_, _, rfl⟩ := hv)) <;>
    simp_all [Top.beq, headModel, Model.eval]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
/-- A well-formed non-variable dag denotes a term with its top symbol. -/
theorem eval_head (ρ : Nat → Term s) {d : Dag s} {K : Top s} (hd : d.Wf) (h : topOf d = some K) :
    HeadIs (Dag.eval ρ d) K := by
  cases d with
  | var => simp [topOf] at h
  | atom a => simp only [topOf, Option.some.injEq] at h; subst h; simp [HeadIs, Dag.eval_atom]
  | free g args => simp only [topOf, Option.some.injEq] at h; subst h; simp [HeadIs, Dag.eval_free]
  | comm g a b => simp only [topOf, Option.some.injEq] at h; subst h; simp [HeadIs, Dag.eval_comm]
  | ac g args =>
    simp only [topOf, Option.some.injEq] at h; subst h
    simp only [Dag.Wf] at hd
    rw [Dag.eval_ac]
    match args, hd.1 with
    | x :: y :: rest, _ => exact ⟨_, _, rfl⟩

/-- A term whose top symbol is not the AC symbol is one factor. -/
theorem flatten_single (f : s.ACSym) {t : Term s} {K : Top s} (h : HeadIs t K) (ne : K.beq (.ac f) = false) :
    flatten f t = [classOf t] := by
  classical
  cases K with
  | atom a => simp only [HeadIs] at h; subst h; rfl
  | free g => obtain ⟨_, rfl⟩ := h; rfl
  | comm g => obtain ⟨_, _, rfl⟩ := h; rfl
  | ac g =>
    obtain ⟨a, b, rfl⟩ := h
    have : f ≠ g := fun e => by subst e; simp [Top.beq] at ne
    simp [flatten, this]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
/-- A sort that cannot hold a product only has single factors. -/
theorem flatten_sorted (f : s.ACSym) {t : Term s} {srt : SortId} (ht : HasSort t srt)
    (no : Subsort.check (s.acSort f) srt = false) : (flatten f t).length = 1 := by
  classical
  have notAc : ∀ a b, t ≠ .ac f a b := by
    intro a b e
    subst e
    have : ∀ u srt, HasSort u srt → ∀ a b, u = .ac f a b → Subsort (s.acSort f) srt := by
      intro u srt h
      induction h with
      | ac g x y _ _ _ _ => intro a b e; cases e; exact .refl _
      | widen _ hs ih => intro a b e; exact (ih a b e).trans hs
      | _ => intro a b e; cases e
    have := (Subsort.check_iff _ _).mpr (this _ _ ht a b rfl)
    rw [no] at this
    cases this
  cases t with
  | ac g a b =>
    have : f ≠ g := fun e => by subst e; exact notAc a b rfl
    simp [flatten, this]
  | _ => rfl

/-- The valuation gives slots with sorts terms of those sorts. -/
def Sorted (st : St s) (ρ : Nat → Term s) : Prop := ∀ i srt, st.sortOf i = some srt → HasSort (ρ i) srt

theorem single_spec (f : s.ACSym) (d : Dag s) :
    ((single f d).1 = none ∧ (single f d).2 = none) ∨
      ∃ K, topOf d = some K ∧ K.beq (.ac f) = false ∧ single f d = (some 1, some K) := by
  cases h : topOf d with
  | none => left; simp [single, h]
  | some K =>
    cases K with
    | ac g =>
      by_cases e : g = f
      · left; simp [single, h, e]
      · right; exact ⟨_, rfl, by simp [Top.beq, e], by simp [single, h, e]⟩
    | _ => right; exact ⟨_, rfl, by simp [Top.beq], by simp [single, h]⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem flatten_of_equiv_single (f : s.ACSym) {t v : Term s} (e : EquivB t v) {c : Class s}
    (h : flatten f v = [c]) : flatten f t = [c] := by
  have p := flatten_equiv f e
  rw [h] at p
  exact List.perm_singleton.mp p

/-- The classification of a subterm is right about its factors. -/
theorem classify_spec (f : s.ACSym) {st : St s} {ρ : Nat → Term s} (b : Binds st ρ) (so : Sorted st ρ)
    (wf : ∀ i d, st.value i = some d → d.Wf) {t : Dag s} (ht : t.Wf) :
    (∀ u, (classify st f t).1 = some u → (flatten f (Dag.eval ρ t)).length ≤ u) ∧
      ∀ K, (classify st f t).2 = some K → ∃ v, HeadIs v K ∧ K.beq (.ac f) = false ∧
        flatten f (Dag.eval ρ t) = [classOf v] := by
  have ofSingle : ∀ d, d.Wf → ∀ w, EquivB w (Dag.eval ρ d) →
      (∀ u, (single f d).1 = some u → (flatten f w).length ≤ u) ∧
      ∀ K, (single f d).2 = some K → ∃ v, HeadIs v K ∧ K.beq (.ac f) = false ∧ flatten f w = [classOf v] := by
    intro d hd w e
    rcases single_spec f d with ⟨n1, n2⟩ | ⟨K, top, ne, eq⟩
    · exact ⟨fun u h => (by rw [n1] at h; cases h), fun K h => (by rw [n2] at h; cases h)⟩
    · have hh := eval_head ρ hd top
      have fl := flatten_of_equiv_single f e (flatten_single f hh ne)
      rw [eq]
      refine ⟨fun u h => ?_, fun K' h => ?_⟩
      · simp only [Option.some.injEq] at h; subst h; simp [fl]
      · simp only [Option.some.injEq] at h; subst h; exact ⟨_, hh, ne, fl⟩
  have ofSort : ∀ x, (∀ u, sortBound f (st.sortOf x) = some u → (flatten f (ρ x)).length ≤ u) := by
    intro x u h
    unfold sortBound at h
    split at h
    · cases h
    · next srt hs =>
      split at h
      · cases h
      · next no =>
        simp only [Option.some.injEq] at h; subst h
        simp only [Bool.not_eq_true] at no
        rw [flatten_sorted f (so x srt hs) no]
        exact Nat.le_refl _
  cases t with
  | var x =>
    simp only [classify, Dag.eval_var]
    split
    · next d hv =>
      split
      · exact ofSingle d (wf x d hv) (ρ x) (b x d hv)
      · exact ⟨ofSort x, fun K h => by cases h⟩
    · exact ⟨ofSort x, fun K h => by cases h⟩
  | atom a => exact ofSingle _ ht _ (.refl _)
  | free g args => exact ofSingle _ ht _ (.refl _)
  | comm g a c => exact ofSingle _ ht _ (.refl _)
  | ac g args => exact ofSingle _ ht _ (.refl _)

end Tamarin.MaudeUnify
