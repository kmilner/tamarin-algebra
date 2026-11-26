import Tamarin.MaudeUnifyDiophantine

/-!
# Maude's selections of basis elements

`ACU_UnificationSubproblem2::nextSelection` for a theory without identity:
every subset of the basis, in Maude's order, that keeps each coordinate
within its bound and gives every coordinate a positive value. The basis is
traversed in list order; each element is first included, when that respects
the bounds, and then left out, when the elements after it can still cover
what is not covered yet. Each element carries the coordinates that the
elements after it cover (its `remainder`), as Maude computes it.
-/
namespace Tamarin.MaudeUnify.Select
open Dioph

variable {n : Nat}

/-- A basis element with the coordinates that the later elements cover. -/
structure Elem (n : Nat) where
  vec : Vector Nat n
  rem : Vector Bool n

/-- The coordinates a vector is positive at. -/
def support (v : Vector Nat n) : Vector Bool n := Vector.ofFn fun i => decide (0 < v[i])

/-- Pointwise or. -/
def union (a b : Vector Bool n) : Vector Bool n := Vector.ofFn fun i => a[i] || b[i]

/-- The basis in Maude's list order with remainders: each element's remainder
is the union of the supports of the elements after it. -/
def withRems : List (Vector Nat n) → List (Elem n)
  | [] => []
  | v :: vs =>
    let rest := withRems vs
    ⟨v, match rest with
      | [] => Vector.replicate n false
      | e :: _ => union (support e.vec) e.rem⟩ :: rest

/-- Whether an element fits on top of the totals. -/
def includable (upper : Vector (Option Nat) n) (tot : Vector Nat n) (e : Elem n) : Bool :=
  (List.finRange n).all fun i => fits upper[i] (tot[i] + e.vec[i])

/-- Whether the remainder contains every uncovered coordinate. -/
def reaches (rem unc : Vector Bool n) : Bool := (List.finRange n).all fun i => !unc[i] || rem[i]

/-- Add a vector to the totals. -/
def add (tot v : Vector Nat n) : Vector Nat n := Vector.ofFn fun i => tot[i] + v[i]

/-- Remove the support of a vector from the uncovered coordinates. -/
def cover (unc : Vector Bool n) (v : Vector Nat n) : Vector Bool n :=
  Vector.ofFn fun i => unc[i] && !decide (0 < v[i])

/-- The selections, include before exclude, as Maude's forward and backtracking
passes produce them. -/
def selections (upper : Vector (Option Nat) n) :
    List (Elem n) → Vector Nat n → Vector Bool n → List (List (Elem n))
  | [], _, unc => if (List.finRange n).all (fun i => !unc[i]) then [[]] else []
  | e :: rest, tot, unc =>
    (if includable upper tot e then
      (selections upper rest (add tot e.vec) (cover unc e.vec)).map (e :: ·) else []) ++
    (if reaches e.rem unc then selections upper rest tot unc else [])

/-- All selections of a basis in Maude's order. -/
def all (upper : Vector (Option Nat) n) (basis : List (Vector Nat n)) : List (List (Elem n)) :=
  selections upper (withRems basis) (Vector.replicate n 0) (Vector.replicate n true)

/-! ### Correctness -/

/-- The value of a selection at a coordinate. -/
def colSum (S : List (Elem n)) (i : Fin n) : Nat := (S.map fun e => e.vec[i]).sum

/-- Each element's remainder contains the supports of the elements after it. -/
def Rem : List (Elem n) → Prop
  | [] => True
  | e :: rest => (∀ i : Fin n, ∀ e' ∈ rest, 0 < e'.vec[i] → e.rem[i] = true) ∧ Rem rest

theorem vget_ofFn' {α : Type} (f : Fin n → α) (i : Fin n) : (Vector.ofFn f)[i] = f i := by
  simp [Fin.getElem_fin]

theorem rep_at {α : Type} (a : α) (i : Fin n) : (Vector.replicate n a)[i] = a := by
  simp [Fin.getElem_fin]

theorem union_at (a b : Vector Bool n) (i : Fin n) : (union a b)[i] = (a[i] || b[i]) := vget_ofFn' _ i

theorem support_at (v : Vector Nat n) (i : Fin n) : (support v)[i] = decide (0 < v[i]) := vget_ofFn' _ i

theorem fits_mono {b : Option Nat} {x y : Nat} (h : fits b x = true) (le : y ≤ x) : fits b y = true := by
  rw [fits_iff] at *
  intro u hu
  exact Nat.le_trans le (h u hu)

theorem selections_sound (upper : Vector (Option Nat) n) (L : List (Elem n)) (tot : Vector Nat n)
    (unc : Vector Bool n) (tfit : ∀ i : Fin n, fits upper[i] tot[i] = true)
    (S : List (Elem n)) (h : S ∈ selections upper L tot unc) :
    S.Sublist L ∧ (∀ i : Fin n, fits upper[i] (tot[i] + colSum S i) = true) ∧
      ∀ i : Fin n, unc[i] = true → ∃ e ∈ S, 0 < e.vec[i] := by
  induction L generalizing tot unc S with
  | nil =>
    simp only [selections] at h
    split at h
    · next none =>
      simp only [List.mem_singleton] at h
      subst h
      refine ⟨List.Sublist.slnil, fun i => ?_, fun i hi => ?_⟩
      · simpa [colSum] using tfit i
      · have := List.all_eq_true.mp none i (List.mem_finRange i)
        rw [hi] at this
        cases this
    · cases h
  | cons e rest ih =>
    simp only [selections, List.mem_append] at h
    rcases h with h | h
    · split at h
      · next inc =>
        obtain ⟨S', hS', rfl⟩ := List.mem_map.mp h
        have tfit' : ∀ i : Fin n, fits upper[i] (add tot e.vec)[i] = true := by
          intro i
          rw [add, vget_ofFn']
          exact List.all_eq_true.mp inc i (List.mem_finRange i)
        obtain ⟨sub, fit, cov⟩ := ih (add tot e.vec) (cover unc e.vec) tfit' S' hS'
        refine ⟨sub.cons_cons e, fun i => ?_, fun i hi => ?_⟩
        · have := fit i
          simp only [add, vget_ofFn'] at this
          simp only [colSum, List.map_cons, List.sum_cons]
          rwa [Nat.add_assoc] at this
        · by_cases pos : 0 < e.vec[i]
          · exact ⟨e, List.mem_cons_self, pos⟩
          · have : (cover unc e.vec)[i] = true := by
              simp only [cover, vget_ofFn', hi, Bool.true_and, Bool.not_eq_true', decide_eq_false_iff_not]
              exact pos
            obtain ⟨e', he', p'⟩ := cov i this
            exact ⟨e', List.mem_cons_of_mem _ he', p'⟩
      · cases h
    · split at h
      · obtain ⟨sub, fit, cov⟩ := ih tot unc tfit S h
        exact ⟨sub.cons e, fit, cov⟩
      · cases h

theorem colSum_cons (e : Elem n) (S : List (Elem n)) (i : Fin n) : colSum (e :: S) i = e.vec[i] + colSum S i := by
  simp [colSum]

theorem selections_complete (upper : Vector (Option Nat) n) (L : List (Elem n)) (rem : Rem L)
    (tot : Vector Nat n) (unc : Vector Bool n) (S : List (Elem n)) (sub : S.Sublist L)
    (fit : ∀ i : Fin n, fits upper[i] (tot[i] + colSum S i) = true)
    (cov : ∀ i : Fin n, unc[i] = true → ∃ e ∈ S, 0 < e.vec[i]) :
    S ∈ selections upper L tot unc := by
  induction L generalizing tot unc S with
  | nil =>
    obtain rfl := List.sublist_nil.mp sub
    simp only [selections]
    have none : (List.finRange n).all (fun i => !unc[i]) = true := by
      apply List.all_eq_true.mpr
      intro i _
      cases h : unc[i] with
      | false => rfl
      | true => obtain ⟨e, he, _⟩ := cov i h; cases he
    rw [ite_eq_left none]
    exact List.mem_singleton_self _
  | cons e rest ih =>
    simp only [selections, List.mem_append]
    cases sub with
    | cons _ sub =>
      right
      have reach : reaches e.rem unc = true := by
        apply List.all_eq_true.mpr
        intro i _
        cases h : unc[i] with
        | false => rfl
        | true =>
          obtain ⟨e', he', pos⟩ := cov i h
          simp [rem.1 i e' (sub.subset he') pos]
      simp only [reach, ↓reduceIte]
      exact ih rem.2 tot unc S sub fit cov
    | cons_cons _ sub =>
      rename_i S'
      left
      have inc : includable upper tot e = true := by
        apply List.all_eq_true.mpr
        intro i _
        apply fits_mono (fit i)
        rw [colSum_cons]
        omega
      simp only [inc, ↓reduceIte]
      apply List.mem_map_of_mem
      refine ih rem.2 (add tot e.vec) (cover unc e.vec) S' sub (fun i => ?_) (fun i hi => ?_)
      · rw [add, vget_ofFn', Nat.add_assoc, ← colSum_cons]
        exact fit i
      · simp only [cover, vget_ofFn', Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hi
        obtain ⟨e', he', pos⟩ := cov i hi.1
        rcases List.mem_cons.mp he' with rfl | he'
        · exact absurd pos hi.2
        · exact ⟨e', he', pos⟩

theorem withRems_vec : ∀ (vs : List (Vector Nat n)), (withRems vs).map (·.vec) = vs
  | [] => rfl
  | v :: vs => by simp [withRems, withRems_vec vs]

theorem withRems_rem : ∀ (vs : List (Vector Nat n)), Rem (withRems vs)
  | [] => trivial
  | v :: vs => by
    refine ⟨fun i e' he' pos => ?_, withRems_rem vs⟩
    -- the remainder of the head is the union of the supports after it
    have key : ∀ (ws : List (Vector Nat n)) (e' : Elem n), e' ∈ withRems ws → 0 < e'.vec[i] →
        (match withRems ws with
          | [] => Vector.replicate n false
          | e :: _ => union (support e.vec) e.rem)[i] = true := by
      intro ws
      induction ws with
      | nil => intro e' h; cases h
      | cons w ws ihw =>
        intro e' h pos
        show (union (support w) (match withRems ws with
          | [] => Vector.replicate n false
          | e :: _ => union (support e.vec) e.rem))[i] = true
        rw [union_at, support_at, Bool.or_eq_true, decide_eq_true_eq]
        simp only [withRems] at h
        rcases List.mem_cons.mp h with rfl | h
        · exact .inl pos
        · exact .inr (ihw e' h pos)
    exact key vs e' he' pos

/-- The selections of a basis respect the bounds and cover every coordinate. -/
theorem all_sound (upper : Vector (Option Nat) n) (basis : List (Vector Nat n)) {S : List (Elem n)}
    (h : S ∈ all upper basis) :
    (S.map (·.vec)).Sublist basis ∧ (∀ i : Fin n, fits upper[i] (colSum S i) = true) ∧
      ∀ i : Fin n, ∃ e ∈ S, 0 < e.vec[i] := by
  obtain ⟨sub, fit, cov⟩ := selections_sound upper _ _ _ (fun i => by
    rw [rep_at]; exact (fits_iff _ _).mpr fun _ _ => Nat.zero_le _) S h
  refine ⟨withRems_vec basis ▸ sub.map _, fun i => ?_, fun i => cov i (rep_at _ i)⟩
  have := fit i
  rwa [rep_at, Nat.zero_add] at this

/-- Every subset of a basis, in basis order, that respects the bounds and
covers every coordinate is a selection. -/
theorem all_complete (upper : Vector (Option Nat) n) (basis : List (Vector Nat n))
    (S : List (Vector Nat n)) (sub : S.Sublist basis)
    (fit : ∀ i : Fin n, fits upper[i] ((S.map fun v => v[i]).sum) = true)
    (cov : ∀ i : Fin n, ∃ v ∈ S, 0 < v[i]) :
    ∃ T ∈ all upper basis, T.map (·.vec) = S := by
  rw [← withRems_vec basis] at sub
  obtain ⟨T, subT, rfl⟩ := List.sublist_map_iff.mp sub
  refine ⟨T, ?_, rfl⟩
  apply selections_complete upper _ (withRems_rem basis) _ _ T subT
  · intro i
    rw [rep_at, Nat.zero_add]
    have := fit i
    rw [List.map_map] at this
    exact this
  · intro i _
    obtain ⟨v, hv, pos⟩ := cov i
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
    exact ⟨e, he, pos⟩

end Tamarin.MaudeUnify.Select
