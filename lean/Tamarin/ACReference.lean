import Tamarin.ACBasisComplete
import Tamarin.VariablePermutation
import Tamarin.ACBagSearch
import Tamarin.ACCoverage
import Tamarin.ACConstrainedSelection
import Tamarin.ACHilbert
import Tamarin.Buckets

/-! A terminating reference for simultaneous homogeneous equations at one
ordinary AC head. Inputs and answer indices use natural numbers throughout. -/
namespace Tamarin.ACSystem.Reference
open VariablePermutation
variable {sig : Signature} [Interrupt]

/-- Build the coordinate table from the source variable occurrences. -/
def frame (f : sig.ACSym) (rows : List Row)
    (sorted : ∀ v ∈ variables rows, v.sort = sig.acSort f) :
    Frame f rows (variables rows).eraseDups.length := by
  let vs := (variables rows).eraseDups
  -- The position of a variable is read from a table, not searched in the list.
  let table := Buckets.index Variable.id (vs.length + 1) 0 vs
  let idx (v : Variable) : Option (Fin vs.length) :=
    let i := Buckets.lookup Variable.id table (0 + vs.length) v
    if h : i < vs.length then some ⟨i, h⟩ else none
  refine ⟨vs.get, idx, ?_, ?_, ?_, ?_⟩
  · intro i
    have distinct : vs.Nodup := Matching.ACBagSearch.dedup_distinct _
    have found : Buckets.lookup Variable.id table (0 + vs.length) (vs.get i) = i.val := by
      rw [Buckets.lookup_index Variable.id (vs.length + 1) (Nat.succ_pos _) 0 vs (vs.get i)]
      simp [List.get_eq_getElem, distinct.idxOf_getElem]
    simp only [idx, found]
    exact dite_eq_left i.isLt
  · intro v hv
    have h : v ∈ vs := List.mem_eraseDups.mpr hv
    exact ⟨⟨_, List.idxOf_lt_length_of_mem h⟩, List.getElem_idxOf _⟩
  · intro i
    exact List.mem_eraseDups.mp (List.getElem_mem i.isLt)
  · intro i
    exact sorted _ (List.mem_eraseDups.mp (List.getElem_mem i.isLt))

private def witness (f : sig.ACSym) (used : List Variable) (j : Nat) : Variable :=
  ⟨freshBound used + j, sig.acSort f⟩

omit [Interrupt] in
private theorem unused (f : sig.ACSym) (used : List Variable) (j : Nat) :
    witness f used j ∉ used := by
  intro h
  have lt := lt_freshBound used _ h
  change freshBound used + j < freshBound used at lt
  omega

private def branches {f : sig.ACSym} {rows : List Row} {n} (fr : Frame f rows n)
    (avoid : List Variable) : List (Branch f rows avoid) :=
  let matrix := rows.map (ACBasis.encode fr.names)
  let gs := ACBasis.hilbert matrix
  (Homogeneous.selections gs).attach.map fun js =>
    selectedBranch fr gs (ACBasis.hilbert_correct matrix)
      (fun j => witness f (variables rows ++ avoid) j.val) (fun _ => rfl)
      (fun j => unused _ _ j.val) js

/-- No precomputed basis, witness assignment, search budget, or success
hypothesis is required of the caller. -/
def solve (f : sig.ACSym) (rows : List Row)
    (sorted : ∀ v ∈ variables rows, v.sort = sig.acSort f) (avoid : List Variable) :
    List (Substitution sig) :=
  (branches (frame f rows sorted) avoid).map Branch.answer

omit [Interrupt] in
theorem correct (f : sig.ACSym) (rows : List Row)
    (sorted : ∀ v ∈ variables rows, v.sort = sig.acSort f) (avoid : List Variable) :
    (Outcome.complete (solve f rows sorted avoid)).CorrectIn (problem f rows) avoid := by
  let fr := frame f rows sorted
  have inject {k : Nat} : Function.Injective (fun j : Fin k => witness f (variables rows ++ avoid) j.val) :=
    fun _ _ h => Fin.ext (Nat.add_left_cancel (congrArg Variable.id h))
  simpa only [solve, branches, List.map_map, Function.comp_def] using
    basis_answers_correct fr _ (ACBasis.hilbert_correct _) _ inject
      (fun _ => rfl) (fun j => unused f (variables rows ++ avoid) j.val)

omit [Interrupt] in
theorem range_fresh {f : sig.ACSym} {rows : List Row} {sorted avoid σ}
    (returned : σ ∈ solve f rows sorted avoid) {v w}
    (live : (problem f rows).Occurs v) (occ : (σ.image v).Occurs w) :
    w ∉ variables rows ++ avoid := by
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp returned
  exact b.range_fresh live occ

omit [Interrupt] in
/-- Images in a homogeneous answer are variables or products at the selected
head. Other signatures can combine the answer using just this outer shape. -/
theorem image_shape {f : sig.ACSym} {rows sorted avoid σ}
    (returned : σ ∈ solve f rows sorted avoid) (v : Variable) :
    (∃ w, σ.image v = .var w) ∨ ∃ a b, σ.image v = .ac f a b := by
  obtain ⟨arm,_,rfl⟩ := List.mem_map.mp returned
  change (∃ w, arm.image v = _) ∨ ∃ a b, arm.image v = _
  unfold Branch.image
  split
  · split
    · exact .inl ⟨_,rfl⟩
    next w ws _ => cases ws with
      | nil => exact .inl ⟨_,rfl⟩
      | cons => exact .inr ⟨_,_,rfl⟩
  · exact .inl ⟨_,rfl⟩

section Constrained
variable {α : Type}

/-- A generator that no admissible selection contains: it has multiplicity two
at a capped coordinate, or meets two capped coordinates with conflicting tags. -/
private def rejected {n} (tags : Vector α n) (cap : α → Bool) (clash : α → α → Bool)
    (g : ACBasis.Vec n) : Bool :=
  let live := (List.finRange n).filter fun i => 0 < g i && cap tags[i]
  live.any (fun i => 2 ≤ g i) || live.any fun i => live.any fun k => clash tags[i] tags[k]

private def capMask {n} (tags : Vector α n) (cap : α → Bool) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin n => cap tags[i])).cast (by simp)

omit [Interrupt] in
private theorem capMask_bit {n} (tags : Vector α n) (cap : α → Bool) (i : Fin n) :
    (capMask tags cap).getLsbD i = cap tags[i] := by
  simp only [capMask, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some]

private def chosen {n} (gs : List (ACBasis.Vec n)) (tags : Vector α n) (cap : α → Bool)
    (clash : α → α → Bool) : List (List (Fin gs.length)) :=
  let bad := Vector.ofFn fun j : Fin gs.length => rejected tags cap clash (gs.get j)
  Homogeneous.constrainedSelections gs (capMask tags cap) (fun j => bad[j])

private theorem chosen_covering {n} (gs : List (ACBasis.Vec n)) (tags : Vector α n) (cap : α → Bool)
    (clash : α → α → Bool) {js} (h : js ∈ chosen gs tags cap clash) :
    js ∈ Homogeneous.selections gs := by
  exact Homogeneous.constrainedSelections_covering _ _ _ h

private def branchesWith {f : sig.ACSym} {rows : List Row} {n} (fr : Frame f rows n)
    (avoid : List Variable) (tag : Variable → α) (cap : α → Bool) (clash : α → α → Bool) :
    List (Branch f rows avoid) :=
  let matrix := rows.map (ACBasis.encode fr.names)
  let gs := ACBasis.hilbert matrix
  let tags := Vector.ofFn fun i => tag (fr.names i)
  Interrupt.map (fun js =>
    selectedBranch fr gs (ACBasis.hilbert_correct matrix)
      (fun j => witness f (variables rows ++ avoid) j.val) (fun _ => rfl)
      (fun j => unused _ _ j.val) ⟨js.val, chosen_covering gs tags cap clash js.property⟩)
    (chosen gs tags cap clash).attach

/-- The answers of `solve` that respect the column constraints. A capped column
receives one witness, and two columns with conflicting tags never share one. -/
def solveWith (f : sig.ACSym) (rows : List Row)
    (sorted : ∀ v ∈ variables rows, v.sort = sig.acSort f) (avoid : List Variable)
    (tag : Variable → α) (cap : α → Bool) (clash : α → α → Bool) : List (Substitution sig) :=
  Interrupt.map Branch.answer (branchesWith (frame f rows sorted) avoid tag cap clash)

theorem solveWith_subset {f : sig.ACSym} {rows sorted avoid} {tag : Variable → α} {cap clash σ}
    (h : σ ∈ solveWith f rows sorted avoid tag cap clash) : σ ∈ solve f rows sorted avoid := by
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp h
  obtain ⟨js,-,rfl⟩ := List.mem_map.mp hb
  exact List.mem_map_of_mem (List.mem_map_of_mem (List.mem_attach _ ⟨js.val,_⟩))

private def picks {n} (gs : List (ACBasis.Vec n)) (w : Fin gs.length → Variable)
    (js : List (Fin gs.length)) (i : Fin n) : List Variable :=
  js.flatMap fun j => List.replicate (gs.get j i) (w j)

omit [Interrupt] in
private theorem image_selected {n} {f : sig.ACSym} {rows : List Row} {avoid : List Variable}
    (fr : Frame f rows n) (gs : List (ACBasis.Vec n)) (basis) (w : Fin gs.length → Variable)
    (typed) (fresh) (js : {l // l ∈ Homogeneous.selections gs}) (i : Fin n) :
    (selectedBranch (avoid := avoid) fr gs basis w typed fresh js).answer.image (fr.names i) =
      match picks gs w js.val i with
      | [] => .var (fr.names i)
      | u :: us => (Side.mk u us).term f := by
  change Branch.image _ _ = _
  have same : slots (selectedBranch (avoid := avoid) fr gs basis w typed fresh js).active (fr.names i) =
      picks gs w js.val i := by
    simp [selectedBranch, branchFromBasis, slots, picks, List.flatMap_map, fr.inverse]
  rw [Branch.image, ite_eq_left (fr.used i), same]
  generalize picks gs w js.val i = l
  cases l <;> rfl

omit [Interrupt] in
private theorem picks_length {n} (gs : List (ACBasis.Vec n)) (w : Fin gs.length → Variable)
    (js : List (Fin gs.length)) (i : Fin n) :
    (picks gs w js i).length = (js.map fun j => gs.get j i).sum := by
  induction js with
  | nil => rfl
  | cons j js ih => simp only [picks, List.flatMap_cons, List.length_append, List.length_replicate,
      List.map_cons, List.sum_cons] at ih ⊢; rw [ih]

omit [Interrupt] in
private theorem picks_single {n} (gs : List (ACBasis.Vec n)) (w : Fin gs.length → Variable)
    (js : List (Fin gs.length)) (i : Fin n) (small : (js.map fun j => gs.get j i).sum ≤ 1)
    {j} (hj : j ∈ js) (pos : 0 < gs.get j i) : picks gs w js i = [w j] := by
  induction js with
  | nil => cases hj
  | cons k js ih =>
    simp only [List.map_cons, List.sum_cons] at small
    change List.replicate (gs.get k i) (w k) ++ picks gs w js i = [w j]
    rcases List.mem_cons.mp hj with rfl | hj
    · have one : gs.get j i = 1 := by omega
      have none : (picks gs w js i).length = 0 := by rw [picks_length]; omega
      rw [one, List.eq_nil_of_length_eq_zero none]
      rfl
    · have le : gs.get j i ≤ (js.map fun j => gs.get j i).sum := by
        have (xs : List Nat) (m : Nat) (hm : m ∈ xs) : m ≤ xs.sum := by
          induction xs with
          | nil => cases hm
          | cons a xs ih =>
            rcases List.mem_cons.mp hm with rfl | hm
            · simp
            · simp only [List.sum_cons]; have := ih hm; omega
        exact this _ _ (List.mem_map_of_mem hj)
      have zero : gs.get k i = 0 := by omega
      rw [zero]
      exact ih (by omega) hj

/-- An answer of `solve` that the constrained solver omits maps a capped column
to a product, or two conflicting columns to the same witness. -/
theorem solveWith_missing {f : sig.ACSym} {rows sorted avoid} {tag : Variable → α} {cap clash σ}
    (mem : σ ∈ solve f rows sorted avoid)
    (absent : σ ∉ solveWith f rows sorted avoid tag cap clash) :
    (∃ v ∈ variables rows, cap (tag v) = true ∧ ∃ a b, σ.image v = .ac f a b) ∨
    ∃ v ∈ variables rows, ∃ u ∈ variables rows, clash (tag v) (tag u) = true ∧
      ∃ w, σ.image v = .var w ∧ σ.image u = .var w := by
  let fr := frame f rows sorted
  let matrix := rows.map (ACBasis.encode fr.names)
  let gs := ACBasis.hilbert matrix
  let tags := Vector.ofFn fun i => tag (fr.names i)
  let w := fun j : Fin gs.length => witness f (variables rows ++ avoid) j.val
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp mem
  obtain ⟨js,-,rfl⟩ := List.mem_map.mp hb
  have out : js.val ∉ chosen gs tags cap clash := by
    intro inside
    apply absent
    exact List.mem_map_of_mem (List.mem_map.mpr ⟨⟨js.val,inside⟩,List.mem_attach _ _,rfl⟩)
  have shape (i : Fin _) := image_selected (avoid := avoid) fr gs (ACBasis.hilbert_correct matrix) w
    (fun _ => rfl) (fun j => unused _ _ j.val) js i
  have product (i : Fin _) (capped : cap (tag (fr.names i)) = true)
      (two : 2 ≤ (js.val.map fun j => gs.get j i).sum) :
      ∃ v ∈ variables rows, cap (tag v) = true ∧ ∃ a b,
        (selectedBranch (avoid := avoid) fr gs (ACBasis.hilbert_correct matrix) w
          (fun _ => rfl) (fun j => unused _ _ j.val) js).answer.image v = .ac f a b := by
    refine ⟨fr.names i,fr.used i,capped,?_⟩
    rw [shape i]
    have len := picks_length gs w js.val i
    match hp : picks gs w js.val i with
    | [] => rw [hp] at len; simp only [List.length_nil] at len; omega
    | [_] => rw [hp] at len; simp only [List.length_cons, List.length_nil] at len; omega
    | u :: u' :: us => exact ⟨_,_,rfl⟩
  have live {g : ACBasis.Vec (variables rows).eraseDups.length} {i}
      (h : i ∈ (List.finRange _).filter fun i => 0 < g i && cap tags[i]) :
      0 < g i ∧ cap (tag (fr.names i)) = true := by
    simpa [tags] using (List.mem_filter.mp h).2
  rcases Homogeneous.constrainedSelections_missing gs _ _ js.property out with ⟨j,hj,bad⟩ | ⟨i,hc,two⟩
  · simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, rejected, Bool.or_eq_true,
      List.any_eq_true] at bad
    have le (i : Fin _) : gs.get j i ≤ (js.val.map fun j => gs.get j i).sum := by
      have (xs : List Nat) (m : Nat) (hm : m ∈ xs) : m ≤ xs.sum := by
        induction xs with
        | nil => cases hm
        | cons a xs ih =>
          rcases List.mem_cons.mp hm with rfl | hm
          · simp
          · simp only [List.sum_cons]; have := ih hm; omega
      exact this _ _ (List.mem_map.mpr ⟨j,hj,rfl⟩)
    rcases bad with ⟨i,hi,two⟩ | ⟨i,hi,k,hk,conflict⟩
    · have two : 2 ≤ gs.get j i := by simpa using two
      exact .inl (product i (live hi).2 (Nat.le_trans two (le i)))
    · by_cases bi : 2 ≤ (js.val.map fun j => gs.get j i).sum
      · exact .inl (product i (live hi).2 bi)
      by_cases bk : 2 ≤ (js.val.map fun j => gs.get j k).sum
      · exact .inl (product k (live hk).2 bk)
      refine .inr ⟨fr.names i,fr.used i,fr.names k,fr.used k,by simpa [tags] using conflict,w j,?_,?_⟩
      · rw [shape i, picks_single gs w js.val i (by omega) hj (live hi).1]; rfl
      · rw [shape k, picks_single gs w js.val k (by omega) hj (live hk).1]; rfl
  · rw [capMask_bit] at hc
    exact .inl (product i (by simpa [tags] using hc) two)

end Constrained

end Tamarin.ACSystem.Reference
