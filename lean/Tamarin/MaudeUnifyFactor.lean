import Tamarin.MaudeUnifySelection
import Tamarin.MaudeUnifyDag
import Tamarin.Cancellation

/-!
# Completeness of the AC step

The AC step of Maude's unification abstracts the arguments of the problems of
one AC symbol by Diophantine variables, computes the basis of the system of
their multiplicities, and builds one unifier for each selection of basis
elements. Whatever values the subterms take in a solution, they factor
through one of the selections: the factor classes of the values give
solutions of the system, each a sum of basis elements; the elements used form
a selection; and each selected element gets as witness the product of the
classes that use it.

This is stated about terms, independently of Maude's state. A subterm with
bound one takes a single factor; two subterms whose stable symbols differ
never take the same factor. Basis elements that force two different stable
symbols together are dropped, as Maude drops them.
-/
namespace Tamarin.MaudeUnify
open Cancellation

variable {s : Signature}

/-- A non-variable top symbol, the stable symbol of an alien subterm. -/
inductive Top (s : Signature) where
  | atom (a : s.Atom)
  | free (f : s.FreeSym)
  | comm (f : s.CSym)
  | ac (f : s.ACSym)

section
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

def Top.beq : Top s → Top s → Bool
  | .atom a, .atom b => decide (a = b)
  | .free f, .free g => decide (f = g)
  | .comm f, .comm g => decide (f = g)
  | .ac f, .ac g => decide (f = g)
  | _, _ => false

/-- Whether a basis element forces two different stable symbols together. -/
def clashes (stable : List (Option (Top s))) (v : List Nat) : Bool :=
  let tops := (stable.zip v).filterMap fun (t, x) => if x = 0 then none else t
  match tops with
  | [] => false
  | t :: ts => ts.any fun u => !t.beq u

/-- The basis in Maude's list order: elements that clash are dropped, the
others pushed to the front. -/
def basisList {n : Nat} (stable : List (Option (Top s))) (sols : List (Vector Nat n)) : List (Vector Nat n) :=
  sols.foldl (fun acc v => if clashes stable v.toList then acc else v :: acc) []

end

/-- The coefficient matrix by columns, one column per subterm. -/
def colsOf (n : Nat) (rows : List (List Int)) : Vector (Vector Int rows.length) n :=
  Vector.ofFn fun i => Vector.ofFn fun j => (rows.getD j []).getD i 0

/-! ### Counting factors -/

/-- Occurrences of a class in a list of classes. -/
noncomputable def cnt (a : Class s) (l : List (Class s)) : Nat := by
  classical exact l.count a

theorem cnt_eq [DecidableEq (Class s)] (a : Class s) (l : List (Class s)) : cnt a l = l.count a := by
  unfold cnt
  congr
  exact Subsingleton.elim _ _

theorem cnt_append (a : Class s) (l m : List (Class s)) : cnt a (l ++ m) = cnt a l + cnt a m := by
  classical
  simp [cnt_eq, List.count_append]

theorem cnt_replicate_self (a : Class s) (k : Nat) : cnt a (List.replicate k a) = k := by
  classical
  simp [cnt_eq]

theorem cnt_replicate_other {a b : Class s} (ne : b ≠ a) (k : Nat) : cnt a (List.replicate k b) = 0 := by
  classical
  simp [cnt_eq, List.count_replicate, ne]

theorem sum_map_add' {α : Type} (l : List α) (g h : α → Nat) :
    (l.map fun x => g x + h x).sum = (l.map g).sum + (l.map h).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem cnt_pos {a : Class s} {l : List (Class s)} : 0 < cnt a l ↔ a ∈ l := by
  classical
  simp [cnt_eq, List.count_pos_iff]

theorem cnt_le_length (a : Class s) (l : List (Class s)) : cnt a l ≤ l.length := by
  classical
  simp only [cnt_eq]
  exact List.count_le_length

theorem perm_of_cnt {l m : List (Class s)} (h : ∀ a, cnt a l = cnt a m) : l.Perm m := by
  classical
  rw [List.perm_iff_count]
  intro a
  simpa [cnt_eq] using h a

theorem sum_indicator [DecidableEq (Class s)] {A : List (Class s)} (nd : A.Nodup) {x : Class s} (hx : x ∈ A) :
    (A.map fun a => if x = a then 1 else 0).sum = 1 := by
  induction A with
  | nil => cases hx
  | cons b bs ihb =>
    obtain ⟨notin, nd'⟩ := List.nodup_cons.mp nd
    simp only [List.map_cons, List.sum_cons]
    by_cases e : x = b
    · subst e
      have zero : ∀ cs : List (Class s), x ∉ cs → (cs.map fun a => if x = a then 1 else 0).sum = 0 := by
        intro cs hcs
        induction cs with
        | nil => rfl
        | cons c cs ihc =>
          have ne : x ≠ c := fun h => hcs (h ▸ List.mem_cons_self)
          simp only [List.map_cons, List.sum_cons, ne, ite_false]
          rw [Nat.zero_add]; exact ihc fun h => hcs (List.mem_cons_of_mem _ h)
      simp [zero bs notin]
    · rcases List.mem_cons.mp hx with h | h
      · exact absurd h e
      · simp [e, ihb nd' h]

/-- Summing a count over a list of distinct classes that contains every
element of a list gives its length. -/
theorem sum_cnt {A : List (Class s)} (nd : A.Nodup) {l : List (Class s)} (sub : ∀ a ∈ l, a ∈ A) :
    (A.map fun a => cnt a l).sum = l.length := by
  classical
  induction l with
  | nil =>
    simp only [cnt_eq, List.count_nil, List.length_nil]
    induction A <;> simp_all
  | cons x xs ih =>
    have ih := ih fun a ha => sub a (List.mem_cons_of_mem _ ha)
    have step : (A.map fun a => cnt a (x :: xs)) = (A.map fun a => (if x = a then 1 else 0) + cnt a xs) := by
      apply List.map_congr_left
      intro a _
      simp only [cnt_eq, List.count_cons, beq_iff_eq]
      by_cases e : x = a
      · subst e; simp; omega
      · simp [e]
    rw [step, sum_map_add', ih]
    have one := sum_indicator nd (sub x List.mem_cons_self)
    simp [one, Nat.add_comm]

/-- The value of a dag-free product: flattening a product of terms is
flattening each of them. -/
theorem flatten_product (f : s.ACSym) {us : List (Term s)} (h : us ≠ []) :
    flatten f (Dag.product f us) = us.flatMap (flatten f) := by
  obtain ⟨u, us, rfl⟩ := List.exists_cons_of_ne_nil h
  induction us generalizing u with
  | nil => simp [Dag.product, ACRepresentation.fold]
  | cons v vs ih =>
    rw [Dag.product_cons_cons, flatten_ac, ih v (by simp)]
    simp

/-- A class that occurs in a flattening is the class of a single factor. -/
theorem single_rep (f : s.ACSym) {a : Class s} {t : Term s} (h : a ∈ flatten f t) :
    ∃ u : Term s, flatten f u = [a] := by
  classical
  induction t with
  | ac g x y ix iy =>
    by_cases e : f = g
    · subst g
      rw [flatten_ac] at h
      rcases List.mem_append.mp h with hx | hy
      · exact ix hx
      · exact iy hy
    · simp only [flatten, ite_eq_right e, List.mem_singleton] at h
      refine ⟨.ac g x y, ?_⟩
      simp only [flatten, ite_eq_right e, h]
  | var v => exact ⟨.var v, by rw [List.mem_singleton.mp h]; rfl⟩
  | atom c => exact ⟨.atom c, by rw [List.mem_singleton.mp h]; rfl⟩
  | free g xs _ => exact ⟨.free g xs, by rw [List.mem_singleton.mp h]; rfl⟩
  | comm g x y _ _ => exact ⟨.comm g x y, by rw [List.mem_singleton.mp h]; rfl⟩

/-! ### Lists of basis elements -/

section Lists
variable {α : Type} [DecidableEq α]

/-- The list with only the first occurrence of each element, skipping `seen`. -/
def nubFrom (seen : List α) : List α → List α
  | [] => []
  | x :: xs => if x ∈ seen then nubFrom seen xs else x :: nubFrom (x :: seen) xs

theorem nubFrom_sublist (seen l : List α) : (nubFrom seen l).Sublist l := by
  induction l generalizing seen with
  | nil => exact .slnil
  | cons x xs ih =>
    simp only [nubFrom]
    split
    · exact (ih seen).cons x
    · exact (ih (x :: seen)).cons_cons x

theorem mem_nubFrom (seen l : List α) (y : α) : y ∈ nubFrom seen l ↔ y ∈ l ∧ y ∉ seen := by
  induction l generalizing seen with
  | nil => simp [nubFrom]
  | cons x xs ih =>
    simp only [nubFrom]
    split
    · next hx =>
      rw [ih]
      constructor
      · rintro ⟨h, n⟩; exact ⟨List.mem_cons_of_mem _ h, n⟩
      · rintro ⟨h, n⟩
        rcases List.mem_cons.mp h with rfl | h
        · exact absurd hx n
        · exact ⟨h, n⟩
    · rw [List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨h, n⟩)
        · next hx => exact ⟨List.mem_cons_self, hx⟩
        · exact ⟨List.mem_cons_of_mem _ h, fun m => n (List.mem_cons_of_mem _ m)⟩
      · rintro ⟨h, n⟩
        by_cases e : y = x
        · exact .inl e
        · rcases List.mem_cons.mp h with h | h
          · exact absurd h e
          · exact .inr ⟨h, by simp [e, n]⟩

theorem nodup_nubFrom (seen l : List α) : (nubFrom seen l).Nodup := by
  induction l generalizing seen with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    simp only [nubFrom]
    split
    · exact ih seen
    · refine List.nodup_cons.mpr ⟨fun h => ?_, ih _⟩
      exact ((mem_nubFrom _ _ _).mp h).2 List.mem_cons_self

theorem sum_indicator' (S : List α) (nd : S.Nodup) {x : α} (hx : x ∈ S) (φ : α → Nat) :
    (S.map fun g => if x = g then φ g else 0).sum = φ x := by
  induction S with
  | nil => cases hx
  | cons b bs ih =>
    obtain ⟨notin, nd'⟩ := List.nodup_cons.mp nd
    simp only [List.map_cons, List.sum_cons]
    by_cases e : x = b
    · subst e
      have zero : ∀ cs : List α, x ∉ cs → (cs.map fun g => if x = g then φ g else 0).sum = 0 := by
        intro cs hcs
        induction cs with
        | nil => rfl
        | cons c cs ihc =>
          have ne : x ≠ c := fun h => hcs (h ▸ List.mem_cons_self)
          simp only [List.map_cons, List.sum_cons, ne, ite_false]
          rw [Nat.zero_add]; exact ihc fun h => hcs (List.mem_cons_of_mem _ h)
      simp [zero bs notin]
    · rcases List.mem_cons.mp hx with h | h
      · exact absurd h e
      · simp [e, ih nd' h]

/-- A sum over a list whose elements lie in a list of distinct elements is a
weighted sum over the latter, weighted by occurrences. -/
theorem sum_by_count (S : List α) (nd : S.Nodup) (L : List α) (sub : ∀ x ∈ L, x ∈ S) (φ : α → Nat) :
    (L.map φ).sum = (S.map fun g => L.count g * φ g).sum := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil, List.count_nil, Nat.zero_mul]
    clear nd sub
    induction S with
    | nil => rfl
    | cons _ _ ih => simp [← ih]
  | cons x xs ih =>
    have ih := ih fun y hy => sub y (List.mem_cons_of_mem _ hy)
    have step : (S.map fun g => (x :: xs).count g * φ g) =
        S.map fun g => (if x = g then φ g else 0) + xs.count g * φ g := by
      apply List.map_congr_left
      intro g _
      simp only [List.count_cons, beq_iff_eq]
      by_cases e : x = g
      · subst e; simp [Nat.add_mul, Nat.add_comm]
      · simp [e]
    rw [step, sum_map_add', ← ih, sum_indicator' S nd (sub x List.mem_cons_self)]
    simp

/-- A sum over distinct elements of a list is at most the sum over the list. -/
theorem sum_le_of_subset (S : List α) (nd : S.Nodup) (L : List α) (sub : ∀ x ∈ S, x ∈ L) (φ : α → Nat) :
    (S.map φ).sum ≤ (L.map φ).sum := by
  induction S generalizing L with
  | nil => simp
  | cons g gs ih =>
    obtain ⟨notin, nd'⟩ := List.nodup_cons.mp nd
    have hg := sub g List.mem_cons_self
    have perm := List.perm_cons_erase hg
    have total : (L.map φ).sum = φ g + ((L.erase g).map φ).sum := by
      rw [(perm.map φ).sum_nat]; simp
    have rest := ih nd' (L.erase g) fun x hx =>
      (List.mem_erase_of_ne (fun e => notin (by rw [← e]; exact hx))).mpr (sub x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons]
    omega

end Lists

section Basis
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

theorem mem_basisList {n : Nat} {stable : List (Option (Top s))} {sols : List (Vector Nat n)} {v : Vector Nat n} :
    v ∈ basisList stable sols ↔ v ∈ sols ∧ clashes stable v.toList = false := by
  unfold basisList
  have gen : ∀ (acc : List (Vector Nat n)) (l : List (Vector Nat n)),
      v ∈ l.foldl (fun acc v => if clashes stable v.toList then acc else v :: acc) acc ↔
        v ∈ acc ∨ (v ∈ l ∧ clashes stable v.toList = false) := by
    intro acc l
    induction l generalizing acc with
    | nil => simp
    | cons w ws ih =>
      simp only [List.foldl_cons]
      rw [ih]
      split
      · next c =>
        constructor
        · rintro (h | ⟨h, n⟩)
          · exact .inl h
          · exact .inr ⟨List.mem_cons_of_mem _ h, n⟩
        · rintro (h | ⟨h, n⟩)
          · exact .inl h
          · rcases List.mem_cons.mp h with rfl | h
            · rw [c] at n; cases n
            · exact .inr ⟨h, n⟩
      · next c =>
        simp only [List.mem_cons]
        constructor
        · rintro ((rfl | h) | ⟨h, n⟩)
          · exact .inr ⟨.inl rfl, by simpa using c⟩
          · exact .inl h
          · exact .inr ⟨.inr h, n⟩
        · rintro (h | ⟨rfl | h, n⟩)
          · exact .inl (.inr h)
          · exact .inl (.inl rfl)
          · exact .inr ⟨h, n⟩
  rw [gen]
  simp

theorem Top.beq_self (x : Top s) : x.beq x = true := by
  cases x <;> simp [Top.beq]

/-- A clashing element is positive at two coordinates whose stable symbols differ. -/
theorem clashes_spec {stable : List (Option (Top s))} {v : List Nat} (h : clashes stable v = true) :
    ∃ i j x y, v.getD i 0 ≠ 0 ∧ v.getD j 0 ≠ 0 ∧ stable.getD i none = some x ∧
      stable.getD j none = some y ∧ x.beq y = false := by
  unfold clashes at h
  dsimp only at h
  have from_zip : ∀ t, t ∈ (stable.zip v).filterMap (fun (t, x) => if x = 0 then none else t) →
      ∃ i, v.getD i 0 ≠ 0 ∧ stable.getD i none = some t := by
    intro t ht
    obtain ⟨⟨o, x⟩, hp, ho⟩ := List.mem_filterMap.mp ht
    obtain ⟨i, hi, eq⟩ := List.mem_iff_getElem.mp hp
    rw [List.getElem_zip] at eq
    simp only [Prod.mk.injEq] at eq
    obtain ⟨e1, e2⟩ := eq
    have hs : i < stable.length := by simp at hi; omega
    have hv : i < v.length := by simp at hi; omega
    by_cases nz : x = 0
    · simp [nz] at ho
    · simp only [nz, ite_false] at ho
      refine ⟨i, ?_, ?_⟩
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv, Option.getD_some, e2]; exact nz
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs, Option.getD_some, e1, ho]
  split at h
  · cases h
  · next t ts eq =>
    obtain ⟨u, hu, bad⟩ := List.any_eq_true.mp h
    obtain ⟨i, hi, si⟩ := from_zip t (by rw [eq]; exact List.mem_cons_self)
    obtain ⟨j, hj, sj⟩ := from_zip u (by rw [eq]; exact List.mem_cons_of_mem _ hu)
    exact ⟨i, j, t, u, hi, hj, si, sj, by simpa using bad⟩

end Basis

/-! ### The factorization -/

open ACBasis.Hilbert in
/-- The rows hold for the values of the subterms: for every factor class, the
multiplicities weighted by the occurrences of the class sum to zero. -/
def RowsHold (f : s.ACSym) {n : Nat} (ts : Fin n → Term s) (rows : List (List Int)) : Prop :=
  ∀ r : Fin rows.length, ∀ a : Class s,
    isum (fun i : Fin n => (rows[r]).getD i 0 * (cnt a (flatten f (ts i)) : Int)) = 0

theorem cnt_flatMap {α : Type} (b : Class s) (L : List α) (h : α → List (Class s)) :
    cnt b (L.flatMap h) = (L.map fun x => cnt b (h x)).sum := by
  induction L with
  | nil => classical simp [cnt_eq]
  | cons x xs ih => simp [List.flatMap_cons, cnt_append, ih]

theorem cnt_replicate_flatten (b : Class s) (k : Nat) (l : List (Class s)) :
    cnt b (List.replicate k l).flatten = k * cnt b l := by
  induction k with
  | zero => classical simp [cnt_eq]
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, cnt_append, ih, Nat.succ_mul, Nat.add_comm]

theorem flatten_ne_nil (f : s.ACSym) (t : Term s) : flatten f t ≠ [] := by
  intro h
  have := fold_flatten f t
  rw [h] at this
  cases this

theorem lt_of_getD_ne {l : List Nat} {i : Nat} (h : l.getD i 0 ≠ 0) : i < l.length := by
  rw [List.getD_eq_getElem?_getD] at h
  apply Classical.byContradiction
  intro c
  rw [List.getElem?_eq_none (by omega)] at h
  exact h rfl

theorem sum_flatMap {α β : Type} (L : List α) (h : α → List β) (φ : β → Nat) :
    ((L.flatMap h).map φ).sum = (L.map fun x => ((h x).map φ).sum).sum := by
  induction L with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, ih]

theorem flatMap_congr' {α β : Type} {L : List α} {h k : α → List β} (e : ∀ x ∈ L, h x = k x) :
    L.flatMap h = L.flatMap k := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, List.flatMap_cons, e x List.mem_cons_self,
      ih fun y hy => e y (List.mem_cons_of_mem _ hy)]

theorem count_inst {α : Type} [DecidableEq α] [i1 : BEq α] [LawfulBEq α] (a : α) (l : List α) :
    @List.count α instBEqOfDecidableEq a l = @List.count α i1 a l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.count_cons, ih]
    by_cases h : x = a
    · subst h; simp
    · simp [h]

theorem sum_replicate' {β : Type} (k : Nat) (x : β) (φ : β → Nat) :
    ((List.replicate k x).map φ).sum = k * φ x := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.map_cons, List.sum_cons, ih, Nat.succ_mul, Nat.add_comm]

theorem sum_map_zero {β : Type} (L : List β) : (L.map fun _ => (0 : Nat)).sum = 0 := by
  induction L with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem le_sum_of_mem {α : Type} {L : List α} {x : α} (hx : x ∈ L) (φ : α → Nat) : φ x ≤ (L.map φ).sum := by
  induction L with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | h
    · omega
    · have := ih h; omega

theorem exists_pos_of_sum {α : Type} {L : List α} {φ : α → Nat} (h : 0 < (L.map φ).sum) : ∃ x ∈ L, 0 < φ x := by
  induction L with
  | nil => simp at h
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons] at h
    by_cases p : 0 < φ y
    · exact ⟨y, List.mem_cons_self, p⟩
    · obtain ⟨x, hx, px⟩ := ih (by omega)
      exact ⟨x, List.mem_cons_of_mem _ hx, px⟩

theorem zip_map_flatMap {n : Nat} {α : Type} (T : List (Select.Elem n)) (S0 : List (Vector Nat n)) (w : Vector Nat n → α)
    (hT : T.map (·.vec) = S0) (i : Fin n) :
    (T.zip (S0.map w)).flatMap (fun p => List.replicate p.1.vec[i] p.2) =
      S0.flatMap fun g => List.replicate g[i] (w g) := by
  subst hT
  induction T with
  | nil => rfl
  | cons e es ih =>
    show List.flatMap _ ((e, w e.vec) :: es.zip (List.map w (List.map (·.vec) es))) =
      List.flatMap _ (e.vec :: List.map (·.vec) es)
    rw [List.flatMap_cons, List.flatMap_cons, ih]

variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

open ACBasis.Hilbert in
/-- Whatever values a solution gives the subterms, they factor through a
selection of the basis: each selected element gets a witness, and each
subterm is the product of the witnesses of the selected elements, each as
often as the element counts the subterm. -/
theorem factor (f : s.ACSym) {n : Nat} (ts : Fin n → Term s) (rows : List (List Int))
    (upper : Vector (Option Nat) n) (stable : List (Option (Top s))) {fuel : Nat}
    {sols : List (Vector Nat n)} (hb : Dioph.basis (colsOf n rows) upper fuel = some sols)
    (pos : ∀ i : Fin n, upper[i] ≠ some 0)
    (hold : RowsHold f ts rows)
    (bnd : ∀ i : Fin n, ∀ u, upper[i] = some u → (flatten f (ts i)).length ≤ u)
    (stab : ∀ i j : Fin n, ∀ x y, stable.getD i none = some x → stable.getD j none = some y →
      x.beq y = false → ∀ a, a ∈ flatten f (ts i) → a ∉ flatten f (ts j)) :
    ∃ T ∈ Select.all upper (basisList stable sols), ∃ ws : List (Term s), ws.length = T.length ∧
      ∀ i : Fin n, EquivB (ts i)
        (Dag.product f ((T.zip ws).flatMap fun p => List.replicate p.1.vec[i] p.2)) := by
  classical
  -- the columns of the factor classes
  let col : Class s → Vector Nat n := fun a => Vector.ofFn fun i => cnt a (flatten f (ts i))
  have colAt : ∀ a (i : Fin n), (col a)[i] = cnt a (flatten f (ts i)) := fun a i => Dioph.vget_ofFn _ i
  have sol : ∀ a, Sol (colsOf n rows) (col a) := by
    intro a r
    have h := hold r a
    unfold res
    rw [← h]
    congr 1
    funext i
    rw [colAt]
    simp only [colsOf, Dioph.vget_ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem r.isLt,
      Option.getD_some]
    rfl
  have within : ∀ a, Dioph.Within upper (col a) := fun a i u hu => by
    rw [colAt]; exact Nat.le_trans (cnt_le_length _ _) (bnd i u hu)
  have gen := fun a => Dioph.basis_generates (colsOf n rows) upper fuel hb pos (col a) (sol a) (within a)
  let gs : Class s → List (Vector Nat n) := fun a => Classical.choose (gen a)
  have gsSols : ∀ a, ∀ g ∈ gs a, g ∈ sols := fun a => (Classical.choose_spec (gen a)).1
  have gsSum : ∀ a (i : Fin n), (col a)[i] = ((gs a).map fun g => g[i]).sum :=
    fun a => (Classical.choose_spec (gen a)).2
  -- the classes that occur
  let A := nubFrom [] ((List.finRange n).flatMap fun i => flatten f (ts i))
  have ndA : A.Nodup := nodup_nubFrom _ _
  have memA : ∀ a, a ∈ A ↔ ∃ i, a ∈ flatten f (ts i) := by
    intro a
    rw [mem_nubFrom]
    simp
  -- an element used by a class is positive only where the class occurs
  have usedAt : ∀ a, ∀ g ∈ gs a, ∀ i : Fin n, 0 < g[i] → a ∈ flatten f (ts i) := by
    intro a g hg i p
    have le := le_sum_of_mem hg (fun g : Vector Nat n => g[i])
    rw [← gsSum, colAt] at le
    exact cnt_pos.mp (by omega)
  let U := A.flatMap gs
  have inBasis : ∀ g ∈ U, g ∈ basisList stable sols := by
    intro g hg
    obtain ⟨a, _, hga⟩ := List.mem_flatMap.mp hg
    refine mem_basisList.mpr ⟨gsSols a g hga, ?_⟩
    cases c : clashes stable g.toList with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨i, j, x, y, hi, hj, sx, sy, ne⟩ := clashes_spec c
      have li : i < n := by have := lt_of_getD_ne hi; simpa using this
      have lj : j < n := by have := lt_of_getD_ne hj; simpa using this
      have gi : 0 < g[(⟨i, li⟩ : Fin n)] := by
        have : g.toList.getD i 0 = g[(⟨i, li⟩ : Fin n)] := by
          simp [List.getD_eq_getElem?_getD, getElem?_pos g i li]
        omega
      have gj : 0 < g[(⟨j, lj⟩ : Fin n)] := by
        have : g.toList.getD j 0 = g[(⟨j, lj⟩ : Fin n)] := by
          simp [List.getD_eq_getElem?_getD, getElem?_pos g j lj]
        omega
      exact stab ⟨i, li⟩ ⟨j, lj⟩ x y sx sy ne a (usedAt a g hga _ gi) (usedAt a g hga _ gj)
  -- the selection: the elements used, in basis order, once each
  let S0 := nubFrom [] ((basisList stable sols).filter fun g => decide (g ∈ U))
  have subS0 : S0.Sublist (basisList stable sols) := (nubFrom_sublist _ _).trans List.filter_sublist
  have ndS0 : S0.Nodup := nodup_nubFrom _ _
  have memS0 : ∀ g, g ∈ S0 ↔ g ∈ U := by
    intro g
    rw [mem_nubFrom]
    simp only [List.mem_filter, decide_eq_true_eq, List.not_mem_nil, not_false_eq_true, and_true]
    exact ⟨fun h => h.2, fun h => ⟨inBasis g h, h⟩⟩
  have fit : ∀ i : Fin n, Dioph.fits upper[i] ((S0.map fun v => v[i]).sum) = true := by
    intro i
    rw [Dioph.fits_iff]
    intro u hu
    have le1 := sum_le_of_subset S0 ndS0 U (fun g hg => (memS0 g).mp hg) (fun v : Vector Nat n => v[i])
    have eqU : (U.map fun v : Vector Nat n => v[i]).sum = (A.map fun a => (col a)[i]).sum := by
      simp only [U]
      rw [sum_flatMap]
      congr 1
      apply List.map_congr_left
      intro a _
      rw [gsSum]
    have eqA : (A.map fun a => (col a)[i]).sum = (flatten f (ts i)).length := by
      simp only [colAt]
      exact sum_cnt ndA fun a ha => (memA a).mpr ⟨i, ha⟩
    have := bnd i u hu
    omega
  have cov : ∀ i : Fin n, ∃ v ∈ S0, 0 < v[i] := by
    intro i
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ (flatten_ne_nil f (ts i))
    have p : 0 < (col a)[i] := by rw [colAt]; exact cnt_pos.mpr ha
    rw [gsSum] at p
    obtain ⟨g, hg, pg⟩ := exists_pos_of_sum p
    exact ⟨g, (memS0 g).mpr (List.mem_flatMap.mpr ⟨a, (memA a).mpr ⟨i, ha⟩, hg⟩), pg⟩
  obtain ⟨T, hT, hTv⟩ := Select.all_complete upper (basisList stable sols) S0 subS0 fit cov
  -- witnesses
  let rep : Class s → Term s := fun a =>
    if h : ∃ u : Term s, flatten f u = [a] then Classical.choose h else Dag.dflt
  have repSpec : ∀ a ∈ A, flatten f (rep a) = [a] := by
    intro a ha
    obtain ⟨i, hi⟩ := (memA a).mp ha
    have h := single_rep f hi
    simp only [rep, dite_eq_left_of_eq_true (eq_true h)]
    exact Classical.choose_spec h
  let block : Vector Nat n → List (Class s) := fun g => A.flatMap fun a => List.replicate ((gs a).count g) a
  let w : Vector Nat n → Term s := fun g => Dag.product f ((block g).map rep)
  have blockFlat : ∀ g ∈ S0, flatten f (w g) = block g := by
    intro g hg
    obtain ⟨a, ha, hga⟩ := List.mem_flatMap.mp ((memS0 g).mp hg)
    have ne : (block g).map rep ≠ [] := by
      intro h
      have : a ∈ block g := List.mem_flatMap.mpr ⟨a, ha, List.mem_replicate.mpr
        ⟨by have := List.count_pos_iff.mpr hga; omega, rfl⟩⟩
      rw [List.map_eq_nil_iff] at h
      rw [h] at this
      cases this
    simp only [w]
    rw [flatten_product f ne, List.flatMap_map]
    have : ∀ x ∈ block g, flatten f (rep x) = [x] := by
      intro x hx
      obtain ⟨b, hb, hx⟩ := List.mem_flatMap.mp hx
      rw [(List.mem_replicate.mp hx).2]
      exact repSpec b hb
    rw [flatMap_congr' this]
    simp
  refine ⟨T, hT, S0.map w, by rw [List.length_map, ← hTv, List.length_map], fun i => ?_⟩
  rw [zip_map_flatMap T S0 w hTv i]
  have ne : S0.flatMap (fun g => List.replicate g[i] (w g)) ≠ [] := by
    obtain ⟨g, hg, pg⟩ := cov i
    intro h
    have : w g ∈ S0.flatMap (fun g => List.replicate g[i] (w g)) :=
      List.mem_flatMap.mpr ⟨g, hg, List.mem_replicate.mpr ⟨by omega, rfl⟩⟩
    rw [h] at this
    cases this
  apply equiv_of_flatten_perm f
  rw [flatten_product f ne]
  apply perm_of_cnt
  intro b
  rw [cnt_flatMap, sum_flatMap]
  have inner : ∀ g ∈ S0, ((List.replicate g[i] (w g)).map fun x => cnt b (flatten f x)).sum =
      g[i] * cnt b (block g) := by
    intro g hg
    rw [sum_replicate', blockFlat g hg]
  rw [List.map_congr_left inner]
  by_cases hbA : b ∈ A
  · have blockCnt : ∀ g, cnt b (block g) = (gs b).count g := by
      intro g
      simp only [block]
      rw [cnt_flatMap]
      have : (A.map fun a => cnt b (List.replicate ((gs a).count g) a)) =
          A.map fun a => if b = a then (gs a).count g else 0 := by
        apply List.map_congr_left
        intro a _
        by_cases e : b = a
        · subst e; simp [cnt_replicate_self]
        · simp [e, cnt_replicate_other (Ne.symm e)]
      rw [this, sum_indicator' A ndA hbA (fun a => (gs a).count g)]
    simp only [blockCnt]
    have viaCount := sum_by_count S0 ndS0 (gs b)
      (fun g hg => (memS0 g).mpr (List.mem_flatMap.mpr ⟨b, hbA, hg⟩)) (fun g : Vector Nat n => g[i])
    rw [← colAt, gsSum]
    rw [viaCount]
    congr 1
    apply List.map_congr_left
    intro g _
    rw [Nat.mul_comm]
    congr 1
    exact count_inst _ _
  · have zero : cnt b (flatten f (ts i)) = 0 := by
      apply Classical.byContradiction
      intro h
      exact hbA ((memA b).mpr ⟨i, cnt_pos.mp (by omega)⟩)
    have blockZero : ∀ g, cnt b (block g) = 0 := by
      intro g
      simp only [block]
      rw [cnt_flatMap]
      apply List.sum_eq_zero_iff_forall_eq_nat.mpr
      intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      exact cnt_replicate_other (fun e => hbA (by rw [← e]; exact ha)) _
    simp only [zero, blockZero, Nat.mul_zero]
    exact (sum_map_zero S0).symm

end Tamarin.MaudeUnify
