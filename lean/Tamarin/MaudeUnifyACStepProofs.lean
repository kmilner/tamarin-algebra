import Tamarin.MaudeUnifyClassify

/-!
# Proofs about the AC subproblem

Auxiliary lemmas for `acStates_wf`, `acStates_sound` and `acStates_complete`:
sums over selections, the value of what `assign` gives a subterm, the
witnesses, `buildFrom`, and the subterms the rows are built over.
-/
namespace Tamarin.MaudeUnify
open Cancellation


variable {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

/-! ### Sums over lists -/

theorem sum_zip_eq {α β : Type} : ∀ (A : List α) (B : List β) (φ : α → Nat) (ψ : β → Nat),
    A.length = B.length → (∀ p (h1 : p < A.length) (h2 : p < B.length), φ A[p] = ψ B[p]) →
    (A.map φ).sum = (B.map ψ).sum
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | a :: as, b :: bs, φ, ψ, hl, h => by
    simp only [List.map_cons, List.sum_cons]
    have h0 := h 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at h0
    rw [h0, sum_zip_eq as bs φ ψ (by simpa using hl)
      (fun p h1 h2 => h (p + 1) (by simpa using h1) (by simpa using h2))]

theorem sum_single_idx {α : Type} : ∀ (A : List α) (φ : α → Nat) (p : Nat) (hp : p < A.length),
    (∀ q (hq : q < A.length), q ≠ p → φ A[q] = 0) → (A.map φ).sum = φ A[p]
  | [], _, _, hp, _ => by simp at hp
  | a :: as, φ, 0, _, h => by
    simp only [List.map_cons, List.sum_cons, List.getElem_cons_zero]
    have : (as.map φ).sum = 0 := by
      apply List.sum_eq_zero_iff_forall_eq_nat.mpr
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.mp hy
      exact h (q + 1) (by simpa using hq) (by omega)
    omega
  | a :: as, φ, p + 1, hp, h => by
    simp only [List.map_cons, List.sum_cons, List.getElem_cons_succ]
    have h0 := h 0 (by simp) (by omega)
    simp only [List.getElem_cons_zero] at h0
    rw [h0, sum_single_idx as φ p (by simpa using hp)
      (fun q hq ne => h (q + 1) (by simpa using hq) (by omega))]
    simp

theorem mem_zip_of_mem_left {α β : Type} {A : List α} {B : List β} {x : α} (hx : x ∈ A)
    (hl : A.length ≤ B.length) : ∃ y, (x, y) ∈ A.zip B := by
  obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hx
  refine ⟨B[p]'(by omega), ?_⟩
  have : p < (A.zip B).length := by simp; omega
  have e := List.getElem_mem this
  rw [List.getElem_zip] at e
  exact e

theorem isum_swap {k : Nat} {β : Type} (x : Fin k → Int) (g : β → Fin k → Int) (c : β → Int) :
    ∀ (Z : List β), ACBasis.Hilbert.isum (fun i => x i * (Z.map fun q => g q i * c q).sum) =
      (Z.map fun q => c q * ACBasis.Hilbert.isum (fun i => x i * g q i)).sum
  | [] => by simp [ACBasis.Hilbert.isum_const_zero]
  | q :: qs => by
    simp only [List.map_cons, List.sum_cons]
    rw [← isum_swap x g c qs, ← ACBasis.Hilbert.isum_mul_left, ← ACBasis.Hilbert.isum_add]
    congr 1
    funext i
    rw [Int.mul_add, Int.mul_comm (g q i) (c q), ← Int.mul_assoc, Int.mul_comm (x i) (c q), Int.mul_assoc]

/-- A row over the subterms as a sum over its coordinates. -/
theorem sum_zip_isum {α : Type} (w : α → Int) :
    ∀ (l : List α) (R : List Int), R.length ≤ l.length →
      ((l.zip R).map fun p => p.2 * w p.1).sum =
        ACBasis.Hilbert.isum (fun i : Fin l.length => R.getD i 0 * w l[i])
  | [], _, _ => by simp [ACBasis.Hilbert.isum_zero]
  | x :: xs, [], _ => by
    simp only [List.zip_nil_right, List.map_nil, List.sum_nil, List.getD_nil, Int.zero_mul]
    exact (ACBasis.Hilbert.isum_const_zero _).symm
  | x :: xs, c :: cs, h => by
    rw [ACBasis.Hilbert.isum_first]
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
    rw [sum_zip_isum w xs cs (by simpa using h)]
    simp

/-! ### Counting the factors of products -/

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem cnt_of_equiv (f : s.ACSym) {t u : Term s} (h : EquivB t u) (a : Class s) :
    cnt a (flatten f t) = cnt a (flatten f u) := by
  classical
  rw [cnt_eq, cnt_eq]
  exact (flatten_equiv f h).count_eq a

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem equiv_of_cnt (f : s.ACSym) {t u : Term s} (h : ∀ a, cnt a (flatten f t) = cnt a (flatten f u)) :
    EquivB t u :=
  equiv_of_flatten_perm f (perm_of_cnt h)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem cnt_product_flatMap {γ : Type} (f : s.ACSym) (P : List γ) (m : γ → Nat) (t : γ → Term s)
    (ne : P.flatMap (fun p => List.replicate (m p) (t p)) ≠ []) (a : Class s) :
    cnt a (flatten f (Dag.product f (P.flatMap fun p => List.replicate (m p) (t p)))) =
      (P.map fun p => m p * cnt a (flatten f (t p))).sum := by
  rw [flatten_product f ne, cnt_flatMap, sum_flatMap]
  congr 1
  apply List.map_congr_left
  intro p _
  exact sum_replicate' (m p) (t p) (fun x => cnt a (flatten f x))

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem flatMap_replicate_ne {γ : Type} {P : List γ} {m : γ → Nat} {t : γ → Term s} {p : γ}
    (hp : p ∈ P) (pos : 0 < m p) : P.flatMap (fun p => List.replicate (m p) (t p)) ≠ [] := by
  intro h
  have : t p ∈ P.flatMap (fun p => List.replicate (m p) (t p)) :=
    List.mem_flatMap.mpr ⟨p, hp, List.mem_replicate.mpr ⟨by omega, rfl⟩⟩
  rw [h] at this
  cases this

/-! ### What `assign` gives a subterm -/

variable (r : Ranks s)

/-- The value of what the selection assigns to subterm `i`: the product of
the witnesses, each as often as its element counts the subterm. -/
def assignVal (f : s.ACSym) (ρ : Nat → Term s) (sel : List (List Nat)) (ws : List (Dag s)) (i : Nat) : Term s :=
  Dag.product f ((sel.zip ws).flatMap fun p => List.replicate (p.1.getD i 0) (Dag.eval ρ p.2))

theorem flatMap_filter_drop {α β : Type} (q : α → Bool) (g : α → List β)
    (hg : ∀ p, q p = false → g p = []) :
    ∀ (l : List α), (l.filter q).flatMap g = l.flatMap g
  | [] => rfl
  | p :: ps => by
    rw [List.filter_cons]
    split
    · simp only [List.flatMap_cons]; rw [flatMap_filter_drop q g hg ps]
    · next hn =>
      simp only [List.flatMap_cons, hg p (by simpa using hn), List.nil_append]
      exact flatMap_filter_drop q g hg ps

theorem normPicks_perm (so : Nat → Option SortId) (f : s.ACSym) (picks : List (Dag s × Nat))
    (h : ∀ p ∈ picks, ∃ v, p.1 = .var v) :
    (normPicks r so f picks).Perm (picks.flatMap fun p => List.replicate p.2 p.1) := by
  unfold normPicks
  rw [ite_eq_left (List.all_eq_true.mpr fun p hp => by obtain ⟨v, e⟩ := h p hp; rw [e])]
  refine ((List.mergeSort_perm _ _).flatMap_right _).trans ?_
  rw [List.flatMap_map]
  exact .refl _

theorem eval_normPicks (so : Nat → Option SortId) (f : s.ACSym) (ρ : Nat → Term s) (picks : List (Dag s × Nat)) :
    EquivB (Dag.eval ρ (.ac f (normPicks r so f picks)))
      (Dag.eval ρ (.ac f (picks.flatMap fun p => List.replicate p.2 p.1))) := by
  unfold normPicks
  split
  · rw [Dag.eval_ac, Dag.eval_ac]
    refine Dag.product_perm f ((((List.mergeSort_perm _ _).flatMap_right _).trans ?_).map _)
    rw [List.flatMap_map]
    exact .refl _
  · exact Dag.eval_normAC r so ρ f _

theorem eval_assign (st : St s) (f : s.ACSym) (ρ : Nat → Term s) (sel : List (List Nat))
    (ws : List (Dag s)) (i : Nat) :
    EquivB (Dag.eval ρ (assign r st f sel ws i).1) (assignVal f ρ sel ws i) := by
  have filt := flatMap_filter_drop (fun x : List Nat × Dag s => decide (0 < x.fst.getD i 0))
    (fun p => List.replicate (p.1.getD i 0) (Dag.eval ρ p.2))
    (fun p h => by simp only [decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero] at h; rw [h]; rfl) (sel.zip ws)
  unfold assignVal
  rw [← filt]
  unfold assign
  dsimp only
  generalize (sel.zip ws).filter (fun x : List Nat × Dag s => decide (0 < x.fst.getD i 0)) = P
  have flat : ((P.map fun (x : List Nat × Dag s) => (x.2, x.1.getD i 0)).flatMap
      fun p => List.replicate p.2 p.1).map (Dag.eval ρ) =
      P.flatMap fun p => List.replicate (p.1.getD i 0) (Dag.eval ρ p.2) := by
    simp [List.map_flatMap, List.flatMap_map, List.map_replicate]
  split
  · next w hpick =>
    obtain ⟨⟨e, w'⟩, hP, he⟩ := List.map_eq_singleton_iff.mp hpick
    obtain ⟨rfl, h1⟩ := Prod.mk.inj he
    subst hP
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, h1, List.replicate_one]
    exact .refl _
  · refine .trans (eval_normPicks r st.sortOf f ρ _) ?_
    rw [Dag.eval_ac, flat]
    exact .refl _

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem cnt_assignVal (f : s.ACSym) (ρ : Nat → Term s) (sel : List (List Nat)) (ws : List (Dag s)) (i : Nat)
    (cov : ∃ p ∈ sel.zip ws, 0 < p.1.getD i 0) (a : Class s) :
    cnt a (flatten f (assignVal f ρ sel ws i)) =
      ((sel.zip ws).map fun p => p.1.getD i 0 * cnt a (flatten f (Dag.eval ρ p.2))).sum := by
  obtain ⟨p, hp, pos⟩ := cov
  exact cnt_product_flatMap f (sel.zip ws) (fun p => p.1.getD i 0) (fun p => Dag.eval ρ p.2)
    (flatMap_replicate_ne hp pos) a

/-! ### States -/

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem value_ge (st : St s) {i : Nat} (h : st.vals.size ≤ i) : st.value i = none := by
  unfold St.value
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem value_fresh (st : St s) (i : Nat) : st.fresh.1.value i = st.value i := by
  unfold St.value St.fresh
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split
  · next e => subst e; simp
  · rfl

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem sortOf_fresh (st : St s) (i : Nat) : st.fresh.1.sortOf i = st.sortOf i := by
  unfold St.sortOf St.fresh
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split
  · next e => subst e; simp
  · rfl

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem size_fresh (st : St s) : st.fresh.1.vals.size = st.vals.size + 1 := by
  simp [St.fresh]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem sorts_size_fresh (st : St s) : st.fresh.1.sorts.size = st.sorts.size + 1 := by
  simp [St.fresh]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem sortOf_bind (st : St s) (i : Nat) (v : Option (Dag s)) (j : Nat) :
    (st.bind i v).sortOf j = st.sortOf j := rfl

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem acp_eval_agree {n : Nat} {ρ ρ' : Nat → Term s} (ag : Agree n ρ ρ') {d : Dag s} (hd : d.Below n) :
    Dag.eval ρ' d = Dag.eval ρ d :=
  Dag.eval_congr d (fun i hi => ag i (hd i hi))

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem agree_trans {n m : Nat} {ρ ρ' ρ'' : Nat → Term s} (a1 : Agree n ρ ρ') (a2 : Agree m ρ' ρ'')
    (le : n ≤ m) : Agree n ρ ρ'' := fun i hi => (a2 i (by omega)).trans (a1 i hi)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem below_mono {n m : Nat} {d : Dag s} (hd : d.Below n) (le : n ≤ m) : d.Below m :=
  fun i hi => Nat.lt_of_lt_of_le (hd i hi) le

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem fit_mono {n m : Nat} {d : Dag s} (hd : d.Fit n) (le : n ≤ m) : d.Fit m :=
  ⟨hd.1, below_mono hd.2 le⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem fit_var {n x : Nat} (h : x < n) : (Dag.var x : Dag s).Fit n :=
  ⟨by simp [Dag.Wf], fun i hi => by simp [Dag.vars] at hi; omega⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem lt_of_fit_var {n x : Nat} (h : (Dag.var x : Dag s).Fit n) : x < n :=
  h.2 x (by simp [Dag.vars])

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem fit_of_mem_ac {n : Nat} {g : s.ACSym} {args : List (Dag s)} (h : (Dag.ac g args).Fit n)
    {a : Dag s} (ha : a ∈ args) : a.Fit n := by
  have hw : Dag.Wf (.ac g args) := h.1
  simp only [Dag.Wf] at hw
  refine ⟨hw.2 a ha, fun i hi => h.2 i ?_⟩
  rw [Dag.vars_ac]
  exact List.mem_flatMap.mpr ⟨a, ha, hi⟩

/-- Slots bound to variables point below `N`. -/
def VarsBelow (st : St s) (N : Nat) : Prop := ∀ i y, st.value i = some (.var y) → y < N

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem Bounded.varsBelow {st : St s} (b : Bounded st) : VarsBelow st st.vals.size :=
  fun i _ h => lt_of_fit_var (b.vals i _ h)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem follow_lt {st : St s} {N : Nat} (hv : VarsBelow st N) : ∀ (k x : Nat), x < N → st.follow k x < N
  | 0, _, h => h
  | k + 1, x, h => by
    unfold St.follow
    split
    · next y hy => exact follow_lt hv k y (hv x y hy)
    · exact h

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem acp_lastVar_lt {st : St s} {N : Nat} (hv : VarsBelow st N) {x : Nat} (h : x < N) : st.lastVar x < N :=
  follow_lt hv _ x h

/-! ### The subterms of the rows are fit -/

/-- Every subterm is fit to enter a state of `N` slots. -/
def AllFit (N : Nat) (subs : List (Dag s)) : Prop := ∀ t ∈ subs, t.Fit N

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem repr_fit {st : St s} {N : Nat} (hv : VarsBelow st N) {d : Dag s} (hd : d.Fit N) : (repr st d).Fit N := by
  cases d with
  | var x => exact fit_var (acp_lastVar_lt hv (lt_of_fit_var hd))
  | _ => exact hd

theorem addOcc_fit {st : St s} {N : Nat} (hv : VarsBelow st N) {subs : List (Dag s)} {row : List Int}
    {d : Dag s} {m : Int} (hs : AllFit N subs) (hd : d.Fit N) : AllFit N (addOcc st subs row d m).1 := by
  rw [addOcc_eq]
  split
  · exact hs
  · intro t ht
    rcases List.mem_append.mp ht with h | h
    · exact hs t h
    · rw [List.mem_singleton.mp h]; exact repr_fit hv hd

theorem foldOcc_fit {st : St s} {N : Nat} (hv : VarsBelow st N) (m : Int) :
    ∀ (args : List (Dag s)) (acc : List (Dag s) × List Int), AllFit N acc.1 → (∀ a ∈ args, a.Fit N) →
      AllFit N (args.foldl (fun (acc : List (Dag s) × List Int) a => addOcc st acc.1 acc.2 a m) acc).1
  | [], _, h, _ => h
  | a :: as, acc, h, ha => by
    simp only [List.foldl_cons]
    exact foldOcc_fit hv m as _ (addOcc_fit hv h (ha a List.mem_cons_self))
      (fun b hb => ha b (List.mem_cons_of_mem _ hb))

theorem addArgs_fit {st : St s} {N : Nat} (hv : VarsBelow st N) (f : s.ACSym) (m : Int)
    (acc : List (Dag s) × List Int) (d : Dag s) (h : AllFit N acc.1) (hd : d.Fit N) :
    AllFit N (addArgs st f m acc d).1 := by
  unfold addArgs
  split
  · next g args =>
    split
    · exact foldOcc_fit hv m args acc h (fun a ha => fit_of_mem_ac hd ha)
    · exact addOcc_fit hv h hd
  · exact addOcc_fit hv h hd

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem killNew_sub : ∀ (n : Nat) (xs : List (Dag s)) (cs : List Int), ∀ t ∈ (killNew n xs cs).1, t ∈ xs
  | 0, xs, cs, t, ht => by
    simp only [killNew, List.mem_map, List.mem_filter] at ht
    obtain ⟨p, ⟨hp, _⟩, rfl⟩ := ht
    exact (List.of_mem_zip hp).1
  | n + 1, x :: xs, c :: cs, t, ht => by
    simp only [killNew, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (killNew_sub n xs cs t ht)
  | n + 1, [], _, t, ht => by simp [killNew] at ht
  | n + 1, _ :: _, [], t, ht => by simpa [killNew] using ht

theorem addUnif_fit {st : St s} {N : Nat} (hv : VarsBelow st N) (f : s.ACSym) (subs : List (Dag s))
    (rows : List (List Int)) (l rt : Dag s) (hs : AllFit N subs) (hl : l.Fit N) (hr : rt.Fit N) :
    AllFit N (addUnif st f subs rows l rt).1 := by
  have h1 := addArgs_fit hv f (-1) (subs, List.replicate subs.length 0) rt hs hr
  have h2 := addArgs_fit hv f 1 _ l h1 hl
  unfold addUnif
  dsimp only
  split <;> exact fun t ht => h2 t (killNew_sub _ _ _ t ht)

theorem collect_fit {st : St s} {N : Nat} (hv : VarsBelow st N) (f : s.ACSym) :
    ∀ (unifs : List (Dag s × Dag s)) (acc : List (Dag s) × List (List Int)), AllFit N acc.1 →
      (∀ p ∈ unifs, p.1.Fit N ∧ p.2.Fit N) →
      AllFit N (unifs.foldl (fun (acc : List (Dag s) × List (List Int)) (p : Dag s × Dag s) =>
        addUnif st f acc.1 acc.2 p.1 p.2) acc).1
  | [], _, h, _ => h
  | p :: ps, acc, h, hu => by
    simp only [List.foldl_cons]
    exact collect_fit hv f ps _
      (addUnif_fit hv f _ _ _ _ h (hu p List.mem_cons_self).1 (hu p List.mem_cons_self).2)
      (fun q hq => hu q (List.mem_cons_of_mem _ hq))

theorem unsolve_fit (f : s.ACSym) {N : Nat} :
    ∀ (k : Nat) (st : St s) (subs : List (Dag s)) (rows : List (List Int)), k ≤ st.vals.size → st.vals.size = N →
      (∀ i d, st.value i = some d → d.Fit N) → AllFit N subs → AllFit N (unsolve f k st subs rows).2.1
  | 0, _, _, _, _, _, _, h => h
  | k + 1, st, subs, rows, hk, hN, hb, h => by
    have hi : st.vals.size - (k + 1) < st.vals.size := by omega
    simp only [unsolve]
    split
    · next g args hv =>
      split
      · next e =>
        subst e
        have v1 := value_bind st hi none
        have hb1 : ∀ i d, (st.bind (st.vals.size - (k + 1)) none).value i = some d → d.Fit N := by
          intro i d hd
          rw [v1] at hd
          split at hd
          · cases hd
          · exact hb i d hd
        have hv1 : VarsBelow (st.bind (st.vals.size - (k + 1)) none) N := fun i y hy => lt_of_fit_var (hb1 i _ hy)
        have fitArgs := foldOcc_fit hv1 1 args (subs, List.replicate subs.length 0) h
          (fun a ha => fit_of_mem_ac (hb _ _ hv) ha)
        exact unsolve_fit g k _ _ _ (by rw [size_bind]; omega) (by rw [size_bind]; exact hN) hb1
          (addOcc_fit hv1 fitArgs (fit_var (x := st.vals.size - (k + 1)) (hN ▸ hi)))
      · exact unsolve_fit f k st subs rows (by omega) hN hb h
    · exact unsolve_fit f k st subs rows (by omega) hN hb h

/-! ### The witnesses -/

/-- Every subterm mentions only slots below `N`. -/
def AllBelow (N : Nat) (subs : List (Dag s)) : Prop := ∀ t ∈ subs, t.Below N

theorem mem_zipIdx_self {α : Type} (l : List α) {q : Nat} (hq : q < l.length) : (l[q], q) ∈ l.zipIdx :=
  List.mem_zipIdx_iff_getElem?.mpr (by simp [hq])

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
/-- What `witnesses` does: one witness per element, a reused variable
subterm that only its element assigns, once, or a fresh slot. -/
theorem witnesses_spec (subs : List (Dag s)) (sel : List (List Nat)) :
    ∀ (todo : List (List Nat)) (j : Nat) (st : St s) (W : St s × List (Dag s) × List Nat),
    witnesses subs sel todo j st = W →
    W.2.1.length = todo.length ∧ W.1.pending = st.pending ∧ st.vals.size ≤ W.1.vals.size ∧
    (∀ i, W.1.value i = st.value i) ∧ (∀ i, W.1.sortOf i = st.sortOf i) ∧
    (st.sorts.size = st.vals.size → W.1.sorts.size = W.1.vals.size) ∧
    (∀ w ∈ W.2.1, (∃ v, w = .var v) ∧ (w ∈ subs ∨ w.Below W.1.vals.size)) ∧
    (∀ i ∈ W.2.2, ∃ p, ∃ hp : p < todo.length, ∃ hw : p < W.2.1.length, ∃ hi : i < subs.length,
        W.2.1[p] = subs[i] ∧ todo[p].getD i 0 = 1 ∧ ∀ q (hq : q < sel.length), q ≠ j + p → sel[q].getD i 0 = 0) ∧
    (∀ (N : Nat) (ρ0 : Nat → Term s) (wt : List (Term s)), AllBelow N subs → N ≤ st.vals.size →
      wt.length = todo.length →
      (∀ p (hp : p < todo.length) (hw : p < wt.length) i (hi : i < subs.length), todo[p].getD i 0 = 1 →
        (∀ q (hq : q < sel.length), q ≠ j + p → sel[q].getD i 0 = 0) → EquivB (Dag.eval ρ0 subs[i]) wt[p]) →
      ∃ ρ', Agree st.vals.size ρ0 ρ' ∧
        ∀ p (h1 : p < W.2.1.length) (h2 : p < wt.length), EquivB (Dag.eval ρ' W.2.1[p]) wt[p])
  | [], j, st, W, hW => by
    simp only [witnesses] at hW
    subst hW
    refine ⟨rfl, rfl, Nat.le_refl _, fun _ => rfl, fun _ => rfl, id, fun w hw => (by cases hw),
      fun i hi => (by cases hi), fun N ρ0 wt _ _ _ _ => ⟨ρ0, fun _ _ => rfl, fun p h1 => (by simp at h1)⟩⟩
  | e :: rest, j, st, W, hW => by
    simp only [witnesses] at hW
    generalize hf : List.find? _ (List.zipIdx subs) = o at hW
    cases o with
    | some ti =>
      obtain ⟨t, i⟩ := ti
      have hp := List.find?_some hf
      have hm := List.mem_of_find?_eq_some hf
      obtain ⟨hi, ht⟩ := List.mem_zipIdx' hm
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at hp
      obtain ⟨⟨h1, hvar⟩, hall⟩ := hp
      have isVar : ∃ v, t = .var v := by
        cases t with
        | var v => exact ⟨v, rfl⟩
        | _ => simp at hvar
      have others : ∀ q (hq : q < sel.length), q ≠ j → sel[q].getD i 0 = 0 := by
        intro q hq ne
        rcases hall _ (mem_zipIdx_self sel hq) with h | h
        · exact absurd h ne
        · exact h
      dsimp only at hW
      obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ := witnesses_spec subs sel rest (j + 1) st _ rfl
      generalize witnesses subs sel rest (j + 1) st = R at l1 l2 l3 l4 l5 l6 l7 l8 l9 hW
      subst hW
      dsimp only
      refine ⟨by simp [l1], l2, l3, l4, l5, l6, fun w hw => ?_, fun i' hi' => ?_, ?_⟩
      · rcases List.mem_cons.mp hw with rfl | hw
        · exact ⟨isVar, .inl (by rw [ht]; exact List.getElem_mem hi)⟩
        · exact l7 w hw
      · rcases List.mem_append.mp hi' with h | h
        · rw [List.mem_singleton.mp h]
          exact ⟨0, by simp, by simp, hi, by simp [ht], h1,
            fun q hq ne => others q hq (by omega)⟩
        · obtain ⟨p, hp, hw, hi'', e1, e2, e3⟩ := l8 i' h
          exact ⟨p + 1, by simpa using hp, by simpa using hw, hi'', by simpa using e1, by simpa using e2,
            fun q hq ne => e3 q hq (by omega)⟩
      · intro N ρ0 wt hb hN hl hyp
        obtain ⟨u, us, rfl⟩ : ∃ u us, wt = u :: us := by
          cases wt with
          | nil => simp at hl
          | cons u us => exact ⟨u, us, rfl⟩
        obtain ⟨ρ', ag, hρ'⟩ := l9 N ρ0 us hb hN (by simpa using hl)
          (fun p hp hw i hi e1 e2 => by
            have := hyp (p + 1) (by simpa using hp) (by simpa using hw) i hi (by simpa using e1)
              (fun q hq ne => e2 q hq (by omega))
            simpa using this)
        refine ⟨ρ', ag, fun p k1 k2 => ?_⟩
        cases p with
        | zero =>
          simp only [List.getElem_cons_zero]
          have := hyp 0 (by simp) (by simp) i hi (by simpa using h1) (fun q hq ne => others q hq (by omega))
          rw [ht, acp_eval_agree ag (below_mono (hb _ (List.getElem_mem hi)) hN)]
          simpa using this
        | succ p =>
          simp only [List.getElem_cons_succ]
          exact hρ' p (by simpa using k1) (by simpa using k2)
    | none =>
      dsimp only at hW
      obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ := witnesses_spec subs sel rest (j + 1) st.fresh.1 _ rfl
      generalize witnesses subs sel rest (j + 1) st.fresh.1 = R at l1 l2 l3 l4 l5 l6 l7 l8 l9 hW
      subst hW
      dsimp only
      rw [size_fresh] at l3
      refine ⟨by simp [l1], l2, by omega, fun i => (l4 i).trans (value_fresh st i),
        fun i => (l5 i).trans (sortOf_fresh st i),
        fun h => l6 (by rw [sorts_size_fresh, size_fresh, h]), fun w hw => ?_, fun i' hi' => ?_, ?_⟩
      · rcases List.mem_cons.mp hw with rfl | hw
        · refine ⟨⟨_, rfl⟩, .inr fun x hx => ?_⟩
          simp only [Dag.vars, List.mem_singleton] at hx
          subst hx
          show st.vals.size < R.1.vals.size
          omega
        · exact l7 w hw
      · obtain ⟨p, hp, hw, hi'', e1, e2, e3⟩ := l8 i' (by simpa using hi')
        exact ⟨p + 1, by simpa using hp, by simpa using hw, hi'', by simpa using e1, by simpa using e2,
          fun q hq ne => e3 q hq (by omega)⟩
      · intro N ρ0 wt hb hN hl hyp
        obtain ⟨u, us, rfl⟩ : ∃ u us, wt = u :: us := by
          cases wt with
          | nil => simp at hl
          | cons u us => exact ⟨u, us, rfl⟩
        let ρ1 : Nat → Term s := fun x => if x = st.vals.size then u else ρ0 x
        have ag1 : Agree st.vals.size ρ0 ρ1 := fun x hx => by
          simp only [ρ1, show x ≠ st.vals.size by omega, ite_false]
        obtain ⟨ρ', ag, hρ'⟩ := l9 N ρ1 us hb (by rw [size_fresh]; omega) (by simpa using hl)
          (fun p hp hw i hi e1 e2 => by
            have := hyp (p + 1) (by simpa using hp) (by simpa using hw) i hi (by simpa using e1)
              (fun q hq ne => e2 q hq (by omega))
            rw [acp_eval_agree ag1 (below_mono (hb _ (List.getElem_mem hi)) hN)]
            simpa using this)
        rw [size_fresh] at ag
        refine ⟨ρ', agree_trans ag1 ag (by omega), fun p h1 h2 => ?_⟩
        cases p with
        | zero =>
          simp only [List.getElem_cons_zero, Dag.eval_var]
          show EquivB (ρ' st.vals.size) u
          rw [ag st.vals.size (by omega)]
          simp only [ρ1, ite_true]
          exact .refl _
        | succ p =>
          simp only [List.getElem_cons_succ]
          exact hρ' p (by simpa using h1) (by simpa using h2)

/-! ### What `assign` gives is fit -/

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] in
theorem flat_vars (f : s.ACSym) : ∀ (args : List (Dag s)), (∀ d ∈ args, ∃ v, d = .var v) → Dag.flat f args = args
  | [], _ => rfl
  | d :: rest, h => by
    obtain ⟨v, rfl⟩ := h d List.mem_cons_self
    simp only [Dag.flat]
    rw [flat_vars f rest fun d hd => h d (List.mem_cons_of_mem _ hd)]

theorem normAC_perm (so : Nat → Option SortId) (f : s.ACSym) (args : List (Dag s))
    (h : ∀ d ∈ args, ∃ v, d = .var v) : (Dag.normAC r so f args).Perm args := by
  unfold Dag.normAC
  rw [flat_vars f args h]
  exact List.mergeSort_perm _ _

theorem ac_fit (so : Nat → Option SortId) (f : s.ACSym) {N : Nat} (args : List (Dag s))
    (h : ∀ d ∈ args, (∃ v, d = .var v) ∧ d.Below N) (two : 2 ≤ args.length) :
    (Dag.ac f (Dag.normAC r so f args)).Fit N := by
  have perm := normAC_perm r so f args (fun d hd => (h d hd).1)
  refine ⟨?_, fun j hj => ?_⟩
  · simp only [Dag.Wf]
    refine ⟨by rw [perm.length_eq]; exact two, fun d hd => ?_⟩
    obtain ⟨v, rfl⟩ := (h d (perm.subset hd)).1
    simp [Dag.Wf]
  · rw [Dag.vars_ac] at hj
    obtain ⟨d, hd, hj⟩ := List.mem_flatMap.mp hj
    exact (h d (perm.subset hd)).2 j hj

theorem length_flatMap_replicate_ge {γ β : Type} (m : γ → Nat) (t : γ → β) :
    ∀ (P : List γ), (∀ p ∈ P, 1 ≤ m p) → P.length ≤ (P.flatMap fun p => List.replicate (m p) (t p)).length
  | [], _ => by simp
  | p :: ps, h => by
    have := length_flatMap_replicate_ge m t ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have hp := h p List.mem_cons_self
    simp only [List.flatMap_cons, List.length_append, List.length_replicate, List.length_cons]
    omega

/-- The witnesses are variables below `N`. -/
def WsOk (N : Nat) (ws : List (Dag s)) : Prop := ∀ w ∈ ws, (∃ v, w = .var v) ∧ w.Below N

theorem assign_fit (st : St s) (f : s.ACSym) (sel : List (List Nat)) (ws : List (Dag s)) (i : Nat) {N : Nat}
    (hws : WsOk N ws) (cov : ∃ q ∈ sel.zip ws, 0 < q.1.getD i 0) : (assign r st f sel ws i).1.Fit N := by
  have inPicks : ∀ q ∈ (sel.zip ws).filter (fun x => decide (0 < x.fst.getD i 0)),
      q.2 ∈ ws ∧ 0 < q.1.getD i 0 := by
    intro q hq
    obtain ⟨h1, h2⟩ := List.mem_filter.mp hq
    exact ⟨(List.of_mem_zip h1).2, by simpa using h2⟩
  obtain ⟨q0, hq0, pos0⟩ := cov
  have q0In : q0 ∈ (sel.zip ws).filter (fun x => decide (0 < x.fst.getD i 0)) :=
    List.mem_filter.mpr ⟨hq0, by simpa using pos0⟩
  unfold assign
  dsimp only
  generalize (sel.zip ws).filter (fun x : List Nat × Dag s => decide (0 < x.fst.getD i 0)) = P at inPicks q0In ⊢
  have picksOk : ∀ p ∈ P.map (fun (x : List Nat × Dag s) => (x.2, x.1.getD i 0)),
      ((∃ v, p.1 = .var v) ∧ p.1.Below N) ∧ 1 ≤ p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact ⟨hws q.2 (inPicks q hq).1, (inPicks q hq).2⟩
  split
  · next w hpick =>
    have := picksOk (w, 1) (by rw [hpick]; exact List.mem_cons_self)
    obtain ⟨⟨v, e⟩, hb⟩ := this.1
    simp only at e hb
    subst e
    exact ⟨by simp [Dag.Wf], hb⟩
  · next notOne =>
    generalize hQ : P.map (fun (x : List Nat × Dag s) => (x.2, x.1.getD i 0)) = Q at notOne picksOk ⊢
    have ne : Q ≠ [] := by
      intro h; rw [h] at hQ; rw [List.map_eq_nil_iff] at hQ; rw [hQ] at q0In; cases q0In
    have perm := normPicks_perm r st.sortOf f Q (fun p hp => (picksOk p hp).1.1)
    have two : 2 ≤ (Q.flatMap fun p => List.replicate p.2 p.1).length := by
      match Q, ne, notOne, picksOk with
      | [(w, m)], _, no, ok =>
        have := (ok (w, m) List.mem_cons_self).2
        have : m ≠ 1 := fun h => no w (by rw [h])
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_replicate]
        omega
      | x :: y :: rest, _, _, ok =>
        have hx := (ok x List.mem_cons_self).2
        have hy := (ok y (List.mem_cons_of_mem _ List.mem_cons_self)).2
        simp only [List.flatMap_cons, List.length_append, List.length_replicate]
        omega
    refine ⟨?_, fun j hj => ?_⟩
    · simp only [Dag.Wf]
      refine ⟨by rw [perm.length_eq]; exact two, fun d hd => ?_⟩
      obtain ⟨p, hp, hd⟩ := List.mem_flatMap.mp (perm.subset hd)
      rw [(List.mem_replicate.mp hd).2]
      obtain ⟨v, e⟩ := (picksOk p hp).1.1
      rw [e]; simp [Dag.Wf]
    · rw [Dag.vars_ac] at hj
      obtain ⟨d, hd, hj⟩ := List.mem_flatMap.mp hj
      obtain ⟨p, hp, hd⟩ := List.mem_flatMap.mp (perm.subset hd)
      rw [(List.mem_replicate.mp hd).2] at hj
      exact (picksOk p hp).1.2 j hj

/-! ### `buildFrom` -/

/-- One step of `buildFrom` on a subterm that is not reused. -/
def bStep (k : Nat) (f : s.ACSym) (sel : List (List Nat)) (ws : List (Dag s)) (st : St s) (t : Dag s) (i : Nat) :
    Res (St s) :=
  match t with
  | .var x =>
    if (st.value (st.lastVar x)).isNone && (assign r st f sel ws i).2 then
      .ok (st.bind (st.lastVar x) (some (assign r st f sel ws i).1))
    else csf r k st t (assign r st f sel ws i).1
  | _ => csf r k st t (assign r st f sel ws i).1

theorem buildFrom_cons (k : Nat) (f : s.ACSym) (sel : List (List Nat)) (ws : List (Dag s)) (reused : List Nat)
    (st : St s) (t : Dag s) (i : Nat) (rest : List (Dag s × Nat)) :
    buildFrom r k f sel ws reused st ((t, i) :: rest) =
      if i ∈ reused then buildFrom r k f sel ws reused st rest
      else (bStep r k f sel ws st t i).bind fun st => buildFrom r k f sel ws reused st rest := by
  simp only [buildFrom]
  split
  · rfl
  · cases t <;> rfl

theorem bStep_cases (k : Nat) (f : s.ACSym) (sel : List (List Nat)) (ws : List (Dag s)) (st : St s)
    (t : Dag s) (i : Nat) :
    bStep r k f sel ws st t i = csf r k st t (assign r st f sel ws i).1 ∨
      ∃ x, t = .var x ∧ (st.value (st.lastVar x)).isNone = true ∧
        bStep r k f sel ws st t i = .ok (st.bind (st.lastVar x) (some (assign r st f sel ws i).1)) := by
  unfold bStep
  cases t with
  | var x =>
    dsimp only
    split
    · next h =>
      simp only [Bool.and_eq_true] at h
      exact .inr ⟨x, rfl, h.1, rfl⟩
    · exact .inl rfl
  | _ => exact .inl rfl

theorem Res.bind_eq_ok {α β : Type} {x : Res α} {g : α → Res β} {b : β} (h : x.bind g = .ok b) :
    ∃ a, x = .ok a ∧ g a = .ok b := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | fail => cases h
  | gaveUp => cases h

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem bounded_bind {st : St s} (b : Bounded st) {i : Nat} (hi : i < st.vals.size) {d : Dag s}
    (hd : d.Fit st.vals.size) : Bounded (st.bind i (some d)) := by
  refine ⟨by rw [size_bind]; exact b.sizes, fun j d' h => ?_, fun p hp => ?_⟩
  · rw [size_bind]
    rw [value_bind st hi] at h
    split at h
    · cases h; exact hd
    · exact b.vals j d' h
  · rw [size_bind]; exact b.pend p hp

theorem bStep_ok (k : Nat) (f : s.ACSym) (sel : List (List Nat)) (ws : List (Dag s)) {st s1 : St s}
    {t : Dag s} {i : Nat} (b : Bounded st) (ht : t.Fit st.vals.size)
    (hd : (assign r st f sel ws i).1.Fit st.vals.size) (h : bStep r k f sel ws st t i = .ok s1) :
    Bounded s1 ∧ st.vals.size ≤ s1.vals.size ∧ (∀ j, s1.sortOf j = st.sortOf j) ∧
      ∀ ρ, Models s1 ρ → Models st ρ ∧ EquivB (Dag.eval ρ t) (Dag.eval ρ (assign r st f sel ws i).1) := by
  rcases bStep_cases r k f sel ws st t i with e | ⟨x, rfl, hn, e⟩
  · rw [e] at h
    obtain ⟨b1, g1⟩ := csf_wf r k b ht hd h
    exact ⟨b1, g1.1, csf_sorts r k h, fun ρ m => csf_sound r k b ht hd h m⟩
  · rw [e] at h
    cases h
    have hrv : st.lastVar x < st.vals.size := acp_lastVar_lt b.varsBelow (lt_of_fit_var ht)
    refine ⟨bounded_bind b hrv hd, by rw [size_bind]; exact Nat.le_refl _, fun j => rfl, fun ρ m => ?_⟩
    have vb := value_bind st hrv (some (assign r st f sel ws i).1)
    have none : st.value (st.lastVar x) = none := Option.isNone_iff_eq_none.mp hn
    have m0 : Models st ρ := by
      refine ⟨fun j d' hj => m.binds j d' ?_, fun p hp => m.pend p hp⟩
      rw [vb]
      split
      · next e => subst e; rw [none] at hj; cases hj
      · exact hj
    refine ⟨m0, ?_⟩
    have bnd := m.binds (st.lastVar x) (assign r st f sel ws i).1 (by rw [vb]; simp)
    rw [Dag.eval_var]
    exact (lastVar_equiv m0.chains x).trans bnd

theorem bStep_complete (k : Nat) (f : s.ACSym) (sel : List (List Nat)) (ws : List (Dag s)) {st : St s}
    {t : Dag s} {i : Nat} (b : Bounded st) (ht : t.Fit st.vals.size)
    (hd : (assign r st f sel ws i).1.Fit st.vals.size) {ρ : Nat → Term s} (m : Models st ρ)
    (e : EquivB (Dag.eval ρ t) (Dag.eval ρ (assign r st f sel ws i).1)) :
    Promise st ρ (bStep r k f sel ws st t i) := by
  rcases bStep_cases r k f sel ws st t i with h | ⟨x, rfl, hn, h⟩
  · rw [h]; exact csf_complete r k b ht hd m e
  · rw [h]
    have hrv : st.lastVar x < st.vals.size := acp_lastVar_lt b.varsBelow (lt_of_fit_var ht)
    have vb := value_bind st hrv (some (assign r st f sel ws i).1)
    refine ⟨ρ, fun _ _ => rfl, fun j d' hj => ?_, fun p hp => m.pend p hp⟩
    rw [vb] at hj
    split at hj
    · next eq =>
      subst eq
      cases hj
      rw [Dag.eval_var] at e
      exact (lastVar_equiv m.chains x).symm.trans e
    · exact m.binds j d' hj

/-- What `buildFrom` needs of its list: subterms fit, and every subterm that
is not reused gets something from the selection. -/
def BuildCtx (N : Nat) (sel : List (List Nat)) (ws : List (Dag s)) (reused : List Nat)
    (L : List (Dag s × Nat)) : Prop :=
  ∀ p ∈ L, p.1.Fit N ∧ (p.2 ∉ reused → ∃ q ∈ sel.zip ws, 0 < q.1.getD p.2 0)

theorem buildFrom_ok (k : Nat) (f : s.ACSym) (sel : List (List Nat)) (ws : List (Dag s)) (reused : List Nat)
    {N : Nat} (hws : WsOk N ws) :
    ∀ (L : List (Dag s × Nat)) (st st' : St s), Bounded st → N ≤ st.vals.size → BuildCtx N sel ws reused L →
      buildFrom r k f sel ws reused st L = .ok st' →
      Bounded st' ∧ st.vals.size ≤ st'.vals.size ∧ (∀ j, st'.sortOf j = st.sortOf j) ∧
        ∀ ρ, Models st' ρ → Models st ρ ∧
          ∀ p ∈ L, p.2 ∉ reused → EquivB (Dag.eval ρ p.1) (assignVal f ρ sel ws p.2)
  | [], st, st', b, _, _, h => by
    simp only [buildFrom] at h
    cases h
    exact ⟨b, Nat.le_refl _, fun _ => rfl, fun ρ m => ⟨m, fun p hp => by cases hp⟩⟩
  | (t, i) :: rest, st, st', b, hN, ctx, h => by
    rw [buildFrom_cons] at h
    have ctxRest : BuildCtx N sel ws reused rest := fun p hp => ctx p (List.mem_cons_of_mem _ hp)
    split at h
    · next hr =>
      obtain ⟨b', g', so', snd⟩ := buildFrom_ok k f sel ws reused hws rest st st' b hN ctxRest h
      refine ⟨b', g', so', fun ρ m => ⟨(snd ρ m).1, fun p hp hpr => ?_⟩⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · exact absurd hr hpr
      · exact (snd ρ m).2 p hp hpr
    · next hr =>
      obtain ⟨s1, h1, h2⟩ := Res.bind_eq_ok h
      have ht := ctx (t, i) List.mem_cons_self
      have hd := assign_fit r st f sel ws i hws (ht.2 hr)
      obtain ⟨b1, g1, so1, snd1⟩ := bStep_ok r k f sel ws b (fit_mono ht.1 hN) (fit_mono hd hN) h1
      obtain ⟨b', g', so', snd⟩ := buildFrom_ok k f sel ws reused hws rest s1 st' b1 (by omega) ctxRest h2
      refine ⟨b', by omega, fun j => (so' j).trans (so1 j), fun ρ m => ?_⟩
      obtain ⟨m1, eqs⟩ := snd ρ m
      obtain ⟨m0, e0⟩ := snd1 ρ m1
      refine ⟨m0, fun p hp hpr => ?_⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · exact e0.trans (eval_assign r st f ρ sel ws i)
      · exact eqs p hp hpr

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem promise_bind {st : St s} {ρ : Nat → Term s} {x : Res (St s)} {g : St s → Res (St s)}
    (hx : Promise st ρ x)
    (hg : ∀ s1 ρ1, x = .ok s1 → Agree st.vals.size ρ ρ1 → Models s1 ρ1 → st.vals.size ≤ s1.vals.size ∧
      Promise s1 ρ1 (g s1)) :
    Promise st ρ (x.bind g) := by
  cases x with
  | ok s1 =>
    obtain ⟨ρ1, ag, m1⟩ := hx
    obtain ⟨le, p⟩ := hg s1 ρ1 rfl ag m1
    show Promise st ρ (g s1)
    cases hgs : g s1 with
    | ok s2 =>
      rw [hgs] at p
      obtain ⟨ρ2, ag2, m2⟩ := p
      exact ⟨ρ2, agree_trans ag ag2 le, m2⟩
    | fail => rw [hgs] at p; exact p
    | gaveUp => trivial
  | fail => exact hx
  | gaveUp => trivial

theorem buildFrom_complete (k : Nat) (f : s.ACSym) (sel : List (List Nat)) (ws : List (Dag s)) (reused : List Nat)
    {N : Nat} (hws : WsOk N ws) (ρ' : Nat → Term s) :
    ∀ (L : List (Dag s × Nat)) (st : St s) (ρ : Nat → Term s), Bounded st → N ≤ st.vals.size →
      BuildCtx N sel ws reused L →
      (∀ p ∈ L, p.2 ∉ reused → EquivB (Dag.eval ρ' p.1) (assignVal f ρ' sel ws p.2)) →
      Agree N ρ' ρ → Models st ρ → Promise st ρ (buildFrom r k f sel ws reused st L)
  | [], st, ρ, _, _, _, _, _, m => by
    simp only [buildFrom]
    exact ⟨ρ, fun _ _ => rfl, m⟩
  | (t, i) :: rest, st, ρ, b, hN, ctx, eqs, ag, m => by
    rw [buildFrom_cons]
    have ctxRest : BuildCtx N sel ws reused rest := fun p hp => ctx p (List.mem_cons_of_mem _ hp)
    have eqsRest := fun p hp => eqs p (List.mem_cons_of_mem _ hp)
    split
    · exact buildFrom_complete k f sel ws reused hws ρ' rest st ρ b hN ctxRest eqsRest ag m
    · next hr =>
      have ht := ctx (t, i) List.mem_cons_self
      have hd := assign_fit r st f sel ws i hws (ht.2 hr)
      have e : EquivB (Dag.eval ρ t) (Dag.eval ρ (assign r st f sel ws i).1) := by
        rw [acp_eval_agree ag ht.1.2, acp_eval_agree ag hd.2]
        exact (eqs (t, i) List.mem_cons_self hr).trans (eval_assign r st f ρ' sel ws i).symm
      refine promise_bind (bStep_complete r k f sel ws b (fit_mono ht.1 hN) (fit_mono hd hN) m e)
        (fun s1 ρ1 h1 ag1 m1 => ?_)
      obtain ⟨b1, g1, _, _⟩ := bStep_ok r k f sel ws b (fit_mono ht.1 hN) (fit_mono hd hN) h1
      exact ⟨g1, buildFrom_complete k f sel ws reused hws ρ' rest s1 ρ1 b1 (by omega) ctxRest eqsRest
        (agree_trans ag ag1 hN) m1⟩

/-! ### `Res.concatMap` -/

theorem concatMap_ne_fail {α β : Type} (g : α → Res (List β)) : ∀ (l : List α), Res.concatMap g l ≠ .fail
  | [] => by simp [Res.concatMap]
  | a :: as => by
    simp only [Res.concatMap]
    split
    · simp
    · exact concatMap_ne_fail g as
    · have := concatMap_ne_fail g as
      cases h : Res.concatMap g as with
      | ok _ => simp [Res.map]
      | fail => exact absurd h this
      | gaveUp => simp [Res.map]

theorem concatMap_ok_mem {α β : Type} (g : α → Res (List β)) :
    ∀ (l : List α) (L : List β), Res.concatMap g l = .ok L → ∀ y ∈ L, ∃ a ∈ l, ∃ bs, g a = .ok bs ∧ y ∈ bs
  | [], L, h, y, hy => by simp only [Res.concatMap] at h; cases h; cases hy
  | a :: as, L, h, y, hy => by
    simp only [Res.concatMap] at h
    split at h
    · cases h
    · obtain ⟨b, hb, bs, e, m⟩ := concatMap_ok_mem g as L h y hy
      exact ⟨b, List.mem_cons_of_mem _ hb, bs, e, m⟩
    · next bs hga =>
      cases hr : Res.concatMap g as with
      | ok L' =>
        rw [hr] at h
        simp only [Res.map, Res.ok.injEq] at h
        subst h
        rcases List.mem_append.mp hy with hy | hy
        · exact ⟨a, List.mem_cons_self, bs, hga, hy⟩
        · obtain ⟨b, hb, cs, e, m⟩ := concatMap_ok_mem g as L' hr y hy
          exact ⟨b, List.mem_cons_of_mem _ hb, cs, e, m⟩
      | fail => rw [hr] at h; cases h
      | gaveUp => rw [hr] at h; cases h

theorem concatMap_gaveUp {α β : Type} (g : α → Res (List β)) {a : α} (ha : g a = .gaveUp) :
    ∀ (l : List α), a ∈ l → Res.concatMap g l = .gaveUp
  | [], h => by cases h
  | b :: bs, h => by
    simp only [Res.concatMap]
    rcases List.mem_cons.mp h with rfl | h
    · rw [ha]
    · split
      · rfl
      · exact concatMap_gaveUp g ha bs h
      · rw [concatMap_gaveUp g ha bs h]; rfl

theorem concatMap_ok_sub {α β : Type} (g : α → Res (List β)) {a : α} {bs : List β} (ha : g a = .ok bs) :
    ∀ (l : List α) (L : List β), a ∈ l → Res.concatMap g l = .ok L → ∀ y ∈ bs, y ∈ L
  | [], _, h, _ => by cases h
  | b :: rest, L, h, hc => by
    simp only [Res.concatMap] at hc
    intro y hy
    split at hc
    · cases hc
    · next hf =>
      rcases List.mem_cons.mp h with rfl | h
      · rw [ha] at hf; cases hf
      · exact concatMap_ok_sub g ha rest L h hc y hy
    · next cs hgb =>
      cases hr : Res.concatMap g rest with
      | ok L' =>
        rw [hr] at hc
        simp only [Res.map, Res.ok.injEq] at hc
        subst hc
        rcases List.mem_cons.mp h with rfl | h
        · rw [ha] at hgb; cases hgb; exact List.mem_append_left _ hy
        · exact List.mem_append_right _ (concatMap_ok_sub g ha rest L' h hr y hy)
      | fail => rw [hr] at hc; cases hc
      | gaveUp => rw [hr] at hc; cases hc

/-! ### Classification -/

theorem classify_fst (st : St s) (f : s.ACSym) (t : Dag s) :
    (classify st f t).1 = none ∨ (classify st f t).1 = some 1 := by
  have hs : ∀ d : Dag s, (single f d).1 = none ∨ (single f d).1 = some 1 := by
    intro d
    rcases single_spec f d with ⟨h, _⟩ | ⟨K, _, _, h⟩
    · exact .inl h
    · rw [h]; exact .inr rfl
  have hb : ∀ o, sortBound f o = none ∨ sortBound f o = some 1 := by
    intro o
    unfold sortBound
    split
    · exact .inl rfl
    · split
      · exact .inl rfl
      · exact .inr rfl
  unfold classify
  split
  · split
    · split
      · exact hs _
      · exact hb _
    · exact hb _
  · exact hs _

/-! ### Selections -/

theorem vec_getD {n : Nat} (v : Vector Nat n) {i : Nat} (hi : i < n) : v.toList.getD i 0 = v[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi)]
  simp

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem sel_cov {n : Nat} (T : List (Select.Elem n)) (ws : List (Dag s)) (hl : ws.length = T.length)
    (cov : ∀ i : Fin n, ∃ e ∈ T, 0 < e.vec[i]) {i : Nat} (hi : i < n) :
    ∃ q ∈ (T.map (·.vec.toList)).zip ws, 0 < q.1.getD i 0 := by
  obtain ⟨E, hE, pos⟩ := cov ⟨i, hi⟩
  have hm : E.vec.toList ∈ T.map (·.vec.toList) := List.mem_map_of_mem hE
  obtain ⟨y, hy⟩ := mem_zip_of_mem_left (B := ws) hm (by simp [hl])
  exact ⟨_, hy, by rw [vec_getD _ hi]; exact pos⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
/-- The rows hold for every factor class when every subterm counts the
factors of the witnesses as the elements, each a solution, say. -/
theorem rows_of_counts (f : s.ACSym) (ρ : Nat → Term s) (subs : List (Dag s)) (rows : List (List Int))
    (hrows : ∀ row ∈ rows, row.length ≤ subs.length) (Z : List (List Nat × Dag s))
    (hZ : ∀ q ∈ Z, ∀ row ∈ rows,
      ACBasis.Hilbert.isum (fun i : Fin subs.length => row.getD i 0 * (q.1.getD i 0 : Int)) = 0)
    (hcnt : ∀ a, ∀ i (hi : i < subs.length), cnt a (flatten f (Dag.eval ρ subs[i])) =
      (Z.map fun q => q.1.getD i 0 * cnt a (flatten f (Dag.eval ρ q.2))).sum) :
    ∀ a, RowsOk f ρ subs rows a := by
  intro a row hrow
  unfold rowVal
  rw [sum_zip_isum (fun t => (occ f ρ t a : Int)) subs row (hrows row hrow)]
  have hocc : (fun i : Fin subs.length => row.getD i 0 * (occ f ρ subs[i] a : Int)) =
      fun i : Fin subs.length => row.getD i 0 * (Z.map fun q => (q.1.getD i 0 : Int) * (cnt a (flatten f (Dag.eval ρ q.2)) : Int)).sum := by
    funext i
    congr 1
    unfold occ
    simp only [Fin.getElem_fin]
    rw [hcnt a i i.isLt, natCast_sum_map]
    simp only [Int.natCast_mul]
  rw [hocc, isum_swap (fun i : Fin subs.length => row.getD i 0) (fun q i => (q.1.getD i 0 : Int))
    (fun q => (cnt a (flatten f (Dag.eval ρ q.2)) : Int)) Z]
  rw [List.map_congr_left (l := Z) (g := fun _ => (0 : Int)) (fun q hq => by
    rw [hZ q hq row hrow, Int.mul_zero])]
  clear hZ hcnt hocc
  induction Z with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, List.sum_cons, ih, Int.add_zero]

theorem sel_getD {n : Nat} (T : List (Select.Elem n)) {p : Nat}
    (hp : p < (T.map (fun x : Select.Elem n => x.vec.toList)).length) {i : Nat} (hi : i < n) :
    (T.map (fun x : Select.Elem n => x.vec.toList))[p].getD i 0 = (T[p]'(by simpa using hp)).vec[i] := by
  rw [List.getElem_map, vec_getD _ hi]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem sel_setup {st1 : St s} (b1 : Bounded st1) {subs : List (Dag s)} (hsubs : AllFit st1.vals.size subs)
    {T : List (Select.Elem subs.length)} (cov : ∀ i : Fin subs.length, ∃ e ∈ T, 0 < e.vec[i])
    {W : St s × List (Dag s) × List Nat}
    (hW : witnesses subs (T.map (·.vec.toList)) (T.map (·.vec.toList)) 0 st1 = W) :
    Bounded W.1 ∧ WsOk W.1.vals.size W.2.1 ∧
      BuildCtx W.1.vals.size (T.map (·.vec.toList)) W.2.1 W.2.2 subs.zipIdx ∧
      st1.vals.size ≤ W.1.vals.size ∧ (∀ j, W.1.value j = st1.value j) ∧ (∀ j, W.1.sortOf j = st1.sortOf j) ∧
      W.1.pending = st1.pending ∧ W.2.1.length = T.length := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, -, -⟩ := witnesses_spec subs _ _ 0 st1 W hW
  have hl : W.2.1.length = T.length := by rw [l1]; simp
  refine ⟨⟨l6 b1.sizes, fun j d hd => ?_, fun p hp => ?_⟩, fun w hw => ?_, fun p hp => ?_, l3, l4, l5, l2, hl⟩
  · rw [l4] at hd; exact fit_mono (b1.vals j d hd) l3
  · rw [l2] at hp; obtain ⟨a1, a2, a3⟩ := b1.pend p hp; exact ⟨fit_mono a1 l3, fit_mono a2 l3, a3⟩
  · obtain ⟨hv, hin | hb⟩ := l7 w hw
    · exact ⟨hv, below_mono (hsubs w hin).2 l3⟩
    · exact ⟨hv, hb⟩
  · obtain ⟨t, i⟩ := p
    obtain ⟨hi, ht⟩ := List.mem_zipIdx' hp
    refine ⟨?_, fun _ => sel_cov T W.2.1 hl cov hi⟩
    rw [ht]
    exact fit_mono (hsubs _ (List.getElem_mem hi)) l3

theorem sel_sound (k : Nat) (f : s.ACSym) {st1 : St s} (b1 : Bounded st1) {subs : List (Dag s)}
    (hsubs : AllFit st1.vals.size subs) {rows : List (List Int)} (hrows : ∀ row ∈ rows, row.length ≤ subs.length)
    {T : List (Select.Elem subs.length)} (cov : ∀ i : Fin subs.length, ∃ e ∈ T, 0 < e.vec[i])
    (hsol : ∀ E ∈ T, ACBasis.Hilbert.Sol (colsOf subs.length rows) E.vec)
    {W : St s × List (Dag s) × List Nat}
    (hW : witnesses subs (T.map (·.vec.toList)) (T.map (·.vec.toList)) 0 st1 = W) {st' : St s}
    (h : buildFrom r k f (T.map (·.vec.toList)) W.2.1 W.2.2 W.1 subs.zipIdx = .ok st') :
    Bounded st' ∧ st1.vals.size ≤ st'.vals.size ∧ (∀ j, st'.sortOf j = st1.sortOf j) ∧
      ∀ ρ, Models st' ρ → Models st1 ρ ∧ ∀ a, RowsOk f ρ subs rows a := by
  obtain ⟨bW, hws, ctx, l3, l4, l5, l2, hl⟩ := sel_setup b1 hsubs cov hW
  obtain ⟨-, -, -, -, -, -, -, l8, -⟩ := witnesses_spec subs _ _ 0 st1 W hW
  obtain ⟨b', g', so', snd⟩ := buildFrom_ok r k f _ W.2.1 W.2.2 hws subs.zipIdx W.1 st' bW (Nat.le_refl _) ctx h
  refine ⟨b', by omega, fun j => (so' j).trans (l5 j), fun ρ m => ?_⟩
  obtain ⟨m2, eqs⟩ := snd ρ m
  refine ⟨⟨fun j d hd => m2.binds j d (by rw [l4]; exact hd), fun p hp => m2.pend p (by rw [l2]; exact hp)⟩, ?_⟩
  apply rows_of_counts f ρ subs rows hrows ((T.map (·.vec.toList)).zip W.2.1)
  · intro q hq row hrow
    obtain ⟨E, hE, he⟩ := List.mem_map.mp (List.of_mem_zip hq).1
    obtain ⟨ri, hri, rfl⟩ := List.mem_iff_getElem.mp hrow
    have := hsol E hE ⟨ri, hri⟩
    unfold ACBasis.Hilbert.res at this
    refine Eq.trans ?_ this
    congr 1
    funext i
    rw [← he, vec_getD _ i.isLt]
    simp [colsOf, List.getD_eq_getElem?_getD]
  · intro a i hi
    by_cases hr : i ∈ W.2.2
    · obtain ⟨p, hp, hw, hi', e1, e2, e3⟩ := l8 i hr
      have hpz : p < ((T.map (·.vec.toList)).zip W.2.1).length := by simp at hp ⊢; omega
      rw [sum_single_idx _ _ p hpz (fun q hq ne => by
        simp only [List.getElem_zip]
        rw [e3 q (by simp at hq ⊢; omega) (by omega), Nat.zero_mul])]
      simp only [List.getElem_zip]
      rw [e2, Nat.one_mul, e1]
    · rw [cnt_of_equiv f (eqs (subs[i], i) (mem_zipIdx_self subs hi) hr) a,
        cnt_assignVal f ρ _ W.2.1 i (sel_cov T W.2.1 hl cov hi) a]

theorem sel_complete (k : Nat) (f : s.ACSym) {st1 : St s} (b1 : Bounded st1) {subs : List (Dag s)}
    (hsubs : AllFit st1.vals.size subs)
    {T : List (Select.Elem subs.length)} (cov : ∀ i : Fin subs.length, ∃ e ∈ T, 0 < e.vec[i])
    {ρ : Nat → Term s} (m1 : Models st1 ρ) {wt : List (Term s)} (hwt : wt.length = T.length)
    (hfac : ∀ i : Fin subs.length, EquivB (Dag.eval ρ subs[i])
      (Dag.product f ((T.zip wt).flatMap fun p => List.replicate p.1.vec[i] p.2)))
    {W : St s × List (Dag s) × List Nat}
    (hW : witnesses subs (T.map (·.vec.toList)) (T.map (·.vec.toList)) 0 st1 = W) :
    Promise st1 ρ (buildFrom r k f (T.map (·.vec.toList)) W.2.1 W.2.2 W.1 subs.zipIdx) := by
  obtain ⟨bW, hws, ctx, l3, l4, l5, l2, hl⟩ := sel_setup b1 hsubs cov hW
  obtain ⟨-, -, -, -, -, -, -, -, l9⟩ := witnesses_spec subs _ _ 0 st1 W hW
  have hfac' : ∀ i (hi : i < subs.length), ∀ a, cnt a (flatten f (Dag.eval ρ subs[i])) =
      ((T.zip wt).map fun q => q.1.vec[i] * cnt a (flatten f q.2)).sum := by
    intro i hi a
    obtain ⟨E, hE, pos⟩ := cov ⟨i, hi⟩
    obtain ⟨y, hy⟩ := mem_zip_of_mem_left (B := wt) hE (by omega)
    have h := cnt_of_equiv f (hfac ⟨i, hi⟩) a
    rw [cnt_product_flatMap f (T.zip wt) (fun q => q.1.vec[(⟨i, hi⟩ : Fin subs.length)]) (fun q => q.2)
      (flatMap_replicate_ne hy pos) a] at h
    simpa using h
  have hsubsB : AllBelow st1.vals.size subs := fun t ht => (hsubs t ht).2
  obtain ⟨ρ', ag, hρ'⟩ := l9 st1.vals.size ρ wt hsubsB (Nat.le_refl _) (by simp [hwt])
    (fun p hp hw i hi e1 e2 => by
      apply equiv_of_cnt f
      intro a
      have hpT : p < T.length := by simpa using hp
      have hpz : p < (T.zip wt).length := by simp; omega
      rw [hfac' i hi a, sum_single_idx _ _ p hpz (fun q hq ne => by
        simp only [List.getElem_zip]
        have hqT : q < T.length := by simp at hq; omega
        have := e2 q (by simpa using hqT) (by omega)
        rw [sel_getD T (by simpa using hqT) hi] at this
        rw [this, Nat.zero_mul])]
      simp only [List.getElem_zip]
      rw [sel_getD T hp hi] at e1
      rw [e1, Nat.one_mul])
  have claim : ∀ i (hi : i < subs.length),
      EquivB (Dag.eval ρ' subs[i]) (assignVal f ρ' (T.map (·.vec.toList)) W.2.1 i) := by
    intro i hi
    apply equiv_of_cnt f
    intro a
    rw [acp_eval_agree ag (hsubs _ (List.getElem_mem hi)).2, hfac' i hi a,
      cnt_assignVal f ρ' _ W.2.1 i (sel_cov T W.2.1 hl cov hi) a]
    apply sum_zip_eq
    · simp [hwt, hl]
    · intro p h1 h2
      simp only [List.getElem_zip]
      have hpT : p < T.length := by simp at h1; omega
      rw [sel_getD T (by simpa using hpT) hi, cnt_of_equiv f (hρ' p (by omega) (by omega)) a]
  have mW : Models W.1 ρ' := by
    refine ⟨fun j d hd => ?_, fun p hp => ?_⟩
    · rw [l4] at hd
      have hj : j < st1.vals.size := by
        apply Classical.byContradiction
        intro c
        rw [value_ge st1 (by omega)] at hd
        cases hd
      rw [ag j hj, acp_eval_agree ag (b1.vals j d hd).2]
      exact m1.binds j d hd
    · rw [l2] at hp
      obtain ⟨a1, a2, -⟩ := b1.pend p hp
      rw [acp_eval_agree ag a1.2, acp_eval_agree ag a2.2]
      exact m1.pend p hp
  have pr := buildFrom_complete r k f _ W.2.1 W.2.2 hws ρ' subs.zipIdx W.1 ρ' bW (Nat.le_refl _) ctx
    (fun p hp _ => by
      obtain ⟨t, i⟩ := p
      obtain ⟨hi, ht⟩ := List.mem_zipIdx' hp
      show EquivB (Dag.eval ρ' t) _
      rw [ht]
      exact claim i hi)
    (fun _ _ => rfl) mW
  revert pr
  cases buildFrom r k f (T.map (·.vec.toList)) W.2.1 W.2.2 W.1 subs.zipIdx with
  | ok st' =>
    rintro ⟨ρ'', ag'', m''⟩
    exact ⟨ρ'', agree_trans ag ag'' l3, m''⟩
  | fail => exact id
  | gaveUp => exact id

/-! ### Assembling the subproblem -/

theorem Res.map_eq_ok {α β : Type} {g : α → β} {x : Res α} {b : β} (h : x.map g = .ok b) :
    ∃ a, x = .ok a ∧ g a = b := by
  cases x with
  | ok a => exact ⟨a, rfl, by simpa [Res.map] using h⟩
  | fail => cases h
  | gaveUp => cases h

/-- Some element of a successful list of results has a property; a failure
is impossible; giving up promises nothing. -/
def ResSome {β : Type} (P : β → Prop) : Res (List β) → Prop
  | .ok bs => ∃ y ∈ bs, P y
  | .fail => False
  | .gaveUp => True

theorem concatMap_promise {α β : Type} {g : α → Res (List β)} {l : List α} {L : List β}
    (hc : Res.concatMap g l = .ok L) {a : α} (ha : a ∈ l) {P : β → Prop} (hga : ResSome P (g a)) :
    ∃ y ∈ L, P y := by
  revert hga
  cases h : g a with
  | ok bs => rintro ⟨y, hy, py⟩; exact ⟨y, concatMap_ok_sub g h l L ha hc y hy, py⟩
  | fail => exact False.elim
  | gaveUp => intro _; rw [concatMap_gaveUp g h l ha] at hc; cases hc

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem promise_map {st : St s} {ρ : Nat → Term s} {x : Res (St s)} (h : Promise st ρ x) :
    ResSome (fun st' => ∃ ρ', Agree st.vals.size ρ ρ' ∧ Models st' ρ') (x.map fun st => [st]) := by
  cases x with
  | ok st' => exact ⟨st', List.mem_singleton_self _, h⟩
  | fail => exact h
  | gaveUp => trivial

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem rowsHold_of_ok (f : s.ACSym) (ρ : Nat → Term s) (subs : List (Dag s)) (rows : List (List Int))
    (hrows : ∀ row ∈ rows, row.length ≤ subs.length) (h : ∀ a, RowsOk f ρ subs rows a) :
    RowsHold f (fun i : Fin subs.length => Dag.eval ρ subs[i]) rows := by
  intro ri a
  have := h a rows[ri] (List.getElem_mem _)
  unfold rowVal at this
  rw [sum_zip_isum (fun t => (occ f ρ t a : Int)) subs rows[ri] (hrows _ (List.getElem_mem _))] at this
  exact this

/-- The constant valuation, which follows every chain of bindings. -/
def constVal : Nat → Term s := fun _ => Dag.dflt

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem chains_const (st : St s) : Chains st (constVal : Nat → Term s) := fun _ _ _ => .refl _

/-- What collecting the rows and unsolving the bindings keep of a bounded state. -/
theorem ac_front (f : s.ACSym) {st : St s} (b : Bounded st) {unifs : List (Dag s × Dag s)}
    (hu : ∀ p ∈ unifs, p.1.Fit st.vals.size ∧ p.2.Fit st.vals.size) {subs0 : List (Dag s)}
    {rows0 : List (List Int)}
    (hR : unifs.foldl (fun (acc : List (Dag s) × List (List Int)) (p : Dag s × Dag s) =>
        addUnif st f acc.1 acc.2 p.1 p.2) ([], []) = (subs0, rows0))
    {st1 : St s} {subs : List (Dag s)} {rows : List (List Int)}
    (hU : unsolve f st.vals.size st subs0 rows0 = (st1, subs, rows)) :
    Bounded st1 ∧ st1.vals.size = st.vals.size ∧ (∀ i, st1.sortOf i = st.sortOf i) ∧
      st1.pending = st.pending ∧ (∀ i y, st.value i = some (.var y) → st1.value i = some (.var y)) ∧
      AllFit st.vals.size subs ∧ (∀ row ∈ rows, row.length ≤ subs.length) ∧
      (∀ row ∈ rows0, row.length ≤ subs0.length) := by
  have hw : ∀ p ∈ unifs, p.1.Wf ∧ p.2.Wf := fun p hp => ⟨(hu p hp).1.1, (hu p hp).2.1⟩
  obtain ⟨-, lens0, -⟩ := collect_spec f st (chains_const st) unifs [] [] hw (fun _ h => by cases h)
  rw [hR] at lens0
  have fit0 := collect_fit b.varsBelow f unifs ([], []) (fun _ h => by cases h) hu
  rw [hR] at fit0
  have hvw : ∀ i d, st.value i = some d → d.Wf := fun i d h => (b.vals i d h).1
  have U := unsolve_spec f (ρ := constVal) st.vals.size st subs0 rows0 (Nat.le_refl _) lens0 hvw (chains_const st)
  have fitU := unsolve_fit f st.vals.size st subs0 rows0 (Nat.le_refl _) rfl b.vals fit0
  rw [hU] at U fitU
  obtain ⟨u1, u2, u3, u4, u5, -, u7, -⟩ := U
  have so : ∀ i, st1.sortOf i = st.sortOf i := fun i => by unfold St.sortOf; rw [u2]
  refine ⟨⟨by rw [u1, u2]; exact b.sizes, fun i d h => ?_, fun p hp => ?_⟩, u1, so, u3, u5, fitU, u7, lens0⟩
  · rw [u1]; exact b.vals i d (u4 i d h)
  · rw [u1]; rw [u3] at hp; exact b.pend p hp

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] in
theorem upper_at (st1 : St s) (f : s.ACSym) (subs : List (Dag s)) (i : Fin subs.length) :
    (Vector.ofFn fun i : Fin subs.length => ((subs.map (classify st1 f)).getD i (none, none)).1)[i] =
      (classify st1 f subs[i]).1 := by
  rw [Dioph.vget_ofFn]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem i.isLt]
  simp

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] in
theorem stable_at (st1 : St s) (f : s.ACSym) (subs : List (Dag s)) (i : Fin subs.length) :
    ((subs.map (classify st1 f)).map (·.2)).getD i none = (classify st1 f subs[i]).2 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem i.isLt]
  simp

theorem ac_pos (st1 : St s) (f : s.ACSym) (subs : List (Dag s)) :
    ∀ i : Fin subs.length,
      (Vector.ofFn fun i : Fin subs.length => ((subs.map (classify st1 f)).getD i (none, none)).1)[i] ≠ some 0 := by
  intro i
  rw [upper_at]
  rcases classify_fst st1 f subs[i] with h | h <;> rw [h] <;> simp

end Tamarin.MaudeUnify
