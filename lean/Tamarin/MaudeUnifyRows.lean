import Tamarin.MaudeUnifySolvedForm

/-!
# The rows of an AC subproblem

The Diophantine rows that `addUnif` and `unsolve` build hold for a valuation
exactly when the problems and the unsolved bindings they come from hold.
-/
namespace Tamarin.MaudeUnify
open Cancellation


variable {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

/-- Occurrences of a factor class in the value of a dag. -/
noncomputable def occ (f : s.ACSym) (ρ : Nat → Term s) (d : Dag s) (a : Class s) : Nat :=
  cnt a (flatten f (Dag.eval ρ d))

/-- The value of a row on the subterms, for one factor class. -/
noncomputable def rowVal (f : s.ACSym) (ρ : Nat → Term s) (subs : List (Dag s)) (row : List Int) (a : Class s) : Int :=
  ((subs.zip row).map fun p => p.2 * (occ f ρ p.1 a : Int)).sum

/-- The valuation follows the variable bindings of the state. -/
def Chains (st : St s) (ρ : Nat → Term s) : Prop :=
  ∀ x y, st.value x = some (.var y) → EquivB (ρ x) (ρ y)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem follow_equiv {st : St s} {ρ : Nat → Term s} (c : Chains st ρ) (k x : Nat) :
    EquivB (ρ x) (ρ (st.follow k x)) := by
  induction k generalizing x with
  | zero => exact .refl _
  | succ k ih =>
    unfold St.follow
    split
    · next y h => exact (c x y h).trans (ih y)
    · exact .refl _

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem lastVar_equiv {st : St s} {ρ : Nat → Term s} (c : Chains st ρ) (x : Nat) :
    EquivB (ρ x) (ρ (st.lastVar x)) := follow_equiv c _ x

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem Models.chains {st : St s} {ρ : Nat → Term s} (m : Models st ρ) : Chains st ρ := by
  intro x y h
  have := m.binds x _ h
  rwa [Dag.eval_var] at this

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem occ_equiv (f : s.ACSym) {ρ : Nat → Term s} {d e : Dag s} (h : EquivB (Dag.eval ρ d) (Dag.eval ρ e))
    (a : Class s) : occ f ρ d a = occ f ρ e a := by
  classical
  unfold occ
  rw [cnt_eq, cnt_eq]
  exact (flatten_equiv f h).count_eq a

/-! ### Sums over rows -/

theorem sum_zip_modify {α : Type} (w : α → Int) :
    ∀ (l : List α) (r : List Int) (i : Nat) (m : Int) (hi : i < l.length), r.length = l.length →
      ((l.zip (r.modify i (· + m))).map fun p => p.2 * w p.1).sum =
        ((l.zip r).map fun p => p.2 * w p.1).sum + m * w (l[i]'hi)
  | [], _, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | x :: xs, [], _, _, _, h => by simp at h
  | x :: xs, c :: cs, 0, m, _, _ => by
    simp only [List.modify_zero_cons, List.zip_cons_cons, List.map_cons, List.sum_cons,
      List.getElem_cons_zero]
    rw [Int.add_mul]; omega
  | x :: xs, c :: cs, i + 1, m, hi, h => by
    simp only [List.modify_succ_cons, List.zip_cons_cons, List.map_cons, List.sum_cons,
      List.getElem_cons_succ]
    rw [sum_zip_modify w xs cs i m (by simpa using hi) (by simpa using h)]
    omega

theorem sum_zip_append {α : Type} (w : α → Int) (l : List α) (r : List Int) (x : α) (m : Int)
    (h : r.length = l.length) :
    (((l ++ [x]).zip (r ++ [m])).map fun p => p.2 * w p.1).sum =
      ((l.zip r).map fun p => p.2 * w p.1).sum + m * w x := by
  rw [List.zip_append h.symm]
  simp

/-- A row is not changed by subterms after its end. -/
theorem sum_zip_extend {α : Type} (w : α → Int) (l more : List α) (r : List Int) (h : r.length ≤ l.length) :
    (((l ++ more).zip r).map fun p => p.2 * w p.1).sum = ((l.zip r).map fun p => p.2 * w p.1).sum := by
  induction l generalizing r with
  | nil => simp at h; subst h; simp
  | cons x xs ih =>
    cases r with
    | nil => simp
    | cons c cs =>
      simp only [List.cons_append, List.zip_cons_cons, List.map_cons, List.sum_cons]
      rw [ih cs (by simpa using h)]

/-- The subterm a dag stands for in a row: a variable by its representative. -/
def repr (st : St s) : Dag s → Dag s
  | .var x => .var (st.lastVar x)
  | d => d

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem occ_repr (f : s.ACSym) {st : St s} {ρ : Nat → Term s} (c : Chains st ρ) (d : Dag s) (a : Class s) :
    occ f ρ (repr st d) a = occ f ρ d a := by
  cases d with
  | var x =>
    apply occ_equiv
    show EquivB (Dag.eval ρ (.var (st.lastVar x))) (Dag.eval ρ (.var x))
    rw [Dag.eval_var, Dag.eval_var]
    exact (lastVar_equiv c x).symm
  | _ => rfl

theorem addOcc_eq (st : St s) (subs : List (Dag s)) (row : List Int) (d : Dag s) (m : Int) :
    addOcc st subs row d m =
      match subs.findIdx? (· = repr st d) with
      | some i => (subs, row.modify i (· + m))
      | none => (subs ++ [repr st d], row ++ [m]) := by
  unfold addOcc
  cases d <;> rfl

/-- Adding an occurrence keeps the row as long as the subterms and only appends subterms. -/
theorem addOcc_shape (st : St s) (subs : List (Dag s)) (row : List Int) (d : Dag s) (m : Int)
    (h : row.length = subs.length) :
    (addOcc st subs row d m).2.length = (addOcc st subs row d m).1.length ∧
      ∃ more, (addOcc st subs row d m).1 = subs ++ more := by
  rw [addOcc_eq]
  split
  · exact ⟨by simpa using h, [], by simp⟩
  · exact ⟨by simp [h], _, rfl⟩

/-- Adding an occurrence adds its multiplicity times the occurrences of the class. -/
theorem addOcc_val (f : s.ACSym) (st : St s) {ρ : Nat → Term s} (c : Chains st ρ) (subs : List (Dag s))
    (row : List Int) (d : Dag s) (m : Int) (h : row.length = subs.length) (a : Class s) :
    rowVal f ρ (addOcc st subs row d m).1 (addOcc st subs row d m).2 a =
      rowVal f ρ subs row a + m * occ f ρ d a := by
  rw [addOcc_eq]
  split
  · next i hi =>
    obtain ⟨lt, eq, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hi
    have eq' : subs[i] = repr st d := by simpa using eq
    unfold rowVal
    rw [sum_zip_modify (fun t => (occ f ρ t a : Int)) subs row i m lt h]
    simp only [eq', occ_repr f c]
  · unfold rowVal
    rw [sum_zip_append (fun t => (occ f ρ t a : Int)) subs row _ m h, occ_repr f c]

/-- Rows: lengths agree and only subterms are appended. -/
def Aligned (subs : List (Dag s)) (subs' : List (Dag s)) (row' : List Int) : Prop :=
  row'.length = subs'.length ∧ ∃ more, subs' = subs ++ more

theorem foldOcc_spec (f : s.ACSym) (st : St s) {ρ : Nat → Term s} (c : Chains st ρ) (m : Int) :
    ∀ (args : List (Dag s)) (subs : List (Dag s)) (row : List Int), row.length = subs.length →
      let res := args.foldl (fun (acc : List (Dag s) × List Int) a => addOcc st acc.1 acc.2 a m) (subs, row)
      Aligned subs res.1 res.2 ∧
        ∀ a, rowVal f ρ res.1 res.2 a = rowVal f ρ subs row a + m * ((args.map fun d => (occ f ρ d a : Int)).sum)
  | [], _, _, h => ⟨⟨h, [], by simp⟩, fun a => by simp⟩
  | d :: ds, subs, row, h => by
    simp only [List.foldl_cons]
    obtain ⟨hlen, more, hmore⟩ := addOcc_shape st subs row d m h
    obtain ⟨⟨hlen', more', hmore'⟩, val⟩ := foldOcc_spec f st c m ds _ _ hlen
    refine ⟨⟨hlen', more ++ more', by rw [hmore', hmore, List.append_assoc]⟩, fun a => ?_⟩
    rw [val a, addOcc_val f st c subs row d m h a]
    simp only [List.map_cons, List.sum_cons]
    rw [Int.mul_add]
    omega

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem killNew_spec (f : s.ACSym) (ρ : Nat → Term s) :
    ∀ (n : Nat) (xs : List (Dag s)) (cs : List Int), cs.length = xs.length → n ≤ xs.length →
      (killNew n xs cs).2.length = (killNew n xs cs).1.length ∧
      (killNew n xs cs).1.take n = xs.take n ∧ n ≤ (killNew n xs cs).1.length ∧
      ∀ a, rowVal f ρ (killNew n xs cs).1 (killNew n xs cs).2 a = rowVal f ρ xs cs a
  | 0, xs, cs, h, _ => by
    refine ⟨by simp [killNew], by simp, by simp, fun a => ?_⟩
    simp only [killNew, rowVal]
    generalize xs.zip cs = L
    induction L with
    | nil => rfl
    | cons p ps ih =>
      by_cases z : p.2 = 0
      · simp only [List.filter_cons, z, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
          ↓reduceIte, List.map_cons, List.sum_cons]
        rw [ih]; simp
      · simp only [List.filter_cons, z, ne_eq, not_false_eq_true, decide_true, ↓reduceIte,
          List.map_cons, List.zip_cons_cons, List.sum_cons]
        rw [ih]
  | n + 1, x :: xs, c :: cs, h, hn => by
    obtain ⟨l1, l2, l3, l4⟩ := killNew_spec f ρ n xs cs (by simpa using h) (by simpa using hn)
    refine ⟨by simp [killNew, l1], by simp [killNew, l2], by simp [killNew]; omega, fun a => ?_⟩
    simp only [killNew, rowVal, List.zip_cons_cons, List.map_cons, List.sum_cons]
    rw [show (((killNew n xs cs).1.zip (killNew n xs cs).2).map fun p => p.2 * (occ f ρ p.1 a : Int)).sum =
      ((xs.zip cs).map fun p => p.2 * (occ f ρ p.1 a : Int)).sum from l4 a]
  | n + 1, [], cs, h, hn => by simp at hn
  | n + 1, _ :: _, [], h, _ => by simp at h

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem rowVal_zero (f : s.ACSym) (ρ : Nat → Term s) (subs : List (Dag s)) (row : List Int)
    (h : ∀ c ∈ row, c = 0) (a : Class s) : rowVal f ρ subs row a = 0 := by
  unfold rowVal
  induction subs generalizing row with
  | nil => simp
  | cons x xs ih =>
    cases row with
    | nil => simp
    | cons c cs =>
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
      rw [h c List.mem_cons_self, ih cs fun d hd => h d (List.mem_cons_of_mem _ hd)]
      simp

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem rowVal_extend (f : s.ACSym) (ρ : Nat → Term s) (subs more : List (Dag s)) (row : List Int)
    (h : row.length ≤ subs.length) (a : Class s) :
    rowVal f ρ (subs ++ more) row a = rowVal f ρ subs row a :=
  sum_zip_extend (fun t => (occ f ρ t a : Int)) subs more row h

theorem natCast_sum_map {α : Type} (l : List α) (g : α → Nat) :
    ((l.map g).sum : Int) = (l.map fun x => (g x : Int)).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem cnt_ac (f : s.ACSym) (ρ : Nat → Term s) {args : List (Dag s)} (h : args ≠ []) (a : Class s) :
    (cnt a (flatten f (Dag.eval ρ (.ac f args))) : Int) = (args.map fun d => (occ f ρ d a : Int)).sum := by
  rw [Dag.eval_ac, flatten_product f (by simpa using h), List.flatMap_map, cnt_flatMap, natCast_sum_map]
  rfl

theorem addArgs_spec (f : s.ACSym) (st : St s) {ρ : Nat → Term s} (c : Chains st ρ) (m : Int)
    (subs : List (Dag s)) (row : List Int) (h : row.length = subs.length) (d : Dag s) (hd : d.Wf) :
    Aligned subs (addArgs st f m (subs, row) d).1 (addArgs st f m (subs, row) d).2 ∧
      ∀ a, rowVal f ρ (addArgs st f m (subs, row) d).1 (addArgs st f m (subs, row) d).2 a =
        rowVal f ρ subs row a + m * (cnt a (flatten f (Dag.eval ρ d)) : Int) := by
  have single : Aligned subs (addOcc st subs row d m).1 (addOcc st subs row d m).2 ∧
      ∀ a, rowVal f ρ (addOcc st subs row d m).1 (addOcc st subs row d m).2 a =
        rowVal f ρ subs row a + m * (cnt a (flatten f (Dag.eval ρ d)) : Int) := by
    obtain ⟨l1, more, pre⟩ := addOcc_shape st subs row d m h
    exact ⟨⟨l1, more, pre⟩, fun a => by rw [addOcc_val f st c subs row d m h a]; rfl⟩
  cases d with
  | ac g args =>
    by_cases e : g = f
    · subst e
      have ne : args ≠ [] := by
        simp only [Dag.Wf] at hd; intro e; rw [e] at hd; simp at hd
      obtain ⟨al, val⟩ := foldOcc_spec g st c m args subs row h
      simp only [addArgs, ite_true]
      exact ⟨al, fun a => by rw [val a, cnt_ac g ρ ne a]⟩
    · simp only [addArgs, e, ite_false]
      exact single
  | _ => exact single

theorem addUnif_spec (f : s.ACSym) (st : St s) {ρ : Nat → Term s} (c : Chains st ρ)
    (subs : List (Dag s)) (rows : List (List Int)) (l rt : Dag s) (hl : l.Wf) (hr : rt.Wf)
    (hrows : ∀ row ∈ rows, row.length ≤ subs.length) :
    (∃ more, (addUnif st f subs rows l rt).1 = subs ++ more) ∧
      (∀ row ∈ (addUnif st f subs rows l rt).2, row.length ≤ (addUnif st f subs rows l rt).1.length) ∧
      ∀ a, (∀ row ∈ (addUnif st f subs rows l rt).2, rowVal f ρ (addUnif st f subs rows l rt).1 row a = 0) ↔
        ((∀ row ∈ rows, rowVal f ρ subs row a = 0) ∧
          (cnt a (flatten f (Dag.eval ρ l)) : Int) = cnt a (flatten f (Dag.eval ρ rt))) := by
  have z0 : (List.replicate subs.length (0 : Int)).length = subs.length := by simp
  obtain ⟨⟨rlen, rmore, rpre⟩, rval⟩ := addArgs_spec f st c (-1) subs _ z0 rt hr
  generalize hR : addArgs st f (-1) (subs, List.replicate subs.length 0) rt = R at rlen rpre rval
  obtain ⟨⟨llen, lmore, lpre⟩, lval⟩ := addArgs_spec f st c 1 R.1 R.2 rlen l hl
  generalize hL : addArgs st f 1 (R.1, R.2) l = L at llen lpre lval
  have hL' : addArgs st f 1 R l = L := by rw [← hL]
  have nle : subs.length ≤ L.1.length := by rw [lpre, rpre]; simp
  obtain ⟨k1, k2, k3, k4⟩ := killNew_spec f ρ subs.length L.1 L.2 llen nle
  have tk : (killNew subs.length L.1 L.2).1.take subs.length = subs := by
    rw [k2, lpre, rpre]; simp
  have hmore : (killNew subs.length L.1 L.2).1 = subs ++ (killNew subs.length L.1 L.2).1.drop subs.length := by
    have := List.take_append_drop subs.length (killNew subs.length L.1 L.2).1
    rw [tk] at this
    exact this.symm
  generalize (killNew subs.length L.1 L.2).1.drop subs.length = more at hmore
  have newVal : ∀ a, rowVal f ρ (killNew subs.length L.1 L.2).1 (killNew subs.length L.1 L.2).2 a =
      (cnt a (flatten f (Dag.eval ρ l)) : Int) - cnt a (flatten f (Dag.eval ρ rt)) := by
    intro a
    rw [k4, lval a, rval a, rowVal_zero f ρ subs _ (fun c hc => (List.mem_replicate.mp hc).2) a]
    omega
  have oldVal : ∀ row ∈ rows, ∀ a, rowVal f ρ (killNew subs.length L.1 L.2).1 row a = rowVal f ρ subs row a := by
    intro row hrow a
    rw [hmore]
    exact rowVal_extend f ρ subs more row (hrows row hrow) a
  have oldLen : ∀ row ∈ rows, row.length ≤ (killNew subs.length L.1 L.2).1.length := by
    intro row hrow
    have := hrows row hrow
    omega
  have unf : addUnif st f subs rows l rt =
      if (killNew subs.length L.1 L.2).2.any (· ≠ 0)
      then ((killNew subs.length L.1 L.2).1, rows ++ [(killNew subs.length L.1 L.2).2])
      else ((killNew subs.length L.1 L.2).1, rows) := by
    simp only [addUnif, hR, hL']
  rw [unf]
  split
  · refine ⟨⟨more, hmore⟩, fun row hrow => ?_, fun a => ?_⟩
    · rcases List.mem_append.mp hrow with h | h
      · exact oldLen row h
      · rw [List.mem_singleton.mp h]; exact Nat.le_of_eq k1
    · constructor
      · intro all
        refine ⟨fun row hrow => ?_, ?_⟩
        · rw [← oldVal row hrow a]; exact all row (List.mem_append_left _ hrow)
        · have := all _ (List.mem_append_right _ List.mem_cons_self)
          rw [newVal] at this
          omega
      · rintro ⟨old, eq⟩ row hrow
        rcases List.mem_append.mp hrow with h | h
        · rw [oldVal row h]; exact old row h
        · rw [List.mem_singleton.mp h, newVal]; omega
  · next none =>
    refine ⟨⟨more, hmore⟩, oldLen, fun a => ?_⟩
    have zero : ∀ c ∈ (killNew subs.length L.1 L.2).2, c = 0 := by
      intro c hc
      apply Classical.byContradiction
      intro ne
      exact none (List.any_eq_true.mpr ⟨c, hc, by simpa using ne⟩)
    have eq := newVal a
    rw [rowVal_zero f ρ _ _ zero a] at eq
    constructor
    · intro all
      exact ⟨fun row hrow => by rw [← oldVal row hrow a]; exact all row hrow, by omega⟩
    · rintro ⟨old, _⟩ row hrow
      rw [oldVal row hrow]; exact old row hrow

/-- The rows hold for one factor class. -/
def RowsOk (f : s.ACSym) (ρ : Nat → Term s) (subs : List (Dag s)) (rows : List (List Int)) (a : Class s) : Prop :=
  ∀ row ∈ rows, rowVal f ρ subs row a = 0

/-- The two sides have the same factors of a class. -/
def SameCnt (f : s.ACSym) (ρ : Nat → Term s) (l rt : Dag s) (a : Class s) : Prop :=
  (cnt a (flatten f (Dag.eval ρ l)) : Int) = cnt a (flatten f (Dag.eval ρ rt))

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem equiv_iff_sameCnt (f : s.ACSym) (ρ : Nat → Term s) (l rt : Dag s) :
    EquivB (Dag.eval ρ l) (Dag.eval ρ rt) ↔ ∀ a, SameCnt f ρ l rt a := by
  classical
  constructor
  · intro h a
    unfold SameCnt
    rw [cnt_eq, cnt_eq, (flatten_equiv f h).count_eq a]
  · intro h
    apply equiv_of_flatten_perm f
    apply perm_of_cnt
    intro a
    exact Int.ofNat.inj (h a)

theorem collect_spec (f : s.ACSym) (st : St s) {ρ : Nat → Term s} (c : Chains st ρ) :
    ∀ (unifs : List (Dag s × Dag s)) (subs : List (Dag s)) (rows : List (List Int)),
      (∀ p ∈ unifs, p.1.Wf ∧ p.2.Wf) → (∀ row ∈ rows, row.length ≤ subs.length) →
      let R := unifs.foldl (fun (acc : List (Dag s) × List (List Int)) (p : Dag s × Dag s) =>
        addUnif st f acc.1 acc.2 p.1 p.2) (subs, rows)
      (∃ more, R.1 = subs ++ more) ∧ (∀ row ∈ R.2, row.length ≤ R.1.length) ∧
        ∀ a, RowsOk f ρ R.1 R.2 a ↔ (RowsOk f ρ subs rows a ∧ ∀ p ∈ unifs, SameCnt f ρ p.1 p.2 a)
  | [], subs, rows, _, hr => ⟨⟨[], by simp⟩, hr, fun a => by simp [RowsOk]⟩
  | p :: ps, subs, rows, hw, hr => by
    simp only [List.foldl_cons]
    obtain ⟨⟨more, pre⟩, lens, iff⟩ := addUnif_spec f st c subs rows p.1 p.2 (hw p List.mem_cons_self).1
      (hw p List.mem_cons_self).2 hr
    obtain ⟨⟨more', pre'⟩, lens', iff'⟩ := collect_spec f st c ps _ _
      (fun q hq => hw q (List.mem_cons_of_mem _ hq)) lens
    refine ⟨⟨more ++ more', by rw [pre', pre, List.append_assoc]⟩, lens', fun a => ?_⟩
    rw [iff' a]
    unfold RowsOk
    rw [iff a]
    simp only [List.mem_cons, forall_eq_or_imp, SameCnt]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem value_bind (st : St s) {i : Nat} (hi : i < st.vals.size) (v : Option (Dag s)) (j : Nat) :
    (st.bind i v).value j = if j = i then v else st.value j := by
  unfold St.bind St.value
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases e : j = i
  · subst e; simp [hi]
  · simp [Ne.symm e, e]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem size_bind (st : St s) (i : Nat) (v : Option (Dag s)) : (st.bind i v).vals.size = st.vals.size := by
  simp [St.bind]


theorem unsolve_spec (f : s.ACSym) {ρ : Nat → Term s} :
    ∀ (k : Nat) (st : St s) (subs : List (Dag s)) (rows : List (List Int)),
      k ≤ st.vals.size → (∀ row ∈ rows, row.length ≤ subs.length) → (∀ i d, st.value i = some d → d.Wf) →
      Chains st ρ →
      let U := unsolve f k st subs rows
      U.1.vals.size = st.vals.size ∧ U.1.sorts = st.sorts ∧ U.1.pending = st.pending ∧
        (∀ i d, U.1.value i = some d → st.value i = some d) ∧
        (∀ i y, st.value i = some (.var y) → U.1.value i = some (.var y)) ∧
        (∃ more, U.2.1 = subs ++ more) ∧ (∀ row ∈ U.2.2, row.length ≤ U.2.1.length) ∧
        (((∀ a, RowsOk f ρ U.2.1 U.2.2 a) ∧ Binds U.1 ρ) ↔ ((∀ a, RowsOk f ρ subs rows a) ∧ Binds st ρ))
  | 0, st, subs, rows, _, hr, _, _ =>
    ⟨rfl, rfl, rfl, fun _ _ h => h, fun _ _ h => h, ⟨[], by simp [unsolve]⟩, hr, Iff.rfl⟩
  | k + 1, st, subs, rows, hk, hr, hw, c => by
    have hi : st.vals.size - (k + 1) < st.vals.size := by omega
    simp only [unsolve]
    split
    · next g args hv =>
      split
      · next e =>
        subst e
        let st1 := st.bind (st.vals.size - (k + 1)) none
        have v1 := value_bind st hi none
        have c1 : Chains st1 ρ := by
          intro x y h
          rw [v1] at h
          split at h
          · cases h
          · exact c x y h
        have w1 : ∀ i d, st1.value i = some d → d.Wf := by
          intro i d h
          rw [v1] at h
          split at h
          · cases h
          · exact hw i d h
        have z0 : (List.replicate subs.length (0 : Int)).length = subs.length := by simp
        have ne : args ≠ [] := by
          have := hw _ _ hv
          simp only [Dag.Wf] at this
          intro e; rw [e] at this; simp at this
        obtain ⟨al, val⟩ := foldOcc_spec g st1 c1 1 args subs _ z0
        generalize hA : args.foldl (fun (acc : List (Dag s) × List Int) a => addOcc st1 acc.1 acc.2 a 1)
          (subs, List.replicate subs.length 0) = A at al val
        obtain ⟨alen, amore, apre⟩ := al
        obtain ⟨blen, bmore, bpre⟩ := addOcc_shape st1 A.1 A.2 (.var (st.vals.size - (k + 1))) (-1) alen
        have bval := addOcc_val g st1 c1 A.1 A.2 (.var (st.vals.size - (k + 1))) (-1) alen
        generalize hB : addOcc st1 A.1 A.2 (.var (st.vals.size - (k + 1))) (-1) = B at blen bpre bval
        have hr1 : ∀ row ∈ rows ++ [B.2], row.length ≤ B.1.length := by
          intro row hrow
          rcases List.mem_append.mp hrow with h | h
          · have := hr row h; rw [bpre, apre]; simp; omega
          · rw [List.mem_singleton.mp h, blen]; exact Nat.le_refl _
        have size1 : st1.vals.size = st.vals.size := size_bind _ _ _
        obtain ⟨s1, s2, s3, s4, s5, ⟨more, pre⟩, lens, iff⟩ :=
          unsolve_spec g k st1 B.1 (rows ++ [B.2]) (by omega) hr1 w1 c1
        refine ⟨s1.trans size1, s2, s3, fun i d h => ?_, fun i y h => ?_, ⟨amore ++ bmore ++ more, ?_⟩, lens, ?_⟩
        · have := s4 i d h
          rw [v1] at this
          split at this
          · cases this
          · exact this
        · apply s5
          rw [v1]
          split
          · next e => subst e; rw [hv] at h; cases h
          · exact h
        · rw [pre, bpre, apre]; simp
        · rw [iff]
          have rowB : ∀ a, rowVal g ρ B.1 B.2 a =
              (cnt a (flatten g (Dag.eval ρ (.ac g args))) : Int) - cnt a (flatten g (ρ (st.vals.size - (k + 1)))) := by
            intro a
            rw [bval a, val a, rowVal_zero g ρ subs _ (fun c hc => (List.mem_replicate.mp hc).2) a, cnt_ac g ρ ne a]
            simp [occ, Dag.eval_var]
            omega
          have oldRows : ∀ a, ∀ row ∈ rows, rowVal g ρ B.1 row a = rowVal g ρ subs row a := by
            intro a row hrow
            rw [bpre, apre, List.append_assoc]
            exact rowVal_extend g ρ subs _ row (hr row hrow) a
          have bindsIff : Binds st ρ ↔ Binds st1 ρ ∧
              EquivB (ρ (st.vals.size - (k + 1))) (Dag.eval ρ (.ac g args)) := by
            constructor
            · intro b
              refine ⟨fun i d h => ?_, b _ _ hv⟩
              rw [v1] at h
              split at h
              · cases h
              · exact b i d h
            · rintro ⟨b1, bi⟩ i d h
              by_cases e : i = st.vals.size - (k + 1)
              · subst e; rw [hv] at h; cases h; exact bi
              · apply b1 i d
                rw [v1, ite_eq_right e]
                exact h
          have eqv := equiv_iff_sameCnt g ρ (.var (st.vals.size - (k + 1))) (.ac g args)
          rw [Dag.eval_var] at eqv
          rw [bindsIff, eqv]
          simp only [RowsOk, List.mem_append, List.mem_singleton, SameCnt, Dag.eval_var]
          constructor
          · rintro ⟨rowsOk, b1⟩
            refine ⟨fun a row hrow => ?_, b1, fun a => ?_⟩
            · rw [← oldRows a row hrow]; exact rowsOk a row (.inl hrow)
            · have := rowsOk a B.2 (.inr rfl); rw [rowB] at this; omega
          · rintro ⟨rowsOk, b1, same⟩
            refine ⟨fun a row hrow => ?_, b1⟩
            rcases hrow with h | h
            · rw [oldRows a row h]; exact rowsOk a row h
            · subst h; rw [rowB]; have := same a; omega
      · exact unsolve_spec f k st subs rows (by omega) hr hw c
    · exact unsolve_spec f k st subs rows (by omega) hr hw c

end Tamarin.MaudeUnify
