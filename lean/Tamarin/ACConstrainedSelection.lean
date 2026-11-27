import Tamarin.ACCoverage
import Tamarin.Interrupt

/-! Covering selections under per-coordinate constraints. A capped coordinate
admits one selected generator of multiplicity one, and a rejected generator is
never selected. The traversal abandons a prefix as soon as it violates either
condition, so excluded selections are never built. -/
namespace Tamarin.Homogeneous.Constrained
open ACBasis Coverage

variable {α : Type} {n : Nat} [Interrupt]

/-- No capped coordinate lies in the support of two chosen items. -/
def apart (caps : BitVec n) (mask : α → BitVec n) : BitVec n → List α → Bool
  | _, [] => true
  | seen, y :: ys => (seen &&& mask y &&& caps == 0#n) && apart caps mask (seen ||| mask y) ys

/-- The covering traversal restricted to admitted items and capped coordinates.
The visiting order is that of `Coverage.enumerate`. -/
def enumerate [Interrupt] (full caps : BitVec n) (bad : α → Bool) :
    Plan α n → BitVec n → List (List α)
  | .done, covered => if covered = full then [[]] else []
  | .step x support remaining tail, covered =>
    if covered ||| remaining = full then
      enumerate full caps bad tail covered ++
        (if !bad x && (covered &&& support &&& caps == 0#n) then
          (enumerate full caps bad tail (covered ||| support)).map (x :: ·) else [])
    else []

/-- `enumerate` as it is compiled: every node of the traversal asks first. -/
private def enumerateAsking [Interrupt] (full caps : BitVec n) (bad : α → Bool) :
    Plan α n → BitVec n → List (List α)
  | .done, covered => if covered = full then [[]] else []
  | .step x support remaining tail, covered =>
    if Interrupt.poll () then []
    else if covered ||| remaining = full then
      enumerateAsking full caps bad tail covered ++
        (if !bad x && (covered &&& support &&& caps == 0#n) then
          Interrupt.map (x :: ·) (enumerateAsking full caps bad tail (covered ||| support)) else [])
    else []

omit [Interrupt] in
@[csimp] private theorem enumerate_eq_asking : @enumerate = @enumerateAsking := by
  funext α n i full caps bad plan covered
  induction plan generalizing covered with
  | done => rfl
  | step x support remaining tail ih => simp [enumerate, enumerateAsking, Interrupt.quiet, ih]

theorem enumerate_eq (full caps : BitVec n) (bad : α → Bool) (mask : α → BitVec n)
    (xs : List α) (seen : BitVec n) :
    enumerate full caps bad (prepare mask xs) seen =
      (Coverage.enumerate full (prepare mask xs) seen).filter
        (fun ys => ys.all (fun y => !bad y) && apart caps mask seen ys) := by
  induction xs generalizing seen with
  | nil =>
    simp only [prepare, enumerate, Coverage.enumerate]
    split <;> simp [apart]
  | cons x xs ih =>
    simp only [prepare, enumerate, Coverage.enumerate]
    split
    · rw [List.filter_append, List.filter_map, ih, ih]
      congr 1
      cases hb : bad x
      · cases hc : (seen &&& mask x &&& caps == 0#n)
        · simp [Function.comp_def, apart, hb, hc]
        · simp [Function.comp_def, apart, hb, hc]
      · simp [Function.comp_def, hb]
    · rfl

omit [Interrupt] in
private theorem le_sum (xs : List Nat) (m : Nat) (hm : m ∈ xs) : m ≤ xs.sum := by
  induction xs with
  | nil => cases hm
  | cons a xs ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · simp
    · simp only [List.sum_cons]; have := ih hm; omega

/-- Every listed selection keeps the order of the items. -/
theorem enumerate_sublist (full caps : BitVec n) (bad : α → Bool) (mask : α → BitVec n)
    (xs : List α) (seen : BitVec n) {ys : List α}
    (h : ys ∈ enumerate full caps bad (prepare mask xs) seen) : ys.Sublist xs := by
  induction xs generalizing seen ys with
  | nil =>
    simp only [prepare, enumerate] at h
    split at h
    · obtain rfl := List.mem_singleton.mp h
      exact .slnil
    · cases h
  | cons x xs ih =>
    simp only [prepare, enumerate] at h
    split at h
    · rcases List.mem_append.mp h with h | h
      · exact .cons _ (ih _ h)
      · split at h
        · obtain ⟨tail, ht, rfl⟩ := List.mem_map.mp h
          exact .cons_cons _ (ih _ ht)
        · cases h
    · cases h

omit [Interrupt] in
/-- A selection that is not apart uses some capped coordinate twice. -/
theorem crowded (caps : BitVec n) (mask : α → BitVec n) (weight : α → Fin n → Nat)
    (positive : ∀ x (i : Fin n), (mask x).getLsbD i = true → 0 < weight x i)
    (seen : BitVec n) (ys : List α) (h : apart caps mask seen ys = false) :
    ∃ i : Fin n, caps.getLsbD i = true ∧
      ((seen.getLsbD i = true ∧ ∃ y ∈ ys, 0 < weight y i) ∨
        2 ≤ (ys.map (fun y => weight y i)).sum) := by
  induction ys generalizing seen with
  | nil => simp [apart] at h
  | cons y ys ih =>
    simp only [apart, Bool.and_eq_false_iff] at h
    rcases h with h | h
    · have ne : seen &&& mask y &&& caps ≠ 0#n := by simpa using h
      have bit : ∃ i : Fin n, (seen &&& mask y &&& caps).getLsbD i = true := by
        apply Classical.byContradiction
        intro none
        apply ne
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have := fun hb => none ⟨⟨i,hi⟩,hb⟩
        simpa using this
      obtain ⟨i,hi⟩ := bit
      simp only [BitVec.getLsbD_and, Bool.and_eq_true] at hi
      exact ⟨i,hi.2,.inl ⟨hi.1.1,y,List.mem_cons_self,positive y i hi.1.2⟩⟩
    · obtain ⟨i,hc,hit⟩ := ih _ h
      refine ⟨i,hc,?_⟩
      rcases hit with ⟨hs,z,hz,pz⟩ | two
      · simp only [BitVec.getLsbD_or, Bool.or_eq_true] at hs
        rcases hs with hs | hs
        · exact .inl ⟨hs,z,List.mem_cons_of_mem _ hz,pz⟩
        · have py := positive y i hs
          have le : weight z i ≤ (ys.map (fun y => weight y i)).sum :=
            le_sum _ _ (List.mem_map_of_mem hz)
          right
          simp only [List.map_cons, List.sum_cons]
          omega
      · right
        simp only [List.map_cons, List.sum_cons]
        omega

/-! A search whose pruning does not depend on the order of the items. Before
each choice the items that meet a capped coordinate already covered are
dropped. A coordinate that no remaining item covers closes the branch, and a
coordinate that exactly one remaining item covers selects that item. A choice
is made only on an item that meets a capped coordinate. -/
section Search
variable [DecidableEq α]

/-- The coordinates met by some item, and those met by two. -/
def summary (mask : α → BitVec n) : List α → BitVec n → BitVec n → BitVec n × BitVec n
  | [], once, twice => (once, twice)
  | x :: xs, once, twice => summary mask xs (once ||| mask x) (twice ||| (once &&& mask x))

/-- The selections of `enumerate` without rejected items, each in some order.
With no fuel left the remaining items are enumerated in their given order. -/
def search [Interrupt] (full caps : BitVec n) (mask : α → BitVec n) :
    Nat → List α → BitVec n → List (List α)
  | 0, xs, covered => enumerate full caps (fun _ => false) (prepare mask xs) covered
  | fuel + 1, xs, covered =>
    let xs := xs.filter fun x => covered &&& mask x &&& caps == 0#n
    let both := summary mask xs 0#n 0#n
    if covered ||| both.1 = full then
      let forced := both.1 &&& ~~~both.2 &&& ~~~covered
      match xs.find? (fun x => mask x &&& forced != 0#n) with
      | some g =>
        (search full caps mask fuel (xs.filter (· != g)) (covered ||| mask g)).map (g :: ·)
      | none =>
        match xs.find? (fun x => mask x &&& caps != 0#n) with
        | some g =>
          let rest := xs.filter (· != g)
          search full caps mask fuel rest covered ++
            (search full caps mask fuel rest (covered ||| mask g)).map (g :: ·)
        | none => enumerate full caps (fun _ => false) (prepare mask xs) covered
    else []

/-- `search` as it is compiled: every node of the search asks first. -/
private def searchAsking [Interrupt] (full caps : BitVec n) (mask : α → BitVec n) :
    Nat → List α → BitVec n → List (List α)
  | 0, xs, covered => enumerate full caps (fun _ => false) (prepare mask xs) covered
  | fuel + 1, xs, covered =>
    if Interrupt.poll () then [] else
    let xs := xs.filter fun x => covered &&& mask x &&& caps == 0#n
    let both := summary mask xs 0#n 0#n
    if covered ||| both.1 = full then
      let forced := both.1 &&& ~~~both.2 &&& ~~~covered
      match xs.find? (fun x => mask x &&& forced != 0#n) with
      | some g =>
        Interrupt.map (g :: ·) (searchAsking full caps mask fuel (xs.filter (· != g)) (covered ||| mask g))
      | none =>
        match xs.find? (fun x => mask x &&& caps != 0#n) with
        | some g =>
          let rest := xs.filter (· != g)
          searchAsking full caps mask fuel rest covered ++
            Interrupt.map (g :: ·) (searchAsking full caps mask fuel rest (covered ||| mask g))
        | none => enumerate full caps (fun _ => false) (prepare mask xs) covered
    else []

omit [Interrupt] in
@[csimp] private theorem search_eq_asking : @search = @searchAsking := by
  funext α n d i full caps mask fuel xs covered
  induction fuel generalizing xs covered with
  | zero => rfl
  | succ fuel ih => simp [search, searchAsking, Interrupt.quiet, ih]

omit [DecidableEq α] in
omit [Interrupt] in
private theorem exists_bit {v : BitVec n} (h : v ≠ 0#n) : ∃ i : Fin n, v.getLsbD i = true := by
  apply Classical.byContradiction
  intro none
  apply h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have := fun hb => none ⟨⟨i,hi⟩,hb⟩
  simpa using this

omit [DecidableEq α] in
omit [Interrupt] in
private theorem zero_of_bits {v : BitVec n} (h : ∀ i : Fin n, v.getLsbD i = false) : v = 0#n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simpa using h ⟨i,hi⟩

omit [DecidableEq α] in
omit [Interrupt] in
private theorem full_iff (v : BitVec n) :
    v = BitVec.allOnes n ↔ ∀ i : Fin n, v.getLsbD i = true := by
  constructor
  · rintro rfl i
    simp
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simpa [hi] using h ⟨i, hi⟩

omit [DecidableEq α] in
omit [Interrupt] in
private theorem available_bit (mask : α → BitVec n) (xs : List α) (i : Fin n) :
    (prepare mask xs).available.getLsbD i = true ↔ ∃ x ∈ xs, (mask x).getLsbD i = true := by
  induction xs with
  | nil => simp [prepare, Plan.available]
  | cons x xs ih =>
    change ((mask x ||| (prepare mask xs).available).getLsbD i = true) ↔ _
    simp only [BitVec.getLsbD_or, Bool.or_eq_true, ih, List.mem_cons, exists_eq_or_imp]

/-- A selection of items of `xs` that covers every coordinate together with
`covered` and meets no capped coordinate twice. -/
structure Valid (caps : BitVec n) (mask : α → BitVec n) (xs : List α) (covered : BitVec n)
    (zs : List α) : Prop where
  inside : ∀ z ∈ zs, z ∈ xs
  clear : ∀ z ∈ zs, covered &&& mask z &&& caps = 0#n
  apart : ∀ a ∈ zs, ∀ b ∈ zs, a ≠ b → mask a &&& mask b &&& caps = 0#n
  covers : ∀ i : Fin n, covered.getLsbD i = true ∨ ∃ z ∈ zs, (mask z).getLsbD i = true

omit [DecidableEq α] in
omit [Interrupt] in
private theorem Valid.mono {caps : BitVec n} {mask : α → BitVec n} {xs xs' covered zs}
    (h : Valid caps mask xs covered zs) (sub : ∀ z ∈ zs, z ∈ xs') :
    Valid caps mask xs' covered zs := ⟨sub, h.clear, h.apart, h.covers⟩

omit [Interrupt] in
private theorem Valid.take {caps : BitVec n} {mask : α → BitVec n} {xs xs' covered zs} {g : α}
    (h : Valid caps mask xs covered zs) (hg : g ∈ zs) (sub : ∀ z ∈ zs, z ≠ g → z ∈ xs') :
    Valid caps mask xs' (covered ||| mask g) (zs.filter (· != g)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨hz, ne⟩ := List.mem_filter.mp hz
    exact sub z hz (by simpa using ne)
  · intro z hz
    obtain ⟨hz, ne⟩ := List.mem_filter.mp hz
    have ne : z ≠ g := by simpa using ne
    apply zero_of_bits
    intro i
    have a := congrArg (·.getLsbD i) (h.clear z hz)
    have b := congrArg (·.getLsbD i) (h.apart g hg z hz (Ne.symm ne))
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at a b
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
    cases hc : covered.getLsbD i <;> cases hm : (mask g).getLsbD i <;>
      cases hz : (mask z).getLsbD i <;> cases hk : caps.getLsbD i <;> simp_all
  · intro a ha b hb ne
    exact h.apart a (List.mem_filter.mp ha).1 b (List.mem_filter.mp hb).1 ne
  · intro i
    rcases h.covers i with c | ⟨z, hz, bit⟩
    · exact .inl (by simp [c])
    · by_cases same : z = g
      · exact .inl (by simp [← same, bit])
      · exact .inr ⟨z, List.mem_filter.mpr ⟨hz, by simpa using same⟩, bit⟩

omit [Interrupt] in
private theorem take_members {zs ys : List α} {g : α} (hg : g ∈ zs)
    (same : ∀ x, x ∈ ys ↔ x ∈ zs.filter (· != g)) : ∀ x, x ∈ g :: ys ↔ x ∈ zs := by
  intro x
  rw [List.mem_cons, same, List.mem_filter]
  constructor
  · rintro (rfl | ⟨h, -⟩)
    · exact hg
    · exact h
  · intro h
    by_cases e : x = g
    · exact .inl e
    · exact .inr ⟨h, by simpa using e⟩

/-- Every valid selection is listed by the ordered traversal. -/
theorem enumerate_complete (caps : BitVec n) (mask : α → BitVec n) (xs : List α)
    (covered : BitVec n) (zs : List α) (h : Valid caps mask xs covered zs) :
    ∃ ys ∈ enumerate (BitVec.allOnes n) caps (fun _ => false) (prepare mask xs) covered,
      ∀ x, x ∈ ys ↔ x ∈ zs := by
  induction xs generalizing covered zs with
  | nil =>
    have empty : zs = [] := List.eq_nil_iff_forall_not_mem.mpr fun z hz => by
      cases h.inside z hz
    subst empty
    have all : covered = BitVec.allOnes n := (full_iff _).mpr fun i => by
      simpa using h.covers i
    exact ⟨[], by simp [prepare, enumerate, all], fun _ => Iff.rfl⟩
  | cons x xs ih =>
    have possible : covered ||| (mask x ||| (prepare mask xs).available) = BitVec.allOnes n := by
      apply (full_iff _).mpr
      intro i
      simp only [BitVec.getLsbD_or, Bool.or_eq_true, available_bit]
      rcases h.covers i with c | ⟨z, hz, bit⟩
      · exact .inl c
      · rcases List.mem_cons.mp (h.inside z hz) with rfl | tail
        · exact .inr (.inl bit)
        · exact .inr (.inr ⟨z, tail, bit⟩)
    simp only [prepare, enumerate, possible, ↓reduceIte]
    by_cases hx : x ∈ zs
    · have next := h.take hx (xs' := xs) fun z hz ne =>
        (List.mem_cons.mp (h.inside z hz)).resolve_left ne
      obtain ⟨ys, hy, same⟩ := ih _ _ next
      have free : (covered &&& mask x &&& caps == 0#n) = true := by simpa using h.clear x hx
      refine ⟨x :: ys, ?_, take_members hx same⟩
      simp only [Bool.not_false, Bool.true_and, free, ↓reduceIte]
      exact List.mem_append_right _ (List.mem_map_of_mem hy)
    · have next := h.mono (xs' := xs) fun z hz =>
        (List.mem_cons.mp (h.inside z hz)).resolve_left fun e => hx (e ▸ hz)
      obtain ⟨ys, hy, same⟩ := ih _ _ next
      exact ⟨ys, List.mem_append_left _ hy, same⟩

omit [DecidableEq α] in
/-- Every selection listed by the ordered traversal covers all coordinates. -/
theorem enumerate_covers (caps : BitVec n) (bad : α → Bool) (mask : α → BitVec n) (xs : List α)
    (covered : BitVec n) {ys : List α}
    (h : ys ∈ enumerate (BitVec.allOnes n) caps bad (prepare mask xs) covered) (i : Fin n) :
    covered.getLsbD i = true ∨ ∃ y ∈ ys, (mask y).getLsbD i = true := by
  induction xs generalizing covered ys with
  | nil =>
    simp only [prepare, enumerate] at h
    split at h
    next all => exact .inl ((full_iff _).mp all i)
    next => cases h
  | cons x xs ih =>
    simp only [prepare, enumerate] at h
    split at h
    · rcases List.mem_append.mp h with h | h
      · exact ih _ h
      · split at h
        · obtain ⟨tail, ht, rfl⟩ := List.mem_map.mp h
          rcases ih _ ht with c | ⟨y, hy, bit⟩
          · simp only [BitVec.getLsbD_or, Bool.or_eq_true] at c
            rcases c with c | c
            · exact .inl c
            · exact .inr ⟨x, List.mem_cons_self, c⟩
          · exact .inr ⟨y, List.mem_cons_of_mem _ hy, bit⟩
        · cases h
    · cases h

omit [DecidableEq α] in
omit [Interrupt] in
private theorem summary_once (mask : α → BitVec n) (xs : List α) (once twice : BitVec n)
    (i : Fin n) : (summary mask xs once twice).1.getLsbD i = true ↔
      once.getLsbD i = true ∨ ∃ x ∈ xs, (mask x).getLsbD i = true := by
  induction xs generalizing once twice with
  | nil => simp [summary]
  | cons x xs ih =>
    simp only [summary, ih, BitVec.getLsbD_or, Bool.or_eq_true, List.mem_cons, exists_eq_or_imp,
      or_assoc]

omit [DecidableEq α] in
omit [Interrupt] in
private theorem summary_twice (mask : α → BitVec n) (xs : List α) (once twice : BitVec n)
    (i : Fin n) :
    (twice.getLsbD i = true → (summary mask xs once twice).2.getLsbD i = true) ∧
    (once.getLsbD i = true → ∀ x ∈ xs, (mask x).getLsbD i = true →
      (summary mask xs once twice).2.getLsbD i = true) ∧
    (∀ a ∈ xs, ∀ b ∈ xs, a ≠ b → (mask a).getLsbD i = true → (mask b).getLsbD i = true →
      (summary mask xs once twice).2.getLsbD i = true) := by
  induction xs generalizing once twice with
  | nil => simp [summary]
  | cons x xs ih =>
    obtain ⟨keep, seen, pair⟩ := ih (once ||| mask x) (twice ||| (once &&& mask x))
    simp only [summary]
    refine ⟨fun t => keep (by simp [t]), ?_, ?_⟩
    · intro o y hy bit
      rcases List.mem_cons.mp hy with rfl | hy
      · exact keep (by simp [o, bit])
      · exact seen (by simp [o]) y hy bit
    · intro a ha b hb ne ba bb
      rcases List.mem_cons.mp ha with rfl | ta <;> rcases List.mem_cons.mp hb with rfl | tb
      · exact (ne rfl).elim
      · exact seen (by simp [ba]) b tb bb
      · exact seen (by simp [bb]) a ta ba
      · exact pair a ta b tb ne ba bb

/-- Every valid selection is listed, in some order. -/
theorem search_complete (caps : BitVec n) (mask : α → BitVec n) (fuel : Nat) (xs : List α)
    (covered : BitVec n) (zs : List α) (h : Valid caps mask xs covered zs) :
    ∃ ys ∈ search (BitVec.allOnes n) caps mask fuel xs covered, ∀ x, x ∈ ys ↔ x ∈ zs := by
  induction fuel generalizing xs covered zs with
  | zero => exact enumerate_complete caps mask xs covered zs h
  | succ fuel ih =>
    simp only [search]
    generalize hl : xs.filter (fun x => covered &&& mask x &&& caps == 0#n) = live
    have h : Valid caps mask live covered zs := h.mono fun z hz => by
      rw [← hl]
      exact List.mem_filter.mpr ⟨h.inside z hz, by simpa using h.clear z hz⟩
    have possible : covered ||| (summary mask live 0#n 0#n).1 = BitVec.allOnes n := by
      apply (full_iff _).mpr
      intro i
      simp only [BitVec.getLsbD_or, Bool.or_eq_true, summary_once]
      rcases h.covers i with c | ⟨z, hz, bit⟩
      · exact .inl c
      · exact .inr (.inr ⟨z, h.inside z hz, bit⟩)
    simp only [possible, ↓reduceIte]
    have included (g : α) (hg : g ∈ zs) :
        ∃ ys ∈ (search (BitVec.allOnes n) caps mask fuel (live.filter (· != g))
          (covered ||| mask g)).map (g :: ·), ∀ x, x ∈ ys ↔ x ∈ zs := by
      have next := h.take hg (xs' := live.filter (· != g)) fun z hz ne =>
        List.mem_filter.mpr ⟨h.inside z hz, by simpa using ne⟩
      obtain ⟨ys, hy, same⟩ := ih _ _ _ next
      exact ⟨g :: ys, List.mem_map_of_mem hy, take_members hg same⟩
    split
    next g found =>
      apply included
      have hg := List.mem_of_find?_eq_some found
      have ne := List.find?_some found
      obtain ⟨i, bit⟩ := exists_bit (v := mask g &&& ((summary mask live 0#n 0#n).1 &&&
        ~~~(summary mask live 0#n 0#n).2 &&& ~~~covered)) (by simpa using ne)
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, Fin.is_lt, decide_true, Bool.true_and,
        Bool.and_eq_true, Bool.not_eq_true'] at bit
      obtain ⟨mg, ⟨-, single⟩, open_⟩ := bit
      rcases h.covers i with c | ⟨z, hz, mz⟩
      · rw [c] at open_; cases open_
      · by_cases same : z = g
        · exact same ▸ hz
        · have two := (summary_twice mask live 0#n 0#n i).2.2 z (h.inside z hz) g hg same mz mg
          rw [two] at single; cases single
    next =>
      split
      next g _ =>
        by_cases hg : g ∈ zs
        · obtain ⟨ys, hy, same⟩ := included g hg
          exact ⟨ys, List.mem_append_right _ hy, same⟩
        · have next := h.mono (xs' := live.filter (· != g)) fun z hz =>
            List.mem_filter.mpr ⟨h.inside z hz, by
              have : z ≠ g := fun e => hg (e ▸ hz)
              simpa using this⟩
          obtain ⟨ys, hy, same⟩ := ih _ _ _ next
          exact ⟨ys, List.mem_append_left _ hy, same⟩
      next => exact enumerate_complete caps mask live covered zs h

/-- Every listed selection covers all coordinates. -/
theorem search_covers (caps : BitVec n) (mask : α → BitVec n) (fuel : Nat) (xs : List α)
    (covered : BitVec n) {ys : List α}
    (h : ys ∈ search (BitVec.allOnes n) caps mask fuel xs covered) (i : Fin n) :
    covered.getLsbD i = true ∨ ∃ y ∈ ys, (mask y).getLsbD i = true := by
  induction fuel generalizing xs covered ys with
  | zero => exact enumerate_covers caps _ mask xs covered h i
  | succ fuel ih =>
    simp only [search] at h
    have included {g : α} {rest : List α} {ys : List α}
        (h : ys ∈ (search (BitVec.allOnes n) caps mask fuel rest (covered ||| mask g)).map (g :: ·)) :
        covered.getLsbD i = true ∨ ∃ y ∈ ys, (mask y).getLsbD i = true := by
      obtain ⟨tail, ht, rfl⟩ := List.mem_map.mp h
      rcases ih _ _ ht with c | ⟨y, hy, bit⟩
      · simp only [BitVec.getLsbD_or, Bool.or_eq_true] at c
        rcases c with c | c
        · exact .inl c
        · exact .inr ⟨g, List.mem_cons_self, c⟩
      · exact .inr ⟨y, List.mem_cons_of_mem _ hy, bit⟩
    split at h
    · split at h
      · exact included h
      · split at h
        · rcases List.mem_append.mp h with h | h
          · exact ih _ _ h
          · exact included h
        · exact enumerate_covers caps _ mask _ covered h i
    · cases h

end Search

omit [Interrupt] in
/-- Valid selections are exactly those the constrained filter keeps. -/
theorem valid_of_apart (caps : BitVec n) (mask : α → BitVec n) (seen : BitVec n) (ys : List α)
    (distinct : ys.Nodup) (h : apart caps mask seen ys = true) :
    (∀ z ∈ ys, seen &&& mask z &&& caps = 0#n) ∧
      ∀ a ∈ ys, ∀ b ∈ ys, a ≠ b → mask a &&& mask b &&& caps = 0#n := by
  have weaken (a b c : BitVec n) (z : (a ||| b) &&& c &&& caps = 0#n) :
      a &&& c &&& caps = 0#n ∧ b &&& c &&& caps = 0#n := by
    constructor <;>
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have bit := congrArg (·.getLsbD i) z
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_zero] at bit ⊢
      cases ha : a.getLsbD i <;> cases hb : b.getLsbD i <;> cases hc : c.getLsbD i <;>
        cases hk : caps.getLsbD i <;> simp_all
  induction ys generalizing seen with
  | nil => simp
  | cons y ys ih =>
    simp only [apart, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨clear, tail⟩ := ih _ (List.nodup_cons.mp distinct).2 h.2
    refine ⟨?_, ?_⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact h.1
      · exact (weaken _ _ _ (clear z hz)).1
    · intro a ha b hb ne
      rcases List.mem_cons.mp ha with rfl | ta <;> rcases List.mem_cons.mp hb with rfl | tb
      · exact (ne rfl).elim
      · exact (weaken _ _ _ (clear b tb)).2
      · have := (weaken _ _ _ (clear a ta)).2
        rw [BitVec.and_comm (mask a)]
        exact this
      · exact tail a ta b tb ne


end Constrained

variable [Interrupt]

open ACBasis in
/-- Covering selections that avoid every rejected generator and select at most
one generator at each capped coordinate. Each selection lists its generators in
increasing order. The order of the selections depends on the constraints. -/
def constrainedSelections {n} (gs : List (Vec n)) (caps : BitVec n)
    (bad : Fin gs.length → Bool) : List (List (Fin gs.length)) :=
  let masks := Vector.ofFn fun j : Fin gs.length => Coverage.support (gs.get j)
  let all := List.finRange gs.length
  let admitted := all.filter fun j => !bad j
  if caps = 0#n then
    Constrained.enumerate (BitVec.allOnes n) caps (fun _ => false)
      (Coverage.prepare (fun j => masks[j]) admitted) 0#n
  else
    Interrupt.map (fun ys => all.filter (ys.contains ·))
      (Constrained.search (BitVec.allOnes n) caps (fun j => masks[j]) admitted.length admitted 0#n)

omit [Interrupt] in
private theorem filter_members {α : Type} [DecidableEq α] {l all : List α} (sub : l.Sublist all)
    (distinct : all.Nodup) : all.filter (l.contains ·) = l := by
  induction sub with
  | slnil => rfl
  | @cons l all a sub ih =>
    obtain ⟨fresh, rest⟩ := List.nodup_cons.mp distinct
    have out : l.contains a = false := by
      simpa using fun h => fresh (sub.subset h)
    rw [List.filter_cons, out]
    exact ih rest
  | @cons_cons l all a sub ih =>
    obtain ⟨fresh, rest⟩ := List.nodup_cons.mp distinct
    rw [List.filter_cons]
    simp only [List.contains_cons, BEq.rfl, Bool.true_or, ↓reduceIte]
    congr 1
    refine Eq.trans (List.filter_congr fun x hx => ?_) (ih rest)
    have ne : (x == a) = false := by
      have : x ≠ a := fun e => fresh (e ▸ hx)
      simpa using this
    simp [ne]

open ACBasis in
theorem constrainedSelections_covering {n} (gs : List (Vec n)) (caps : BitVec n)
    (bad : Fin gs.length → Bool) {js : List (Fin gs.length)}
    (mem : js ∈ constrainedSelections gs caps bad) : js ∈ selections gs := by
  have covering (ys : List (Fin gs.length)) (sub : ys.Sublist (List.finRange gs.length))
      (all : ∀ i : Fin n, (0#n).getLsbD i = true ∨ ∃ y ∈ ys,
        ((Vector.ofFn fun j : Fin gs.length => Coverage.support (gs.get j))[y]).getLsbD i = true) :
      ys ∈ selections gs := by
    refine List.mem_filter.mpr ⟨(FlatMatchSearch.mem_sublists _ _).mpr sub, ?_⟩
    simp only [covers, decide_eq_true_eq]
    intro i
    rcases all i with c | ⟨y, mem, bit⟩
    · simp at c
    · refine ⟨y, mem, ?_⟩
      simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta] at bit
      rw [Coverage.support_bit] at bit
      exact of_decide_eq_true bit
  unfold constrainedSelections at mem
  dsimp only at mem
  split at mem
  · exact covering js ((Constrained.enumerate_sublist _ _ _ _ _ _ mem).trans List.filter_sublist)
      (Constrained.enumerate_covers caps _ _ _ _ mem)
  · obtain ⟨ys, hy, rfl⟩ := List.mem_map.mp mem
    apply covering _ List.filter_sublist
    intro i
    rcases Constrained.search_covers caps _ _ _ _ hy i with c | ⟨y, mem, bit⟩
    · exact .inl c
    · exact .inr ⟨y, List.mem_filter.mpr ⟨List.mem_finRange y, by simpa using mem⟩, bit⟩

open ACBasis in
/-- A covering selection missing from the constrained family contains a
rejected generator or covers a capped coordinate with total multiplicity two. -/
theorem constrainedSelections_missing {n} (gs : List (Vec n)) (caps : BitVec n)
    (bad : Fin gs.length → Bool) {js : List (Fin gs.length)} (mem : js ∈ selections gs)
    (absent : js ∉ constrainedSelections gs caps bad) :
    (∃ j ∈ js, bad j = true) ∨
      ∃ i : Fin n, caps.getLsbD i = true ∧ 2 ≤ (js.map (fun j => gs.get j i)).sum := by
  obtain ⟨sub, cover⟩ := List.mem_filter.mp mem
  have sub := (FlatMatchSearch.mem_sublists _ _).mp sub
  cases clean : js.all (fun j => !bad j) with
  | false =>
    obtain ⟨j,hj,hb⟩ := List.all_eq_false.mp clean
    exact .inl ⟨j,hj,by simpa using hb⟩
  | true =>
    have off : Constrained.apart caps (fun j => Coverage.support (gs.get j)) 0 js = false := by
      cases h : Constrained.apart caps (fun j => Coverage.support (gs.get j)) 0 js with
      | false => rfl
      | true =>
        exfalso
        apply absent
        obtain ⟨clear, apart⟩ := Constrained.valid_of_apart caps _ 0 js
          (sub.nodup (List.nodup_finRange _)) h
        let masks := Vector.ofFn fun j : Fin gs.length => Coverage.support (gs.get j)
        have valid : Constrained.Valid caps (fun j => masks[j])
            ((List.finRange gs.length).filter fun j => !bad j) 0#n js := by
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro z hz
            exact List.mem_filter.mpr ⟨List.mem_finRange z, List.all_eq_true.mp clean z hz⟩
          · intro z hz
            simp only [masks, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
            exact clear z hz
          · intro a ha b hb ne
            simp only [masks, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
            exact apart a ha b hb ne
          · intro i
            simp only [covers, decide_eq_true_eq] at cover
            obtain ⟨j, hj, pos⟩ := cover i
            refine .inr ⟨j, hj, ?_⟩
            simp only [masks, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
            rw [Coverage.support_bit]
            exact decide_eq_true pos
        unfold constrainedSelections
        dsimp only
        split
        · obtain ⟨ys, hy, same⟩ := Constrained.enumerate_complete caps _ _ _ _ valid
          have order := (Constrained.enumerate_sublist _ _ _ _ _ _ hy).trans
            (List.filter_sublist (l := List.finRange gs.length) (p := fun j => !bad j))
          have eq : ys = js := by
            rw [← filter_members order (List.nodup_finRange _),
              ← filter_members sub (List.nodup_finRange _)]
            apply List.filter_congr
            intro x _
            simp [same]
          exact eq ▸ hy
        · obtain ⟨ys, hy, same⟩ := Constrained.search_complete caps _
            ((List.finRange gs.length).filter fun j => !bad j).length _ _ _ valid
          refine List.mem_map.mpr ⟨ys, hy, ?_⟩
          rw [← filter_members sub (List.nodup_finRange _)]
          apply List.filter_congr
          intro x _
          simp [same]
    obtain ⟨i,hc,hit⟩ := Constrained.crowded caps _ (fun j i => gs.get j i)
      (fun j i h => by rw [Coverage.support_bit] at h; exact of_decide_eq_true h) 0 js off
    rcases hit with ⟨hs,_⟩ | two
    · simp at hs
    · exact .inr ⟨i,hc,two⟩

end Tamarin.Homogeneous
