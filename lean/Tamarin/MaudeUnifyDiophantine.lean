import Tamarin.ACHilbert
import Tamarin.Interrupt

/-!
# Maude's Diophantine basis

`IntSystem::findNextMinimalSolution` (`intContejeanDevie.cc`) as Maude runs it
for AC unification: the search of Contejean and Devie from the unit vectors,
with upper bounds on the coordinates, and with the forced assignments that
Maude derives from an equation that has only one coordinate left to move.
Solutions are listed in the order Maude finds them.

A completed search returns nonzero solutions within the bounds, and every
nonzero solution within the bounds that has no other nonzero solution below
it. Every solution within the bounds is then a sum of returned solutions.
-/
namespace Tamarin.MaudeUnify.Dioph
open ACBasis.Hilbert

variable {n m : Nat}

/-- The coordinates are bounded by the given numbers; `none` is no bound. -/
def Within (upper : Vector (Option Nat) n) (x : Vector Nat n) : Prop :=
  ∀ i : Fin n, ∀ u, upper[i] = some u → x[i] ≤ u

/-- Whether a value respects a bound. -/
def fits : Option Nat → Nat → Bool
  | none, _ => true
  | some u, x => decide (x ≤ u)

theorem fits_iff (b : Option Nat) (x : Nat) : fits b x = true ↔ ∀ u, b = some u → x ≤ u := by
  cases b <;> simp [fits]

/-- The search keeps every coordinate within its bound and freezes the
coordinates that have reached it. -/
def Inv (upper : Vector (Option Nat) n) (σ : State n m) : Prop :=
  Within upper σ.point ∧ ∀ i : Fin n, upper[i] = some σ.point[i] → σ.frozen[i] = true

/-- The coordinates of equation `r` that can still move it. -/
def movable (cols : Vector (Vector Int m) n) (σ : State n m) (r : Fin m) : List (Fin n) :=
  (List.finRange n).filter fun j => !σ.frozen[j] && cols[j][r] != 0

/-- Some coordinate can still move equation `r` towards zero. -/
def hopeful (cols : Vector (Vector Int m) n) (σ : State n m) (r : Fin m) : Bool :=
  σ.residue[r] == 0 || (movable cols σ r).any fun j => decide (σ.residue[r] * cols[j][r] < 0)

/-- The first equation that cannot be balanced any more, or that has a single
coordinate left to move. -/
def issue (cols : Vector (Vector Int m) n) (σ : State n m) : Option (Fin m) :=
  (List.finRange m).find? fun r => !hopeful cols σ r || (movable cols σ r).length == 1

/-- One pass over the coordinates of equation `r`: how many can still move it,
and whether one of them moves it towards zero. -/
def tally (cols : Vector (Vector Int m) n) (σ : State n m) (r : Fin m) (l : List (Fin n)) (acc : Nat × Bool) :
    Nat × Bool :=
  l.foldl (fun acc j => if !σ.frozen[j] && cols[j][r] != 0 then
    (acc.1 + 1, acc.2 || decide (σ.residue[r] * cols[j][r] < 0)) else acc) acc

theorem tally_eq (cols : Vector (Vector Int m) n) (σ : State n m) (r : Fin m) :
    ∀ (l : List (Fin n)) (acc : Nat × Bool), tally cols σ r l acc =
      (acc.1 + (l.filter fun j => !σ.frozen[j] && cols[j][r] != 0).length,
        acc.2 || (l.filter fun j => !σ.frozen[j] && cols[j][r] != 0).any
          fun j => decide (σ.residue[r] * cols[j][r] < 0))
  | [], acc => by simp [tally]
  | j :: l, acc => by
    unfold tally
    rw [List.foldl_cons]
    have ih := tally_eq cols σ r l
    unfold tally at ih
    rw [ih]
    rw [List.filter_cons]
    by_cases h : (!σ.frozen[j] && cols[j][r] != 0) = true
    · simp only [h, ite_true, List.length_cons, List.any_cons, Bool.or_assoc, Prod.mk.injEq]
      constructor
      · omega
      · simp
    · simp only [h, Bool.false_eq_true, ite_false]

/-- The first index that satisfies a test, by a loop without a list. -/
@[inline] def firstFin (k : Nat) (p : Fin k → Bool) : Option (Fin k) :=
  Fin.foldr k (fun r acc => if p r then some r else acc) none

theorem firstFin_eq (k : Nat) (p : Fin k → Bool) : firstFin k p = (List.finRange k).find? p := by
  unfold firstFin
  rw [Fin.foldr_eq_finRange_foldr]
  generalize List.finRange k = l
  induction l with
  | nil => rfl
  | cons r l ih => rw [List.foldr_cons, ih, List.find?_cons]; split <;> simp_all

/-- Whether every index satisfies a test, by a loop without a list. -/
@[inline] def allFin (k : Nat) (p : Fin k → Bool) : Bool := Fin.foldl k (fun acc i => acc && p i) true

theorem allFin_eq (k : Nat) (p : Fin k → Bool) : allFin k p = (List.finRange k).all p := by
  unfold allFin
  rw [Fin.foldl_eq_finRange_foldl]
  have gen : ∀ (l : List (Fin k)) (acc : Bool), l.foldl (fun acc i => acc && p i) acc = (acc && l.all p) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons i l ih => intro acc; rw [List.foldl_cons, ih, List.all_cons, Bool.and_assoc]
  rw [gen, Bool.true_and]

/-- `issue` with one pass over the coordinates of each equation. -/
def issueFast (cols : Vector (Vector Int m) n) (σ : State n m) : Option (Fin m) :=
  firstFin m fun r =>
    let t := Fin.foldl n (fun acc j => if !σ.frozen[j] && cols[j][r] != 0 then
      (acc.1 + 1, acc.2 || decide (σ.residue[r] * cols[j][r] < 0)) else acc) (0, false)
    !(σ.residue[r] == 0 || t.2) || t.1 == 1

@[csimp] theorem issue_eq_issueFast : @issue = @issueFast := by
  funext n m cols σ
  unfold issue issueFast hopeful movable
  rw [firstFin_eq]
  congr 1
  funext r
  rw [Fin.foldl_eq_finRange_foldl]
  have := tally_eq cols σ r (List.finRange n) (0, false)
  unfold tally at this
  rw [this]
  simp

/-- What the equation checks make of a state before it is expanded. -/
inductive Verdict (n m : Nat) where
  | dead
  | forced (σ : State n m)
  | open (σ : State n m)

/-- Add a multiple of a column to the residue. -/
def shiftBy (c : Int) (a b : Vector Int m) : Vector Int m := Vector.zipWith (fun x y => x + c * y) a b

/-- The equation checks of `findNextMinimalSolution`, restarted after each
freeze, at most `k` times. An equation that no coordinate can balance kills
the state. An equation with a single movable coordinate either freezes it,
when the equation is balanced, or forces its value, and the state with the
forced value replaces the old one if it respects the bound and is minimal. -/
def check (cols : Vector (Vector Int m) n) (upper : Vector (Option Nat) n) (found : List (Vector Nat n)) :
    Nat → State n m → Verdict n m
  | 0, σ => .open σ
  | k + 1, σ =>
    match issue cols σ with
    | none => .open σ
    | some r =>
      if !hopeful cols σ r then .dead else
      match movable cols σ r with
      | [j] =>
        let d := σ.residue[r]
        let c := cols[j][r]
        if d = 0 then check cols upper found k { σ with frozen := σ.frozen.set j true }
        else if d % c = 0 then
          let delta := -d / c
          let p := σ.point.set j (σ.point[j] + delta.toNat)
          if fits upper[j] p[j] && minimal found p then
            .forced ⟨p, shiftBy (delta.toNat : Int) σ.residue cols[j], σ.frozen.set j true⟩
          else .dead
        else .dead
      | _ => .open σ

/-- The children of a state, as in `children`, except that a coordinate that
reaches its bound is frozen in the child. -/
def kids (cols : Vector (Vector Int m) n) (upper : Vector (Option Nat) n) (found : List (Vector Nat n))
    (σ : State n m) : List (Fin n) → Vector Bool n → List (State n m)
  | [], _ => []
  | i :: is, fz =>
    if fz[i] = false ∧ scalar σ.residue cols[i] < 0 then
      let rest := kids cols upper found σ is (fz.set i true)
      let p := bump σ.point i
      if minimal found p then
        ⟨p, shift σ.residue cols[i], if upper[i] = some p[i] then fz.set i true else fz⟩ :: rest
      else rest
    else kids cols upper found σ is fz

/-- The search. `found` lists the solutions found so far, the latest first.
A state whose residue is zero is recorded as Maude records it; otherwise it
is checked and expanded. `none` reports an exhausted step budget. -/
def search [Interrupt] (cols : Vector (Vector Int m) n) (upper : Vector (Option Nat) n) :
    Nat → List (State n m) → List (Vector Nat n) → Option (List (Vector Nat n))
  | _, [], found => some found
  | 0, _ :: _, _ => none
  | fuel + 1, σ :: stack, found =>
    if decide (∀ r : Fin m, σ.residue[r] = 0) then search cols upper fuel stack (σ.point :: found)
    else match check cols upper found (n + 1) σ with
      | .dead => search cols upper fuel stack found
      | .forced τ => search cols upper fuel (τ :: stack) found
      | .open τ => search cols upper fuel ((kids cols upper found τ (List.finRange n) τ.frozen).reverse ++ stack) found

/-- `search` as it is compiled: every step asks first, and a search told to
stop reports an exhausted budget. -/
private def searchAsking [Interrupt] (cols : Vector (Vector Int m) n) (upper : Vector (Option Nat) n) :
    Nat → List (State n m) → List (Vector Nat n) → Option (List (Vector Nat n))
  | _, [], found => some found
  | 0, _ :: _, _ => none
  | fuel + 1, σ :: stack, found =>
    if Interrupt.poll () then none else
    if decide (∀ r : Fin m, σ.residue[r] = 0) then searchAsking cols upper fuel stack (σ.point :: found)
    else match check cols upper found (n + 1) σ with
      | .dead => searchAsking cols upper fuel stack found
      | .forced τ => searchAsking cols upper fuel (τ :: stack) found
      | .open τ => searchAsking cols upper fuel ((kids cols upper found τ (List.finRange n) τ.frozen).reverse ++ stack) found

@[csimp] private theorem search_eq_asking : @search = @searchAsking := by
  funext n m i cols upper fuel stack found
  induction fuel generalizing stack found with
  | zero => cases stack <;> rfl
  | succ fuel ih =>
    cases stack with
    | nil => rfl
    | cons σ stack =>
      simp only [search, searchAsking, Interrupt.quiet, Bool.false_eq_true, ite_false]
      split <;> (try split) <;> simp only [ih]

/-- The unit vector of a coordinate, with the earlier coordinates frozen, and
the coordinate itself when its bound is one. The last coordinate is searched
first. -/
def first (cols : Vector (Vector Int m) n) (upper : Vector (Option Nat) n) : List (State n m) :=
  (List.finRange n).reverse.map fun i =>
    ⟨Vector.ofFn fun j => if j = i then 1 else 0, cols[i],
      Vector.ofFn fun j => decide (j.val < i.val) || (j = i && upper[i] == some 1)⟩

/-- The basis in the order Maude finds it, or `none` when the step budget ran out. -/
def basis [Interrupt] (cols : Vector (Vector Int m) n) (upper : Vector (Option Nat) n) (fuel : Nat) :
    Option (List (Vector Nat n)) :=
  (search cols upper fuel (first cols upper) []).map List.reverse

/-! ### Arithmetic of states -/

theorem vget_ofFn {α : Type} (f : Fin n → α) (i : Fin n) : (Vector.ofFn f)[i] = f i := by
  simp [Fin.getElem_fin]

theorem sub_at (x y : Vector Nat n) (i : Fin n) : (Vector.ofFn fun i : Fin n => x[i] - y[i])[i] = x[i] - y[i] :=
  vget_ofFn _ i

theorem le_iff' (g p : Vector Nat n) : le g p = true ↔ ∀ i : Fin n, g[i] ≤ p[i] := by
  simp [le]

theorem not_minimal' {found : List (Vector Nat n)} {p : Vector Nat n}
    (h : ¬ minimal found p = true) : ∃ g ∈ found, ∀ i : Fin n, g[i] ≤ p[i] := by
  unfold minimal at h
  rw [List.all_eq_true] at h
  apply Classical.byContradiction
  intro none
  apply h
  intro g hg
  cases e : le g p with
  | false => rfl
  | true => exact (none ⟨g, hg, (le_iff' g p).mp e⟩).elim

/-- The value of an equation after raising one coordinate by `k`. -/
theorem res_raise (cols : Vector (Vector Int m) n) (p : Vector Nat n) (j : Fin n) (k : Nat) (r : Fin m) :
    res cols (p.set j (p[j] + k)) r = res cols p r + cols[j][r] * (k : Int) := by
  have term (i : Fin n) : cols[i][r] * (((p.set j (p[j] + k))[i] : Nat) : Int) =
      cols[i][r] * (p[i] : Int) + (if i = j then cols[j][r] * (k : Int) else 0) := by
    simp only [Fin.getElem_fin, Vector.getElem_set]
    by_cases same : j.val = i.val
    · have eq : i = j := Fin.ext same.symm
      subst eq
      simp [Int.mul_add]
    · have ne : i ≠ j := fun e => same (congrArg Fin.val e).symm
      simp [same, ne]
  unfold res
  rw [show (fun i : Fin n => cols[i][r] * (((p.set j (p[j] + k))[i] : Nat) : Int)) = _ from funext term,
    isum_add, isum_single]

theorem bump_eq (p : Vector Nat n) (i : Fin n) : bump p i = p.set i (p[i] + 1) := rfl

theorem bump_at' (p : Vector Nat n) (i j : Fin n) :
    (bump p i)[j] = if i = j then p[i] + 1 else p[j] := by
  simp only [bump, Fin.getElem_fin, Vector.getElem_set]
  by_cases same : i = j
  · subst same; simp
  · have : i.val ≠ j.val := fun e => same (Fin.ext e)
    simp [same, this]

theorem set_at (p : Vector Nat n) (i j : Fin n) (v : Nat) :
    (p.set i v)[j] = if i = j then v else p[j] := by
  simp only [Fin.getElem_fin, Vector.getElem_set]
  by_cases same : i = j
  · subst same; simp
  · have : i.val ≠ j.val := fun e => same (Fin.ext e)
    simp [same, this]

theorem frozen_set (fz : Vector Bool n) (i j : Fin n) :
    (fz.set i true)[j] = true ↔ i = j ∨ fz[j] = true := by
  simp only [Fin.getElem_fin, Vector.getElem_set]
  by_cases same : i = j
  · subst same; simp
  · have : i.val ≠ j.val := fun e => same (Fin.ext e)
    simp [same, this]

/-- Below a solution, the residue of an equation is balanced by the
coordinates that are still short of the solution, and frozen coordinates
contribute nothing. -/
theorem gap (cols : Vector (Vector Int m) n) (σ : State n m) (ok : σ.Ok cols) (s : Vector Nat n)
    (hs : Sol cols s) (r : Fin m) :
    σ.residue[r] + isum (fun j : Fin n => cols[j][r] * ((s[j] : Int) - (σ.point[j] : Int))) = 0 := by
  have diff : isum (fun j : Fin n => cols[j][r] * ((s[j] : Int) - (σ.point[j] : Int))) =
      res cols s r - res cols σ.point r := by
    unfold res
    rw [← isum_sub]
    congr 1
    funext i
    simp only [Int.mul_sub]
  rw [diff, hs r, ← ok.1 r]
  omega

theorem mem_movable {cols : Vector (Vector Int m) n} {σ : State n m} {r : Fin m} {j : Fin n} :
    j ∈ movable cols σ r ↔ σ.frozen[j] = false ∧ cols[j][r] ≠ 0 := by
  simp [movable]

/-- A state that covers a solution can still balance every equation. -/
theorem hopeful_of_covers (cols : Vector (Vector Int m) n) (σ : State n m) (ok : σ.Ok cols)
    (s : Vector Nat n) (hs : Sol cols s) (cov : ACBasis.Hilbert.Covers σ s) (r : Fin m) : hopeful cols σ r = true := by
  unfold hopeful
  apply Classical.byContradiction
  intro bad
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, decide_eq_true_eq, not_or, not_exists,
    not_and] at bad
  obtain ⟨off, stuck⟩ := bad
  have g := gap cols σ ok s hs r
  have nonneg : 0 ≤ isum (fun j : Fin n => σ.residue[r] * (cols[j][r] * ((s[j] : Int) - (σ.point[j] : Int)))) := by
    apply isum_nonneg
    intro j
    cases fz : σ.frozen[j] with
    | true =>
      have same := cov.2 j fz
      simp [same]
    | false =>
      have dn : 0 ≤ (s[j] : Int) - (σ.point[j] : Int) := by have := cov.1 j; omega
      by_cases zero : cols[j][r] = 0
      · simp only [Fin.getElem_fin] at zero ⊢; simp [zero]
      · have := stuck j (mem_movable.mpr ⟨fz, zero⟩)
        rw [← Int.mul_assoc]
        exact Int.mul_nonneg (by omega) dn
  rw [isum_mul_left] at nonneg
  have sq : 0 < σ.residue[r] * σ.residue[r] := by
    rcases Int.lt_or_gt_of_ne off with neg | pos
    · have : 0 < (-σ.residue[r]) * (-σ.residue[r]) := Int.mul_pos (by omega) (by omega)
      rwa [Int.neg_mul_neg] at this
    · exact Int.mul_pos pos pos
  have : isum (fun j : Fin n => cols[j][r] * ((s[j] : Int) - (σ.point[j] : Int))) = -σ.residue[r] := by omega
  rw [this, Int.mul_neg] at nonneg
  omega

/-- With a single movable coordinate, the equation fixes its distance to the solution. -/
theorem single_gap (cols : Vector (Vector Int m) n) (σ : State n m) (ok : σ.Ok cols) (s : Vector Nat n)
    (hs : Sol cols s) (cov : ACBasis.Hilbert.Covers σ s) (r : Fin m) (j : Fin n) (one : movable cols σ r = [j]) :
    σ.residue[r] + cols[j][r] * ((s[j] : Int) - (σ.point[j] : Int)) = 0 := by
  have g := gap cols σ ok s hs r
  have only : (fun k : Fin n => cols[k][r] * ((s[k] : Int) - (σ.point[k] : Int))) =
      fun k : Fin n => if k = j then cols[j][r] * ((s[j] : Int) - (σ.point[j] : Int)) else 0 := by
    funext k
    split
    · next e => subst e; rfl
    · next ne =>
      cases fz : σ.frozen[k] with
      | true => have := cov.2 k fz; simp [this]
      | false =>
        by_cases zero : cols[k][r] = 0
        · simp only [Fin.getElem_fin] at zero ⊢; simp [zero]
        · have mem := mem_movable.mpr ⟨fz, zero⟩
          rw [one] at mem
          exact absurd (List.mem_singleton.mp mem) ne
  rw [only, isum_single] at g
  exact g

/-! ### The equation checks -/

/-- What `check` guarantees for a state that covers a minimal solution within
the bounds: it survives, and the state it hands on covers the solution too,
unless a solution already found lies below it. -/
def Keeps (s : Vector Nat n) : Verdict n m → Prop
  | .dead => False
  | .forced τ => ACBasis.Hilbert.Covers τ s
  | .open τ => ACBasis.Hilbert.Covers τ s

/-- The states that `check` hands on. -/
def Hands (cols : Vector (Vector Int m) n) (upper : Vector (Option Nat) n) : Verdict n m → Prop
  | .dead => True
  | .forced τ => τ.Ok cols ∧ Inv upper τ
  | .open τ => τ.Ok cols ∧ Inv upper τ

theorem check_hands (cols : Vector (Vector Int m) n) (upper : Vector (Option Nat) n)
    (found : List (Vector Nat n)) (k : Nat) (σ : State n m) (ok : σ.Ok cols) (inv : Inv upper σ) :
    Hands cols upper (check cols upper found k σ) := by
  induction k generalizing σ with
  | zero => exact ⟨ok, inv⟩
  | succ k ih =>
    simp only [check]
    split
    · exact ⟨ok, inv⟩
    · next r _ =>
      split
      · trivial
      · split
        · next j one =>
          split
          · exact ih { σ with frozen := σ.frozen.set j true } ok
              ⟨inv.1, fun i hi => (frozen_set _ _ _).mpr (.inr (inv.2 i hi))⟩
          · split
            · split
              · next good =>
                simp only [Bool.and_eq_true] at good
                obtain ⟨fit, _⟩ := good
                have pointAt (i : Fin n) := set_at σ.point j i (σ.point[j] + (-σ.residue[r] / cols[j][r]).toNat)
                refine ⟨⟨fun q => ?_, ?_⟩, fun i u hu => ?_, fun i hi => ?_⟩
                · rw [res_raise]
                  simp only [shiftBy, Fin.getElem_fin, Vector.getElem_zipWith]
                  have := ok.1 q
                  simp only [Fin.getElem_fin] at this
                  rw [this, Int.mul_comm]
                · obtain ⟨i, hi⟩ := ok.2
                  refine ⟨i, ?_⟩
                  rw [pointAt]
                  split
                  · next e => subst e; omega
                  · exact hi
                · rw [pointAt]
                  split
                  · next e => subst e; exact (fits_iff _ _).mp (by simpa [pointAt] using fit) u hu
                  · next ne => exact inv.1 i u hu
                · rw [pointAt] at hi
                  apply (frozen_set _ _ _).mpr
                  split at hi
                  · next e => exact .inl e
                  · exact .inr (inv.2 i hi)
              · trivial
            · trivial
        · exact ⟨ok, inv⟩

theorem check_keeps (cols : Vector (Vector Int m) n) (upper : Vector (Option Nat) n)
    (found : List (Vector Nat n)) (k : Nat) (σ : State n m) (ok : σ.Ok cols) (s : Vector Nat n)
    (hs : Minimal cols s) (hw : Within upper s) (cov : ACBasis.Hilbert.Covers σ s) :
    (∃ g ∈ found, ∀ i : Fin n, g[i] ≤ s[i]) ∨ Keeps s (check cols upper found k σ) := by
  induction k generalizing σ with
  | zero => exact .inr cov
  | succ k ih =>
    simp only [check]
    split
    · exact .inr cov
    · next r _ =>
      split
      · next bad =>
        rw [hopeful_of_covers cols σ ok s hs.1 cov r] at bad
        exact absurd bad (by decide)
      · split
        · next j one =>
          have g := single_gap cols σ ok s hs.1 cov r j one
          have nz : cols[j][r] ≠ 0 := (mem_movable.mp (one ▸ List.mem_singleton_self j)).2
          split
          · next zero =>
            have same : σ.point[j] = s[j] := by
              rw [zero, Int.zero_add] at g
              rcases Int.mul_eq_zero.mp g with h | h
              · exact absurd h nz
              · omega
            apply ih { σ with frozen := σ.frozen.set j true } ok
            refine ⟨cov.1, fun i hi => ?_⟩
            rcases (frozen_set _ _ _).mp hi with e | hi
            · subst e; exact same
            · exact cov.2 i hi
          · next off =>
            have hd : σ.residue[r] = cols[j][r] * -((s[j] : Int) - (σ.point[j] : Int)) := by
              rw [Int.mul_neg]; omega
            have div : σ.residue[r] % cols[j][r] = 0 := by rw [hd]; exact Int.mul_emod_right _ _
            have delta : -σ.residue[r] / cols[j][r] = (s[j] : Int) - (σ.point[j] : Int) := by
              rw [hd, Int.neg_mul_eq_mul_neg, Int.neg_neg, Int.mul_ediv_cancel_left _ nz]
            have le := cov.1 j
            have newAt : σ.point[j] + (-σ.residue[r] / cols[j][r]).toNat = s[j] := by
              rw [delta]; omega
            simp only [div, ↓reduceIte]
            have pointAt (i : Fin n) := set_at σ.point j i (σ.point[j] + (-σ.residue[r] / cols[j][r]).toNat)
            have below (i : Fin n) : (σ.point.set j (σ.point[j] + (-σ.residue[r] / cols[j][r]).toNat))[i] ≤ s[i] := by
              rw [pointAt]
              split
              · next e => subst e; omega
              · exact cov.1 i
            split
            · next good =>
              refine .inr ⟨below, fun i hi => ?_⟩
              rw [pointAt]
              rcases (frozen_set _ _ _).mp hi with e | hi
              · subst e; rw [ite_eq_left rfl, newAt]
              · split
                · next e => subst e; rw [newAt]
                · exact cov.2 i hi
            · next bad =>
              cases hm : minimal found (σ.point.set j (σ.point[j] + (-σ.residue[r] / cols[j][r]).toNat)) with
              | false =>
                obtain ⟨g, hg, under⟩ := not_minimal' (by rw [hm]; decide)
                exact .inl ⟨g, hg, fun i => Nat.le_trans (under i) (below i)⟩
              | true =>
                exfalso
                apply bad
                rw [hm, Bool.and_true, fits_iff]
                intro u hu
                rw [pointAt, ite_eq_left rfl, newAt]
                exact hw j u hu
        · exact .inr cov

/-! ### Children -/

theorem kids_hands (cols : Vector (Vector Int m) n) (upper : Vector (Option Nat) n)
    (found : List (Vector Nat n)) (σ : State n m) (ok : σ.Ok cols) (inv : Inv upper σ)
    (is : List (Fin n)) (fz : Vector Bool n) (sup : ∀ j : Fin n, σ.frozen[j] = true → fz[j] = true) :
    ∀ τ ∈ kids cols upper found σ is fz, τ.Ok cols ∧ Inv upper τ := by
  induction is generalizing fz with
  | nil => intro τ h; cases h
  | cons i is ih =>
    intro τ h
    have sup' : ∀ j : Fin n, σ.frozen[j] = true → (fz.set i true)[j] = true :=
      fun j hj => (frozen_set _ _ _).mpr (.inr (sup j hj))
    simp only [kids] at h
    split at h
    · next eligible =>
      split at h
      · rcases List.mem_cons.mp h with rfl | h
        · have short : ∀ u, upper[i] = some u → σ.point[i] < u := by
            intro u hu
            have le := inv.1 i u hu
            rcases Nat.lt_or_eq_of_le le with lt | eq
            · exact lt
            · have := sup i (inv.2 i (eq ▸ hu))
              rw [eligible.1] at this
              cases this
          refine ⟨⟨fun r => ?_, i, by rw [bump_at']; simp⟩, fun j u hu => ?_, fun j hj => ?_⟩
          · show (shift σ.residue cols[i])[r] = res cols (bump σ.point i) r
            rw [bump_eq, res_raise, ← ok.1 r]
            simp [shift]
          · rw [bump_at']
            split
            · next e => subst e; have := short u hu; omega
            · exact inv.1 j u hu
          · split
            · next top =>
              apply (frozen_set _ _ _).mpr
              by_cases e : i = j
              · exact .inl e
              · rw [bump_at', ite_eq_right e] at hj
                exact .inr (sup j (inv.2 j hj))
            · next notTop =>
              by_cases e : i = j
              · subst e; exact absurd hj notTop
              · rw [bump_at', ite_eq_right e] at hj
                exact sup j (inv.2 j hj)
        · exact ih _ sup' τ h
      · exact ih _ sup' τ h
    · exact ih _ sup τ h

/-- If an eligible coordinate is still short of a solution within the bounds,
a child covers the solution, unless a solution already found lies below it. -/
theorem kids_covers (cols : Vector (Vector Int m) n) (upper : Vector (Option Nat) n)
    (found : List (Vector Nat n)) (σ : State n m) (s : Vector Nat n) (hw : Within upper s)
    (below : ∀ i : Fin n, σ.point[i] ≤ s[i])
    (is : List (Fin n)) (fz : Vector Bool n)
    (agree : ∀ i : Fin n, fz[i] = true → σ.point[i] = s[i])
    (short : ∃ i ∈ is, fz[i] = false ∧ scalar σ.residue cols[i] < 0 ∧ σ.point[i] < s[i]) :
    (∃ g ∈ found, ∀ i : Fin n, g[i] ≤ s[i]) ∨
      ∃ τ ∈ kids cols upper found σ is fz, ACBasis.Hilbert.Covers τ s := by
  induction is generalizing fz with
  | nil => obtain ⟨_, h, _⟩ := short; cases h
  | cons i is ih =>
    obtain ⟨k, hk, free, down, lt⟩ := short
    simp only [kids]
    split
    next eligible =>
      by_cases here : σ.point[i] < s[i]
      · have fits' (j : Fin n) : (bump σ.point i)[j] ≤ s[j] := by
          rw [bump_at']
          split
          · next e => subst e; omega
          · exact below j
        split
        next keep =>
          refine .inr ⟨_, List.mem_cons_self, fits', fun j hj => ?_⟩
          split at hj
          · next top =>
            rcases (frozen_set _ _ _).mp hj with e | hj
            · subst e
              show (bump σ.point i)[i] = s[i]
              have := hw i _ top
              have := fits' i
              omega
            · rw [bump_at']
              have ne : i ≠ j := fun e => by subst e; rw [eligible.1] at hj; cases hj
              simp only [ne, ite_false]
              exact agree j hj
          · rw [bump_at']
            have ne : i ≠ j := fun e => by subst e; rw [eligible.1] at hj; cases hj
            simp only [ne, ite_false]
            exact agree j hj
        next drop =>
          obtain ⟨g, hg, under⟩ := not_minimal' drop
          exact .inl ⟨g, hg, fun j => Nat.le_trans (under j) (fits' j)⟩
      · have same : σ.point[i] = s[i] := by have := below i; omega
        have next : ∃ k ∈ is, (fz.set i true)[k] = false ∧ scalar σ.residue cols[k] < 0 ∧
            σ.point[k] < s[k] := by
          have ne : k ≠ i := fun e => by subst e; omega
          refine ⟨k, ?_, ?_, down, lt⟩
          · rcases List.mem_cons.mp hk with e | h
            · exact (ne e).elim
            · exact h
          · cases h : (fz.set i true)[k] with
            | false => rfl
            | true =>
              rcases (frozen_set _ _ _).mp h with e | h
              · exact (ne e.symm).elim
              · rw [free] at h; cases h
        have frozen (j : Fin n) (hj : (fz.set i true)[j] = true) : σ.point[j] = s[j] := by
          rcases (frozen_set _ _ _).mp hj with e | hj
          · subst e; exact same
          · exact agree j hj
        rcases ih _ frozen next with found | ⟨τ, hτ, cov⟩
        · exact .inl found
        · refine .inr ⟨τ, ?_, cov⟩
          split
          · exact List.mem_cons_of_mem _ hτ
          · exact hτ
    next blocked =>
      have ne : k ≠ i := fun e => by subst e; exact blocked ⟨free, down⟩
      have next : ∃ k ∈ is, fz[k] = false ∧ scalar σ.residue cols[k] < 0 ∧ σ.point[k] < s[k] := by
        refine ⟨k, ?_, free, down, lt⟩
        rcases List.mem_cons.mp hk with e | h
        · exact (ne e).elim
        · exact h
      exact ih _ agree next

theorem check_open (cols : Vector (Vector Int m) n) (upper : Vector (Option Nat) n)
    (found : List (Vector Nat n)) (k : Nat) (σ τ : State n m) (h : check cols upper found k σ = .open τ) :
    τ.point = σ.point ∧ τ.residue = σ.residue := by
  induction k generalizing σ with
  | zero => simp only [check, Verdict.open.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  | succ k ih =>
    simp only [check] at h
    split at h
    · simp only [Verdict.open.injEq] at h; subst h; exact ⟨rfl, rfl⟩
    · split at h
      · cases h
      · split at h
        · split at h
          · have := ih _ h; exact this
          · split at h
            · split at h <;> cases h
            · cases h
        · simp only [Verdict.open.injEq] at h; subst h; exact ⟨rfl, rfl⟩

/-! ### The search -/

theorem zero_sol (cols : Vector (Vector Int m) n) (σ : State n m) (ok : σ.Ok cols)
    (h : ∀ r : Fin m, σ.residue[r] = 0) : Sol cols σ.point := by
  intro r; rw [← ok.1 r]; exact h r

/-- A completed search returns nonzero solutions within the bounds, and every
minimal solution within the bounds that was found or that some state of the
stack covers. -/
theorem search_spec (cols : Vector (Vector Int m) n) (upper : Vector (Option Nat) n) (fuel : Nat)
    (stack : List (State n m)) (found out : List (Vector Nat n))
    (done : search cols upper fuel stack found = some out)
    (states : ∀ σ ∈ stack, σ.Ok cols ∧ Inv upper σ)
    (sols : ∀ g ∈ found, Sol cols g ∧ Nonzero g ∧ Within upper g) :
    (∀ g ∈ out, Sol cols g ∧ Nonzero g ∧ Within upper g) ∧
    ∀ s, Minimal cols s → Within upper s →
      (s ∈ found ∨ ∃ σ ∈ stack, ACBasis.Hilbert.Covers σ s) → s ∈ out := by
  induction fuel generalizing stack found with
  | zero =>
    cases stack with
    | nil =>
      obtain rfl : found = out := by simpa [search] using done
      refine ⟨sols, fun s _ _ h => ?_⟩
      rcases h with h | ⟨_, h, _⟩
      · exact h
      · cases h
    | cons σ stack => simp [search] at done
  | succ fuel ih =>
    cases stack with
    | nil =>
      obtain rfl : found = out := by simpa [search] using done
      refine ⟨sols, fun s _ _ h => ?_⟩
      rcases h with h | ⟨_, h, _⟩
      · exact h
      · cases h
    | cons σ stack =>
      obtain ⟨okσ, invσ⟩ := states σ List.mem_cons_self
      have rest (τ) (h : τ ∈ stack) := states τ (List.mem_cons_of_mem _ h)
      -- what a covering state that is dropped leaves: a found solution below the target
      have dropped (s : Vector Nat n) (hs : Minimal cols s)
          (h : ∃ g ∈ found, ∀ i : Fin n, g[i] ≤ s[i]) : s ∈ found := by
        obtain ⟨g, hg, under⟩ := h
        have eq : g = s := hs.2.2 g (sols g hg).1 (sols g hg).2.1 under
        exact eq ▸ hg
      simp only [search] at done
      split at done
      next solved =>
        have sol := zero_sol cols σ okσ (of_decide_eq_true solved)
        have grown : ∀ g ∈ σ.point :: found, Sol cols g ∧ Nonzero g ∧ Within upper g := by
          intro g hg
          rcases List.mem_cons.mp hg with rfl | hg
          · exact ⟨sol, okσ.2, invσ.1⟩
          · exact sols g hg
        obtain ⟨sound, complete⟩ := ih stack _ done rest grown
        refine ⟨sound, fun s hs hw h => complete s hs hw ?_⟩
        rcases h with h | ⟨τ, hτ, cov⟩
        · exact .inl (List.mem_cons_of_mem _ h)
        · rcases List.mem_cons.mp hτ with rfl | hτ
          · have same : τ.point = s := hs.2.2 _ sol okσ.2 cov.1
            exact .inl (same ▸ List.mem_cons_self)
          · exact .inr ⟨τ, hτ, cov⟩
      next open_ =>
        have hands := check_hands cols upper found (n + 1) σ okσ invσ
        have keeps (s : Vector Nat n) (hs : Minimal cols s) (hw : Within upper s)
            (cov : ACBasis.Hilbert.Covers σ s) :=
          check_keeps cols upper found (n + 1) σ okσ s hs hw cov
        split at done
        next dead =>
          obtain ⟨sound, complete⟩ := ih stack found done rest sols
          refine ⟨sound, fun s hs hw h => complete s hs hw ?_⟩
          rcases h with h | ⟨τ, hτ, cov⟩
          · exact .inl h
          · rcases List.mem_cons.mp hτ with rfl | hτ
            · rcases keeps s hs hw cov with below | k
              · exact .inl (dropped s hs below)
              · rw [dead] at k; cases k
            · exact .inr ⟨τ, hτ, cov⟩
        next τ forced =>
          rw [forced] at hands
          have all : ∀ υ ∈ τ :: stack, υ.Ok cols ∧ Inv upper υ := by
            intro υ h
            rcases List.mem_cons.mp h with rfl | h
            · exact hands
            · exact rest υ h
          obtain ⟨sound, complete⟩ := ih _ found done all sols
          refine ⟨sound, fun s hs hw h => complete s hs hw ?_⟩
          rcases h with h | ⟨υ, hυ, cov⟩
          · exact .inl h
          · rcases List.mem_cons.mp hυ with rfl | hυ
            · rcases keeps s hs hw cov with below | k
              · exact .inl (dropped s hs below)
              · rw [forced] at k; exact .inr ⟨τ, List.mem_cons_self, k⟩
            · exact .inr ⟨υ, List.mem_cons_of_mem _ hυ, cov⟩
        next τ opened =>
          have same := check_open cols upper found (n + 1) σ τ opened
          rw [opened] at hands
          have kidsOk := kids_hands cols upper found τ hands.1 hands.2 (List.finRange n) τ.frozen
            (fun _ h => h)
          have all : ∀ υ ∈ (kids cols upper found τ (List.finRange n) τ.frozen).reverse ++ stack,
              υ.Ok cols ∧ Inv upper υ := by
            intro υ h
            rcases List.mem_append.mp h with h | h
            · exact kidsOk υ (List.mem_reverse.mp h)
            · exact rest υ h
          obtain ⟨sound, complete⟩ := ih _ found done all sols
          refine ⟨sound, fun s hs hw h => complete s hs hw ?_⟩
          rcases h with h | ⟨υ, hυ, cov⟩
          · exact .inl h
          · rcases List.mem_cons.mp hυ with rfl | hυ
            · rcases keeps s hs hw cov with below | k
              · exact .inl (dropped s hs below)
              · rw [opened] at k
                have off : ∃ r : Fin m, τ.residue[r] ≠ 0 := by
                  apply Classical.byContradiction
                  intro none
                  apply open_
                  apply decide_eq_true
                  intro r
                  rw [← same.2]
                  apply Classical.byContradiction
                  intro ne
                  exact none ⟨r, ne⟩
                obtain ⟨i, lt, down⟩ := direction cols τ.point s τ.residue hands.1.1 hs.1 k.1 off
                have free : τ.frozen[i] = false := by
                  cases h : τ.frozen[i] with
                  | false => rfl
                  | true => have := k.2 i h; omega
                rcases kids_covers cols upper found τ s hw k.1 (List.finRange n) τ.frozen k.2
                  ⟨i, List.mem_finRange i, free, down, lt⟩ with below | ⟨ω, hω, c⟩
                · exact .inl (dropped s hs below)
                · exact .inr ⟨ω, List.mem_append_left _ (List.mem_reverse.mpr hω), c⟩
            · exact .inr ⟨υ, List.mem_append_right _ hυ, cov⟩

/-! ### The first states -/

theorem first_hands (cols : Vector (Vector Int m) n) (upper : Vector (Option Nat) n)
    (pos : ∀ i : Fin n, upper[i] ≠ some 0) : ∀ σ ∈ first cols upper, σ.Ok cols ∧ Inv upper σ := by
  intro σ h
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp h
  have unitAt (j : Fin n) : (Vector.ofFn fun j : Fin n => if j = i then 1 else 0)[j] = if j = i then 1 else 0 := by
    simp
  refine ⟨⟨fun r => ?_, i, by simp⟩, fun j u hu => ?_, fun j hj => ?_⟩
  · unfold res
    have term (j : Fin n) : cols[j][r] * (((Vector.ofFn fun j : Fin n => if j = i then 1 else 0)[j] : Nat) : Int) =
        if j = i then cols[i][r] else 0 := by
      rw [unitAt]
      by_cases e : j = i
      · subst e; simp
      · simp [e]
    rw [show (fun j : Fin n => cols[j][r] * (((Vector.ofFn fun j : Fin n => if j = i then 1 else 0)[j] : Nat) : Int)) = _
      from funext term, isum_single]
  · show (Vector.ofFn fun j : Fin n => if j = i then 1 else 0)[j] ≤ u
    rw [unitAt]
    split
    · next e => subst e; have := pos j; cases u with
      | zero => exact absurd hu this
      | succ u => omega
    · omega
  · show (Vector.ofFn fun j : Fin n => decide (j.val < i.val) || (j = i && upper[i] == some 1))[j] = true
    change upper[j] = some ((Vector.ofFn fun j : Fin n => if j = i then 1 else 0)[j]) at hj
    rw [unitAt] at hj
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
      beq_iff_eq]
    split at hj
    · next e => subst e; exact .inr ⟨rfl, hj⟩
    · exact absurd hj (pos j)

theorem first_covers (cols : Vector (Vector Int m) n) (upper : Vector (Option Nat) n) (s : Vector Nat n)
    (nz : Nonzero s) (hw : Within upper s) :
    ∃ σ ∈ first cols upper, ACBasis.Hilbert.Covers σ s := by
  classical
  have earliest : ∃ i : Fin n, 0 < s[i] ∧ ∀ j : Fin n, j.val < i.val → s[j] = 0 := by
    obtain ⟨i, hi⟩ := nz
    induction h : i.val using Nat.strongRecOn generalizing i with
    | ind k ih =>
      by_cases early : ∃ j : Fin n, j.val < i.val ∧ 0 < s[j]
      · obtain ⟨j, lt, pos⟩ := early
        exact ih j.val (h ▸ lt) j pos rfl
      · refine ⟨i, hi, fun j lt => ?_⟩
        apply Classical.byContradiction
        intro ne
        exact early ⟨j, lt, by omega⟩
  obtain ⟨i, pos, before⟩ := earliest
  refine ⟨_, List.mem_map.mpr ⟨i, List.mem_reverse.mpr (List.mem_finRange i), rfl⟩,
    fun j => ?_, fun j hj => ?_⟩
  · show (Vector.ofFn fun j : Fin n => if j = i then 1 else 0)[j] ≤ s[j]
    rw [vget_ofFn]
    split
    · next e => subst e; omega
    · omega
  · change (Vector.ofFn fun j : Fin n => decide (j.val < i.val) || (j = i && upper[i] == some 1))[j] = true at hj
    show (Vector.ofFn fun j : Fin n => if j = i then 1 else 0)[j] = s[j]
    rw [vget_ofFn] at hj
    rw [vget_ofFn]
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hj
    rcases hj with lt | ⟨e, one⟩
    · have ne : j ≠ i := fun e => by subst e; omega
      rw [ite_eq_right ne]
      exact (before j lt).symm
    · subst e
      rw [ite_eq_left rfl]
      have := hw j 1 one
      omega

/-! ### The basis -/

theorem basis_spec (cols : Vector (Vector Int m) n) (upper : Vector (Option Nat) n) (fuel : Nat)
    {out : List (Vector Nat n)} (h : basis cols upper fuel = some out) (pos : ∀ i : Fin n, upper[i] ≠ some 0) :
    (∀ g ∈ out, Sol cols g ∧ Nonzero g ∧ Within upper g) ∧
    ∀ s, Minimal cols s → Within upper s → s ∈ out := by
  unfold basis at h
  cases done : search cols upper fuel (first cols upper) [] with
  | none => simp [done] at h
  | some found =>
    obtain rfl : found.reverse = out := by simpa [done] using h
    obtain ⟨sound, complete⟩ := search_spec cols upper fuel _ [] found done (first_hands cols upper pos)
      (fun _ h => by cases h)
    refine ⟨fun g hg => sound g (List.mem_reverse.mp hg), fun s hs hw => List.mem_reverse.mpr ?_⟩
    obtain ⟨σ, hσ, cov⟩ := first_covers cols upper s hs.2.1 hw
    exact complete s hs hw (.inr ⟨σ, hσ, cov⟩)

/-- The sum of the coordinates. -/
def total (x : Vector Nat n) : Nat := ((List.finRange n).map fun i => x[i]).sum

theorem total_lt {x y : Vector Nat n} (le : ∀ i : Fin n, y[i] ≤ x[i]) (ne : y ≠ x) : total y < total x := by
  unfold total
  have strict : ∃ i : Fin n, y[i] < x[i] := by
    apply Classical.byContradiction
    intro none
    apply ne
    apply Vector.ext
    intro i hi
    have a := le ⟨i, hi⟩
    have b : ¬ y[(⟨i, hi⟩ : Fin n)] < x[(⟨i, hi⟩ : Fin n)] := fun h => none ⟨⟨i, hi⟩, h⟩
    simp only [Fin.getElem_fin] at a b
    omega
  obtain ⟨k, hk⟩ := strict
  have go : ∀ l : List (Fin n), k ∈ l → (l.map fun i => y[i]).sum < (l.map fun i => x[i]).sum := by
    intro l hl
    induction l with
    | nil => cases hl
    | cons a as ih =>
      simp only [List.map_cons, List.sum_cons]
      have tail : (as.map fun i => y[i]).sum ≤ (as.map fun i => x[i]).sum := by
        clear ih hl
        induction as with
        | nil => simp
        | cons b bs ihb => simp only [List.map_cons, List.sum_cons]; have := le b; omega
      rcases List.mem_cons.mp hl with rfl | hl
      · omega
      · have := ih hl; have := le a; omega
  exact go _ (List.mem_finRange k)

/-- The difference of two vectors, coordinatewise. -/
def sub (x y : Vector Nat n) : Vector Nat n := Vector.ofFn fun i => x[i] - y[i]

theorem res_sub (cols : Vector (Vector Int m) n) {x y : Vector Nat n} (le : ∀ i : Fin n, y[i] ≤ x[i]) (r : Fin m) :
    res cols (sub x y) r = res cols x r - res cols y r := by
  unfold res
  rw [← isum_sub]
  congr 1
  funext i
  have := le i
  show cols[i][r] * (((Vector.ofFn fun i : Fin n => x[i] - y[i])[i] : Nat) : Int) = _
  rw [sub_at, Int.natCast_sub this, Int.mul_sub]

/-- Below every nonzero solution there is a minimal one. -/
theorem exists_minimal (cols : Vector (Vector Int m) n) (x : Vector Nat n) (hx : Sol cols x) (nz : Nonzero x) :
    ∃ y, Minimal cols y ∧ ∀ i : Fin n, y[i] ≤ x[i] := by
  induction h : total x using Nat.strongRecOn generalizing x with
  | ind k ih =>
    by_cases least : ∀ y, Sol cols y → Nonzero y → (∀ i : Fin n, y[i] ≤ x[i]) → y = x
    · exact ⟨x, ⟨hx, nz, least⟩, fun _ => Nat.le_refl _⟩
    · simp only [Classical.not_forall] at least
      obtain ⟨y, hy, ny, le, ne⟩ := least
      obtain ⟨z, hz, below⟩ := ih (total y) (h ▸ total_lt le ne) y hy ny rfl
      exact ⟨z, hz, fun i => Nat.le_trans (below i) (le i)⟩

/-- Every solution within the bounds is a sum of returned solutions. -/
theorem basis_generates (cols : Vector (Vector Int m) n) (upper : Vector (Option Nat) n) (fuel : Nat)
    {out : List (Vector Nat n)} (h : basis cols upper fuel = some out) (pos : ∀ i : Fin n, upper[i] ≠ some 0)
    (x : Vector Nat n) (hx : Sol cols x) (hw : Within upper x) :
    ∃ gs : List (Vector Nat n), (∀ g ∈ gs, g ∈ out) ∧ ∀ i : Fin n, x[i] = (gs.map fun g => g[i]).sum := by
  have complete := (basis_spec cols upper fuel h pos).2
  induction hk : total x using Nat.strongRecOn generalizing x with
  | ind k ih =>
    by_cases nz : Nonzero x
    · obtain ⟨y, hy, le⟩ := exists_minimal cols x hx nz
      have yw : Within upper y := fun i u hu => Nat.le_trans (le i) (hw i u hu)
      have mem := complete y hy yw
      have dsol : Sol cols (sub x y) := by
        intro r; rw [res_sub cols le, hx r, hy.1 r]; rfl
      have dw : Within upper (sub x y) := fun i u hu => by
        show (Vector.ofFn fun i : Fin n => x[i] - y[i])[i] ≤ u
        rw [sub_at]; have := hw i u hu; omega
      have smaller : total (sub x y) < k := by
        rw [← hk]
        apply total_lt (fun i => by
          show (Vector.ofFn fun i : Fin n => x[i] - y[i])[i] ≤ x[i]
          rw [sub_at]; omega)
        intro eq
        obtain ⟨i, hi⟩ := hy.2.1
        have := congrArg (fun v : Vector Nat n => v[i]) eq
        simp only [sub] at this
        rw [sub_at] at this
        have := le i
        omega
      obtain ⟨gs, hgs, sum⟩ := ih _ smaller (sub x y) dsol dw rfl
      refine ⟨y :: gs, fun g hg => ?_, fun i => ?_⟩
      · rcases List.mem_cons.mp hg with rfl | hg
        · exact mem
        · exact hgs g hg
      · simp only [List.map_cons, List.sum_cons]
        have := sum i
        simp only [sub] at this
        rw [sub_at] at this
        have := le i
        omega
    · refine ⟨[], by simp, fun i => ?_⟩
      apply Classical.byContradiction
      intro ne
      have ne' : x[i] ≠ 0 := by simpa using ne
      exact nz ⟨i, Nat.pos_of_ne_zero ne'⟩

end Tamarin.MaudeUnify.Dioph
