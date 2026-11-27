import Tamarin.ACBasisFast
import Tamarin.ACDistributedBasisEnumeration

/-! The minimal nonnegative solutions of a homogeneous integer system, found
by the search of Contejean and Devie as Maude runs it (`intContejeanDevie.cc`):
start from the unit vectors and increment one coordinate at a time, only in a
direction whose column has a negative scalar product with the current residue.
Coordinates are tried in a fixed order and an earlier coordinate is frozen in
the states that increment a later one, so no vector is reached twice. A state
that dominates a solution already found is dropped.

The coefficients stay coefficients: a coordinate that occurs many times in a
row costs one multiplication, not one coordinate per occurrence. The search is
given a step budget and reports when it runs out, so that its caller keeps a
total function without a termination argument for the search itself. -/
namespace Tamarin.ACBasis.Hilbert

/-- Sum of an integer family, without building a list. -/
def isum {k : Nat} (f : Fin k → Int) : Int := Fin.foldl k (fun acc i => acc + f i) 0

private theorem foldl_init {k : Nat} (f : Fin k → Int) (a : Int) :
    Fin.foldl k (fun acc i => acc + f i) a = a + isum f := by
  induction k with
  | zero => simp [isum]
  | succ k ih =>
    have full : isum f = isum (fun i => f i.castSucc) + f (Fin.last k) := by
      simp only [isum, Fin.foldl_succ_last]
    rw [Fin.foldl_succ_last, ih, full]
    omega

theorem isum_zero (f : Fin 0 → Int) : isum f = 0 := by simp [isum]

theorem isum_last {k : Nat} (f : Fin (k+1) → Int) :
    isum f = isum (fun i => f i.castSucc) + f (Fin.last k) := by
  simp [isum, Fin.foldl_succ_last]

theorem isum_first {k : Nat} (f : Fin (k+1) → Int) :
    isum f = f 0 + isum (fun i => f i.succ) := by
  rw [isum, Fin.foldl_succ, foldl_init]
  omega

theorem isum_add {k : Nat} (f g : Fin k → Int) :
    isum (fun i => f i + g i) = isum f + isum g := by
  induction k with
  | zero => simp [isum_zero]
  | succ k ih => rw [isum_last, isum_last f, isum_last g, ih]; omega

theorem isum_const_zero (k : Nat) : isum (fun _ : Fin k => (0 : Int)) = 0 := by
  induction k with
  | zero => exact isum_zero _
  | succ k ih => rw [isum_last, ih]; rfl

theorem isum_mul_left {k : Nat} (c : Int) (f : Fin k → Int) :
    isum (fun i => c * f i) = c * isum f := by
  induction k with
  | zero => simp [isum_zero]
  | succ k ih => rw [isum_last, isum_last f, ih, Int.mul_add]

theorem isum_sub {k : Nat} (f g : Fin k → Int) :
    isum (fun i => f i - g i) = isum f - isum g := by
  have split : isum f = isum (fun i => f i - g i) + isum g := by
    rw [← isum_add]
    congr 1
    funext i
    omega
  omega

theorem isum_comm {k l : Nat} (f : Fin k → Fin l → Int) :
    isum (fun i => isum (fun j => f i j)) = isum (fun j => isum (fun i => f i j)) := by
  induction k with
  | zero =>
    simp only [isum_zero]
    exact (isum_const_zero l).symm
  | succ k ih =>
    rw [isum_last, ih, ← isum_add]
    congr 1
    funext j
    rw [isum_last]

theorem isum_nonneg {k : Nat} (f : Fin k → Int) (h : ∀ i, 0 ≤ f i) : 0 ≤ isum f := by
  induction k with
  | zero => simp [isum_zero]
  | succ k ih =>
    rw [isum_last]
    have := ih (fun i => f i.castSucc) (fun i => h _)
    have := h (Fin.last k)
    omega

theorem isum_pos {k : Nat} (f : Fin k → Int) (h : ∀ i, 0 ≤ f i) (i : Fin k) (hi : 0 < f i) :
    0 < isum f := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    rw [isum_last]
    have tail := isum_nonneg (fun i => f i.castSucc) (fun i => h _)
    have last := h (Fin.last k)
    by_cases at_end : i = Fin.last k
    · subst at_end; omega
    · have lt : i.val < k := by
        have ne : i.val ≠ k := fun e => at_end (Fin.ext e)
        have := i.isLt
        omega
      have := ih (fun i => f i.castSucc) (fun i => h _) ⟨i.val, lt⟩ hi
      omega

theorem isum_single {k : Nat} (i : Fin k) (c : Int) :
    isum (fun j => if j = i then c else 0) = c := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    rw [isum_last]
    by_cases at_end : i = Fin.last k
    · subst at_end
      have none : (fun j : Fin k => if j.castSucc = Fin.last k then c else 0) = fun _ => 0 := by
        funext j
        have : j.castSucc ≠ Fin.last k := fun e => by
          have := congrArg Fin.val e
          simp at this
          omega
        simp [this]
      rw [none, isum_const_zero]
      simp
    · have lt : i.val < k := by
        have ne : i.val ≠ k := fun e => at_end (Fin.ext e)
        have := i.isLt
        omega
      have same : (fun j : Fin k => if j.castSucc = i then c else 0) =
          fun j => if j = ⟨i.val, lt⟩ then c else 0 := by
        funext j
        have : j.castSucc = i ↔ j = ⟨i.val, lt⟩ := by
          constructor
          · intro e
            apply Fin.ext
            have := congrArg Fin.val e
            simpa using this
          · intro e; subst e; exact Fin.ext rfl
        simp [this]
      have ne : Fin.last k ≠ i := Ne.symm at_end
      rw [same, ih]
      simp [ne]

theorem cast_total {n : Nat} (v : Vec n) : ((total v : Nat) : Int) = isum (fun i => (v i : Int)) := by
  induction n with
  | zero => simp [total, isum_zero]
  | succ n ih =>
    rw [isum_first, ← ih (fun i => v i.succ)]
    simp [total, List.ofFn_succ]

variable {n m : Nat}

/-- One search state: a nonzero vector, the value of every equation on it,
and the coordinates that its descendants no longer increment. -/
structure State (n m : Nat) where
  point : Vector Nat n
  residue : Vector Int m
  frozen : Vector Bool n

/-- The value of equation `r` on a vector. The matrix is stored by columns. -/
def res (cols : Vector (Vector Int m) n) (x : Vector Nat n) (r : Fin m) : Int :=
  isum fun i : Fin n => cols[i][r] * (x[i] : Int)

def Sol (cols : Vector (Vector Int m) n) (x : Vector Nat n) : Prop := ∀ r, res cols x r = 0

def Nonzero (x : Vector Nat n) : Prop := ∃ i : Fin n, 0 < x[i]

def State.Ok (cols : Vector (Vector Int m) n) (σ : State n m) : Prop :=
  (∀ r : Fin m, σ.residue[r] = res cols σ.point r) ∧ Nonzero σ.point

def le (g p : Vector Nat n) : Bool := decide (∀ i : Fin n, g[i] ≤ p[i])

/-- No solution found so far lies below the vector. -/
def minimal (found : List (Vector Nat n)) (p : Vector Nat n) : Bool := found.all fun g => !le g p

def scalar (a b : Vector Int m) : Int := isum fun r : Fin m => a[r] * b[r]

def bump (p : Vector Nat n) (i : Fin n) : Vector Nat n := p.set i (p[i] + 1)

def shift (a b : Vector Int m) : Vector Int m := Vector.zipWith (· + ·) a b

/-- The states that increment one coordinate of a state. A coordinate is
eligible if it is not frozen and moves the residue towards zero. The states
that increment a later coordinate keep the earlier eligible ones frozen. -/
def children (cols : Vector (Vector Int m) n) (found : List (Vector Nat n)) (σ : State n m) :
    List (Fin n) → Vector Bool n → List (State n m)
  | [], _ => []
  | i :: is, fz =>
    if fz[i] = false ∧ scalar σ.residue cols[i] < 0 then
      let rest := children cols found σ is (fz.set i true)
      let p := bump σ.point i
      if minimal found p then ⟨p, shift σ.residue cols[i], fz⟩ :: rest else rest
    else children cols found σ is fz

/-- Every equation that is off balance has a coordinate that is not frozen and
moves it towards zero. A state without one reaches no solution. -/
def viable (cols : Vector (Vector Int m) n) (σ : State n m) : Bool :=
  decide (∀ r : Fin m, σ.residue[r] = 0 ∨
    ∃ i : Fin n, σ.frozen[i] = false ∧ σ.residue[r] * cols[i][r] < 0)

/-- Depth-first search from a stack of states. `none` reports an exhausted
step budget. -/
def search (cols : Vector (Vector Int m) n) :
    Nat → List (State n m) → List (Vector Nat n) → Option (List (Vector Nat n))
  | _, [], found => some found
  | 0, _ :: _, _ => none
  | fuel+1, σ :: stack, found =>
    if decide (∀ r : Fin m, σ.residue[r] = 0) then
      search cols fuel stack (if minimal found σ.point then σ.point :: found else found)
    else if viable cols σ then
      -- The child with the most frozen coordinates is searched first: its
      -- solutions are small and prune the wider children.
      search cols fuel ((children cols found σ (List.finRange n) σ.frozen).reverse ++ stack) found
    else search cols fuel stack found

private theorem res_bump (cols : Vector (Vector Int m) n) (p : Vector Nat n) (i : Fin n) (r : Fin m) :
    res cols (bump p i) r = res cols p r + cols[i][r] := by
  have term (j : Fin n) : cols[j][r] * ((bump p i)[j] : Int) =
      cols[j][r] * (p[j] : Int) + (if j = i then cols[i][r] else 0) := by
    simp only [bump, Fin.getElem_fin, Vector.getElem_set]
    by_cases same : i.val = j.val
    · have eq : j = i := Fin.ext same.symm
      subst eq
      simp [Int.mul_add]
    · have ne : j ≠ i := fun e => same (congrArg Fin.val e).symm
      simp [same, ne]
  unfold res
  rw [show (fun j : Fin n => cols[j][r] * ((bump p i)[j] : Int)) = _ from funext term,
    isum_add, isum_single]

private theorem sq_nonneg (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · have : 0 ≤ (-a) * (-a) := Int.mul_nonneg (by omega) (by omega)
    rwa [Int.neg_mul_neg] at this

private theorem sq_pos (a : Int) (h : a ≠ 0) : 0 < a * a := by
  rcases Int.lt_or_gt_of_ne h with neg | pos
  · have : 0 < (-a) * (-a) := Int.mul_pos (by omega) (by omega)
    rwa [Int.neg_mul_neg] at this
  · exact Int.mul_pos pos pos

/-- Below a solution, a vector that is not a solution has a coordinate that
is still short and whose column points against the residue: the residue has
a negative scalar product with the image of the difference. -/
theorem direction (cols : Vector (Vector Int m) n) (t s : Vector Nat n) (R : Vector Int m)
    (hR : ∀ r : Fin m, R[r] = res cols t r) (hs : Sol cols s) (below : ∀ i : Fin n, t[i] ≤ s[i])
    (off : ∃ r : Fin m, R[r] ≠ 0) : ∃ i : Fin n, t[i] < s[i] ∧ scalar R cols[i] < 0 := by
  apply Classical.byContradiction
  intro none
  let d : Fin n → Int := fun i => (s[i] : Int) - (t[i] : Int)
  have dn (i : Fin n) : 0 ≤ d i := by have := below i; simp only [d]; omega
  have nonneg : 0 ≤ isum (fun i => d i * scalar R cols[i]) := by
    apply isum_nonneg
    intro i
    by_cases short : t[i] < s[i]
    · have : 0 ≤ scalar R cols[i] := by
        apply Classical.byContradiction
        intro neg
        exact none ⟨i, short, by omega⟩
      exact Int.mul_nonneg (dn i) this
    · have zero : d i = 0 := by have := below i; simp only [d]; omega
      simp [zero]
  have diff (r : Fin m) : isum (fun i : Fin n => cols[i][r] * d i) = res cols s r - res cols t r := by
    unfold res
    rw [← isum_sub]
    congr 1
    funext i
    simp only [d, Int.mul_sub]
  have swap : isum (fun i => d i * scalar R cols[i]) = isum (fun r : Fin m => R[r] * (0 - R[r])) := by
    unfold scalar
    have inner (i : Fin n) : d i * isum (fun r : Fin m => R[r] * cols[i][r]) =
        isum (fun r : Fin m => R[r] * (cols[i][r] * d i)) := by
      rw [← isum_mul_left]
      congr 1
      funext r
      ac_rfl
    rw [show (fun i => d i * isum (fun r : Fin m => R[r] * cols[i][r])) = _ from funext inner,
      isum_comm]
    congr 1
    funext r
    rw [isum_mul_left, diff r, hs r, ← hR r]
  have total : isum (fun r : Fin m => R[r] * (0 - R[r])) + isum (fun r : Fin m => R[r] * R[r]) = 0 := by
    rw [← isum_add]
    have zero : (fun r : Fin m => R[r] * (0 - R[r]) + R[r] * R[r]) = fun _ => 0 := by
      funext r
      have cancel : (0 - R[r]) + R[r] = 0 := by omega
      rw [← Int.mul_add, cancel, Int.mul_zero]
    rw [zero, isum_const_zero]
  obtain ⟨r, hr⟩ := off
  have pos := isum_pos (fun r : Fin m => R[r] * R[r]) (fun r => sq_nonneg _) r (sq_pos _ hr)
  omega

/-- A state covers a solution that it can still reach: the solution lies
above it and agrees with it on the frozen coordinates. -/
def Covers (σ : State n m) (s : Vector Nat n) : Prop :=
  (∀ i : Fin n, σ.point[i] ≤ s[i]) ∧ ∀ i : Fin n, σ.frozen[i] = true → σ.point[i] = s[i]

private theorem le_iff (g p : Vector Nat n) : le g p = true ↔ ∀ i : Fin n, g[i] ≤ p[i] := by
  simp [le]

private theorem bump_at (p : Vector Nat n) (i j : Fin n) :
    (bump p i)[j] = if i = j then p[i] + 1 else p[j] := by
  simp only [bump, Fin.getElem_fin, Vector.getElem_set]
  by_cases same : i = j
  · subst same; simp
  · have : i.val ≠ j.val := fun e => same (Fin.ext e)
    simp [same, this]

private theorem not_minimal {found : List (Vector Nat n)} {p : Vector Nat n}
    (h : ¬ minimal found p = true) : ∃ g ∈ found, le g p = true := by
  unfold minimal at h
  rw [List.all_eq_true] at h
  apply Classical.byContradiction
  intro none
  apply h
  intro g hg
  cases e : le g p with
  | false => rfl
  | true => exact (none ⟨g, hg, e⟩).elim

theorem children_ok (cols : Vector (Vector Int m) n) (found : List (Vector Nat n)) (σ : State n m)
    (ok : σ.Ok cols) (is : List (Fin n)) (fz : Vector Bool n) :
    ∀ τ ∈ children cols found σ is fz, τ.Ok cols := by
  induction is generalizing fz with
  | nil => intro τ h; cases h
  | cons i is ih =>
    intro τ h
    simp only [children] at h
    split at h
    · split at h
      · rcases List.mem_cons.mp h with rfl | h
        · refine ⟨fun r => ?_, i, ?_⟩
          · have at_r := ok.1 r
            simp only [Fin.getElem_fin] at at_r
            simp only [shift, Fin.getElem_fin, Vector.getElem_zipWith, res_bump, at_r]
          · rw [bump_at]; simp
        · exact ih _ τ h
      · exact ih _ τ h
    · exact ih _ τ h

/-- If an eligible coordinate is still short of the solution, a child covers
the solution, unless a solution already found lies below it. -/
theorem children_covers (cols : Vector (Vector Int m) n) (found : List (Vector Nat n))
    (σ : State n m) (s : Vector Nat n) (below : ∀ i : Fin n, σ.point[i] ≤ s[i])
    (is : List (Fin n)) (fz : Vector Bool n)
    (agree : ∀ i : Fin n, fz[i] = true → σ.point[i] = s[i])
    (short : ∃ i ∈ is, fz[i] = false ∧ scalar σ.residue cols[i] < 0 ∧ σ.point[i] < s[i]) :
    (∃ g ∈ found, ∀ i : Fin n, g[i] ≤ s[i]) ∨ ∃ τ ∈ children cols found σ is fz, Covers τ s := by
  induction is generalizing fz with
  | nil => obtain ⟨_, h, _⟩ := short; cases h
  | cons i is ih =>
    obtain ⟨k, hk, free, down, lt⟩ := short
    simp only [children]
    split
    next eligible =>
      by_cases here : σ.point[i] < s[i]
      · have fits (j : Fin n) : (bump σ.point i)[j] ≤ s[j] := by
          rw [bump_at]
          split
          · next e => subst e; omega
          · exact below j
        split
        next keep =>
          refine .inr ⟨_, List.mem_cons_self, fits, fun j hj => ?_⟩
          rw [bump_at]
          have ne : i ≠ j := fun e => by
            subst e
            rw [eligible.1] at hj
            cases hj
          simp only [ne, ite_false]
          exact agree j hj
        next drop =>
          obtain ⟨g, hg, under⟩ := not_minimal drop
          exact .inl ⟨g, hg, fun j => Nat.le_trans ((le_iff _ _).mp under j) (fits j)⟩
      · have same : σ.point[i] = s[i] := by have := below i; omega
        have next : ∃ k ∈ is, (fz.set i true)[k] = false ∧ scalar σ.residue cols[k] < 0 ∧
            σ.point[k] < s[k] := by
          have ne : k ≠ i := fun e => by subst e; omega
          refine ⟨k, ?_, ?_, down, lt⟩
          · rcases List.mem_cons.mp hk with e | h
            · exact (ne e).elim
            · exact h
          · have : i.val ≠ k.val := fun e => ne (Fin.ext e.symm)
            simp only [Fin.getElem_fin, Vector.getElem_set, this, ite_false]
            exact free
        have frozen (j : Fin n) (hj : (fz.set i true)[j] = true) : σ.point[j] = s[j] := by
          by_cases e : i = j
          · subst e; exact same
          · have : i.val ≠ j.val := fun h => e (Fin.ext h)
            simp only [Fin.getElem_fin, Vector.getElem_set, this, ite_false] at hj
            exact agree j hj
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

/-- A state that covers a solution is viable: the difference to the solution
balances every equation, and it vanishes on the frozen coordinates. -/
theorem viable_of_covers (cols : Vector (Vector Int m) n) (σ : State n m) (ok : σ.Ok cols)
    (s : Vector Nat n) (hs : Sol cols s) (cov : Covers σ s) : viable cols σ = true := by
  apply decide_eq_true
  intro r
  apply Classical.byContradiction
  intro bad
  have off : σ.residue[r] ≠ 0 := fun z => bad (.inl z)
  have stuck (i : Fin n) (free : σ.frozen[i] = false) : 0 ≤ σ.residue[r] * cols[i][r] := by
    apply Classical.byContradiction
    intro neg
    exact bad (.inr ⟨i, free, by omega⟩)
  let d : Fin n → Int := fun i => (s[i] : Int) - (σ.point[i] : Int)
  have nonneg : 0 ≤ isum (fun i => σ.residue[r] * (cols[i][r] * d i)) := by
    apply isum_nonneg
    intro i
    cases free : σ.frozen[i] with
    | true =>
      have same := cov.2 i free
      have zero : d i = 0 := by simp only [d]; omega
      simp [zero]
    | false =>
      have dn : 0 ≤ d i := by have := cov.1 i; simp only [d]; omega
      have := Int.mul_nonneg (stuck i free) dn
      rwa [Int.mul_assoc] at this
  have diff : isum (fun i : Fin n => cols[i][r] * d i) = res cols s r - res cols σ.point r := by
    unfold res
    rw [← isum_sub]
    congr 1
    funext i
    simp only [d, Int.mul_sub]
  rw [isum_mul_left, diff, hs r, ← ok.1 r] at nonneg
  have pos := sq_pos _ off
  have flip : σ.residue[r] * (0 - σ.residue[r]) = -(σ.residue[r] * σ.residue[r]) := by
    rw [Int.mul_sub]; simp
  omega

/-- A nonzero solution with no other nonzero solution below it. -/
def Minimal (cols : Vector (Vector Int m) n) (s : Vector Nat n) : Prop :=
  Sol cols s ∧ Nonzero s ∧ ∀ y, Sol cols y → Nonzero y → (∀ i : Fin n, y[i] ≤ s[i]) → y = s

private theorem zero_iff (cols : Vector (Vector Int m) n) (σ : State n m) (ok : σ.Ok cols) :
    (∀ r : Fin m, σ.residue[r] = 0) ↔ Sol cols σ.point := by
  constructor
  · intro h r; rw [← ok.1 r]; exact h r
  · intro h r; rw [ok.1 r]; exact h r

/-- A completed search returns nonzero solutions only, and every minimal
solution that some state of the stack covers. -/
theorem search_spec (cols : Vector (Vector Int m) n) (fuel : Nat) (stack : List (State n m))
    (found out : List (Vector Nat n)) (done : search cols fuel stack found = some out)
    (states : ∀ σ ∈ stack, σ.Ok cols) (sols : ∀ g ∈ found, Sol cols g ∧ Nonzero g) :
    (∀ g ∈ out, Sol cols g ∧ Nonzero g) ∧
    ∀ s, Minimal cols s → (s ∈ found ∨ ∃ σ ∈ stack, Covers σ s) → s ∈ out := by
  induction fuel generalizing stack found with
  | zero =>
    cases stack with
    | nil =>
      obtain rfl : found = out := by simpa [search] using done
      refine ⟨sols, fun s _ h => ?_⟩
      rcases h with h | ⟨_, h, _⟩
      · exact h
      · cases h
    | cons σ stack => simp [search] at done
  | succ fuel ih =>
    cases stack with
    | nil =>
      obtain rfl : found = out := by simpa [search] using done
      refine ⟨sols, fun s _ h => ?_⟩
      rcases h with h | ⟨_, h, _⟩
      · exact h
      · cases h
    | cons σ stack =>
      have okσ := states σ List.mem_cons_self
      have rest (τ) (h : τ ∈ stack) := states τ (List.mem_cons_of_mem _ h)
      simp only [search] at done
      split at done
      next solved =>
        have sol : Sol cols σ.point := (zero_iff cols σ okσ).mp (of_decide_eq_true solved)
        have grown : ∀ g ∈ (if minimal found σ.point then σ.point :: found else found),
            Sol cols g ∧ Nonzero g := by
          intro g hg
          split at hg
          · rcases List.mem_cons.mp hg with rfl | hg
            · exact ⟨sol, okσ.2⟩
            · exact sols g hg
          · exact sols g hg
        obtain ⟨sound, complete⟩ := ih stack _ done rest grown
        refine ⟨sound, fun s hs h => complete s hs ?_⟩
        rcases h with h | ⟨τ, hτ, cov⟩
        · left
          split
          · exact List.mem_cons_of_mem _ h
          · exact h
        · rcases List.mem_cons.mp hτ with rfl | hτ
          · have same : τ.point = s := hs.2.2 _ sol okσ.2 cov.1
            left
            split
            · exact same ▸ List.mem_cons_self
            · next dominated =>
              obtain ⟨g, hg, under⟩ := not_minimal dominated
              have eq : g = s := hs.2.2 g (sols g hg).1 (sols g hg).2
                (fun i => same ▸ (le_iff _ _).mp under i)
              exact eq ▸ hg
          · exact .inr ⟨τ, hτ, cov⟩
      next open_ =>
       split at done
       next alive =>
        have kids := children_ok cols found σ okσ (List.finRange n) σ.frozen
        have all : ∀ τ ∈ (children cols found σ (List.finRange n) σ.frozen).reverse ++ stack,
            τ.Ok cols := by
          intro τ h
          rcases List.mem_append.mp h with h | h
          · exact kids τ (List.mem_reverse.mp h)
          · exact rest τ h
        obtain ⟨sound, complete⟩ := ih _ found done all sols
        refine ⟨sound, fun s hs h => complete s hs ?_⟩
        rcases h with h | ⟨τ, hτ, cov⟩
        · exact .inl h
        · rcases List.mem_cons.mp hτ with rfl | hτ
          · have off : ∃ r : Fin m, τ.residue[r] ≠ 0 := by
              apply Classical.byContradiction
              intro none
              apply open_
              apply decide_eq_true
              intro r
              apply Classical.byContradiction
              intro ne
              exact none ⟨r, ne⟩
            obtain ⟨i, lt, down⟩ := direction cols τ.point s τ.residue okσ.1 hs.1 cov.1 off
            have free : τ.frozen[i] = false := by
              cases h : τ.frozen[i] with
              | false => rfl
              | true => have := cov.2 i h; omega
            rcases children_covers cols found τ s cov.1 (List.finRange n) τ.frozen cov.2
              ⟨i, List.mem_finRange i, free, down, lt⟩ with ⟨g, hg, under⟩ | ⟨υ, hυ, c⟩
            · exact .inl ((hs.2.2 g (sols g hg).1 (sols g hg).2 under) ▸ hg)
            · exact .inr ⟨υ, List.mem_append_left _ (List.mem_reverse.mpr hυ), c⟩
          · exact .inr ⟨τ, List.mem_append_right _ hτ, cov⟩
       next dead =>
        obtain ⟨sound, complete⟩ := ih stack found done rest sols
        refine ⟨sound, fun s hs h => complete s hs ?_⟩
        rcases h with h | ⟨τ, hτ, cov⟩
        · exact .inl h
        · rcases List.mem_cons.mp hτ with rfl | hτ
          · exact (dead (viable_of_covers cols τ okσ s hs.1 cov)).elim
          · exact .inr ⟨τ, hτ, cov⟩

/-- The matrix of a list of rows, by columns. -/
def columns (rows : List (Row n)) : Vector (Vector Int rows.length) n :=
  Vector.ofFn fun i => Vector.ofFn fun r => ((rows.get r).pos i : Int) - ((rows.get r).neg i : Int)

/-- One state per unit vector. The state of a coordinate keeps the earlier
coordinates frozen at zero. The last coordinate comes first: its state only
reaches its own multiples. -/
def start (cols : Vector (Vector Int m) n) : List (State n m) :=
  (List.finRange n).reverse.map fun i =>
    ⟨Vector.ofFn fun j => if j = i then 1 else 0, cols[i], Vector.ofFn fun j => decide (j.val < i.val)⟩

def view (v : Vector Nat n) : Vec n := fun i => v[i]

private theorem res_columns (rows : List (Row n)) (v : Vector Nat n) (r : Fin rows.length) :
    res (columns rows) v r =
      ((dot (rows.get r).pos (view v) : Nat) : Int) - ((dot (rows.get r).neg (view v) : Nat) : Int) := by
  unfold res dot
  rw [cast_total, cast_total, ← isum_sub]
  congr 1
  funext i
  simp only [columns, Fin.getElem_fin, Vector.getElem_ofFn, view, Int.natCast_mul, Int.sub_mul]

theorem sol_iff (rows : List (Row n)) (v : Vector Nat n) :
    Sol (columns rows) v ↔ SystemHolds rows (view v) := by
  constructor
  · intro h r hr
    obtain ⟨j, rfl⟩ := List.get_of_mem hr
    have := h j
    rw [res_columns] at this
    unfold Row.Holds
    omega
  · intro h r
    rw [res_columns]
    have := h _ (List.get_mem rows r)
    unfold Row.Holds at this
    omega

theorem view_ofFn (x : Vec n) : view (Vector.ofFn x) = x := by
  funext i
  simp [view]

private theorem ofFn_view (v : Vector Nat n) : Vector.ofFn (view v) = v := by
  apply Vector.ext
  intro i hi
  simp [view]

theorem minimal_iff (rows : List (Row n)) (v : Vector Nat n) :
    Minimal (columns rows) v ↔ Irreducible rows (view v) := by
  constructor
  · rintro ⟨sol, ⟨i, hi⟩, least⟩
    refine ⟨(sol_iff rows v).mp sol, ⟨i, hi⟩, fun y hy ⟨j, hj⟩ under => ?_⟩
    have := least (Vector.ofFn y) ((sol_iff rows _).mpr (by rwa [view_ofFn]))
      ⟨j, by simpa using hj⟩ (fun k => by simpa [view] using under k)
    rw [← this, view_ofFn]
  · rintro ⟨sol, ⟨i, hi⟩, least⟩
    refine ⟨(sol_iff rows v).mpr sol, ⟨i, hi⟩, fun y hy ⟨j, hj⟩ under => ?_⟩
    have := least (view y) ((sol_iff rows y).mp hy) ⟨j, hj⟩ under
    rw [← ofFn_view y, this, ofFn_view]

private theorem start_ok (cols : Vector (Vector Int m) n) : ∀ σ ∈ start cols, σ.Ok cols := by
  intro σ h
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp h
  refine ⟨fun r => ?_, i, by simp⟩
  unfold res
  have term (j : Fin n) : cols[j][r] * (((Vector.ofFn fun j : Fin n => if j = i then 1 else 0)[j] : Nat) : Int) =
      if j = i then cols[i][r] else 0 := by
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
    by_cases e : j = i
    · subst e; simp
    · simp [e]
  rw [show (fun j : Fin n => cols[j][r] * (((Vector.ofFn fun j : Fin n => if j = i then 1 else 0)[j] : Nat) : Int)) = _
    from funext term, isum_single]

private theorem start_covers (cols : Vector (Vector Int m) n) (s : Vector Nat n) (nz : Nonzero s) :
    ∃ σ ∈ start cols, Covers σ s := by
  classical
  -- The first positive coordinate of the solution.
  have first : ∃ i : Fin n, 0 < s[i] ∧ ∀ j : Fin n, j.val < i.val → s[j] = 0 := by
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
  obtain ⟨i, pos, before⟩ := first
  simp only [Fin.getElem_fin] at pos before
  refine ⟨_, List.mem_map.mpr ⟨i, List.mem_reverse.mpr (List.mem_finRange i), rfl⟩,
    fun j => ?_, fun j hj => ?_⟩
  · simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
    split
    · next e => subst e; omega
    · omega
  · simp only [Fin.getElem_fin, Vector.getElem_ofFn, decide_eq_true_eq] at hj
    have ne : j ≠ i := fun e => by subst e; omega
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, ne, ite_false]
    exact (before j hj).symm

/-- The irreducible solutions of the system, or `none` when the search does
not finish within the step budget. -/
def basis? (fuel : Nat) (rows : List (Row n)) : Option (List (Vec n)) :=
  (search (columns rows) fuel (start (columns rows)) []).map fun found => minimize (found.map view)

theorem mem_basis {fuel : Nat} {rows : List (Row n)} {gs : List (Vec n)}
    (h : basis? fuel rows = some gs) (x : Vec n) : x ∈ gs ↔ Irreducible rows x := by
  unfold basis? at h
  cases done : search (columns rows) fuel (start (columns rows)) [] with
  | none => simp [done] at h
  | some found =>
    obtain rfl : minimize (found.map view) = gs := by simpa [done] using h
    obtain ⟨sound, complete⟩ := search_spec _ _ _ _ _ done (start_ok _) (by simp)
    have solves (y) (hy : y ∈ found.map view) : SystemHolds rows y ∧ ∃ i, 0 < y i := by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
      exact ⟨(sol_iff rows v).mp (sound v hv).1, (sound v hv).2⟩
    have present (y : Vec n) (irr : Irreducible rows y) : y ∈ found.map view := by
      have least : Minimal (columns rows) (Vector.ofFn y) :=
        (minimal_iff rows _).mpr (by rwa [view_ofFn])
      have := complete _ least (.inr (start_covers _ _ least.2.1))
      exact List.mem_map.mpr ⟨_, this, view_ofFn y⟩
    rw [mem_minimize]
    constructor
    · rintro ⟨mem, nz, least⟩
      refine ⟨(solves x mem).1, nz, fun y hy ynz under => ?_⟩
      -- Some irreducible solution lies below `y`, and it was found.
      have gen := (generate_correct rows y).mp hy
      obtain ⟨z, hz, znz, le⟩ := dominating (generate rows) y gen ynz
      have zx := least z (present z ((mem_generate rows z).mp hz)) znz
        (fun i => Nat.le_trans (le i) (under i))
      subst zx
      funext i
      exact Nat.le_antisymm (under i) (le i)
    · rintro irr
      exact ⟨present x irr, irr.2.1, fun y hy ynz under => irr.2.2 y (solves y hy).1 ynz under⟩

theorem basis_correct {fuel : Nat} {rows : List (Row n)} {gs : List (Vec n)}
    (h : basis? fuel rows = some gs) : BasisCorrect rows gs :=
  (generate_correct rows).of_mem fun g => (mem_basis h g).trans (mem_generate rows g).symm

end Tamarin.ACBasis.Hilbert

namespace Tamarin.ACBasis

/-- Steps granted to the direct search before the row-by-row generation takes over. -/
def hilbertFuel : Nat := 100000000

/-! A merge sort by recursion on a step count. `List.mergeSort` is defined by
well-founded recursion, which the kernel does not evaluate, and the proofs by
`decide` that run the unifier need the basis to reduce. Every loop carries its
result, so the stack does not grow with the list. -/
section Merging
variable {α : Type}

def mergeLoop (le : α → α → Bool) : Nat → List α → List α → List α → List α
  | 0, xs, ys, acc => acc.reverse ++ (xs ++ ys)
  | _ + 1, [], ys, acc => acc.reverse ++ ys
  | _ + 1, xs, [], acc => acc.reverse ++ xs
  | fuel + 1, x :: xs, y :: ys, acc =>
    if le x y then mergeLoop le fuel xs (y :: ys) (x :: acc)
    else mergeLoop le fuel (x :: xs) ys (y :: acc)

theorem mem_mergeLoop (le : α → α → Bool) (fuel : Nat) (xs ys acc : List α) (a : α) :
    a ∈ mergeLoop le fuel xs ys acc ↔ a ∈ acc ∨ a ∈ xs ∨ a ∈ ys := by
  induction fuel generalizing xs ys acc with
  | zero => simp [mergeLoop]
  | succ fuel ih =>
    cases xs with
    | nil => simp [mergeLoop]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeLoop]
      | cons y ys =>
        simp only [mergeLoop]
        split
        · rw [ih]; simp only [List.mem_cons]; grind
        · rw [ih]; simp only [List.mem_cons]; grind

/-- Merge the runs two by two. -/
def mergePairs (le : α → α → Bool) : List (List α) → List (List α) → List (List α)
  | a :: b :: rest, done => mergePairs le rest (mergeLoop le (a.length + b.length) a b [] :: done)
  | [a], done => (a :: done).reverse
  | [], done => done.reverse

theorem mem_mergePairs (le : α → α → Bool) (runs done : List (List α)) (a : α) :
    (∃ l ∈ mergePairs le runs done, a ∈ l) ↔ (∃ l ∈ runs, a ∈ l) ∨ ∃ l ∈ done, a ∈ l := by
  induction runs, done using mergePairs.induct le with
  | case1 x y rest done ih =>
    simp only [mergePairs, ih, List.mem_cons, exists_eq_or_imp, mem_mergeLoop]
    simp only [List.not_mem_nil, false_or]
    grind
  | case2 x done => simp [mergePairs]; grind
  | case3 done => simp [mergePairs]

def mergeRounds (le : α → α → Bool) : Nat → List (List α) → List (List α)
  | 0, runs => runs
  | _ + 1, [run] => [run]
  | fuel + 1, runs => mergeRounds le fuel (mergePairs le runs [])

theorem mem_mergeRounds (le : α → α → Bool) (fuel : Nat) (runs : List (List α)) (a : α) :
    (∃ l ∈ mergeRounds le fuel runs, a ∈ l) ↔ ∃ l ∈ runs, a ∈ l := by
  induction fuel, runs using mergeRounds.induct le with
  | case1 runs => rfl
  | case2 fuel run => rfl
  | case3 fuel runs _ ih =>
    rw [mergeRounds, ih, mem_mergePairs]
    · simp
    · assumption

/-- The elements in an order that `le` sorts when it is a total preorder. -/
def sortBy (le : α → α → Bool) (xs : List α) : List α :=
  (mergeRounds le xs.length (xs.map fun x => [x])).flatten

theorem mem_sortBy (le : α → α → Bool) (xs : List α) (a : α) : a ∈ sortBy le xs ↔ a ∈ xs := by
  simp only [sortBy, List.mem_flatten, mem_mergeRounds, List.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, mem⟩
    obtain rfl := List.mem_singleton.mp mem
    exact hx
  · exact fun h => ⟨[a], ⟨a, h, rfl⟩, List.mem_singleton_self a⟩

end Merging

/-- Lexicographic order on coordinate lists. -/
def lexLe : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && lexLe as bs)

/-- Columns beyond this number are searched without merging equal ones. -/
def quotientWidth : Nat := 128

open ACFeasibility.ColumnQuotient in
/-- The minimal solutions through the classes of equal columns. A solution is
minimal exactly when its class sums are minimal for the system with one column
per class, so the search runs once per class and each of its solutions is
distributed over the columns of the classes. `none` when all columns differ,
when there are too many of them, when every coefficient is zero or one, so
that the direct search is short, or when the search does not finish. -/
def quotientBasis? (fuel : Nat) {n} (rows : List (Row n)) : Option (List (Vec n)) :=
  if n ≤ quotientWidth ∧ (rows.any fun r => !r.isUnit) = true then
    let reps := representatives rows
    if reps.length < n then
      match Distributed.classify rows reps with
      | none => none
      | some cls =>
        (Hilbert.basis? fuel (projected rows reps)).map fun qs =>
          -- A distributed vector is a chain of closures as long as the vector.
          -- Its coordinates are stored first, so that later reads do not walk it.
          ((qs.flatMap (Distributed.plan n fun i => cls[i]).draw).map Vector.ofFn).map Hilbert.view
    else none
  else none

open ACFeasibility.ColumnQuotient in
theorem mem_quotientBasis {fuel : Nat} {n} {rows : List (Row n)} {gs : List (Vec n)}
    (h : quotientBasis? fuel rows = some gs) (x : Vec n) : x ∈ gs ↔ x ∈ generate rows := by
  unfold quotientBasis? at h
  split at h
  · dsimp only at h
    split at h
    · obtain ⟨cls, classified, profiles, -⟩ := Distributed.layout rows
      rw [classified] at h
      cases found : Hilbert.basis? fuel (projected rows (representatives rows)) with
      | none => simp [found] at h
      | some qs =>
        simp only [found, Option.map_some, Option.some.injEq] at h
        subst h
        have same : (Hilbert.view ∘ Vector.ofFn : Vec n → Vec n) = id :=
          funext fun g => Hilbert.view_ofFn g
        rw [List.map_map, same, List.map_id]
        have shape : projected rows (representatives rows) =
            rows.map (restrict (representatives rows).get) := by
          simp [projected, show (representatives rows).get =
            (fun j : Fin (representatives rows).length => (representatives rows)[j.val]) from rfl]
        rw [Distributed.generate_iff rows (representatives rows).get (fun i => cls[i]) profiles x,
          ← shape, mem_generate, ← Hilbert.mem_basis found]
        simp only [List.mem_flatMap, Distributed.mem_draw]
        exact ⟨fun ⟨_, m, e⟩ => e ▸ m, fun m => ⟨_, m, rfl⟩⟩
    · cases h
  · cases h

/-- A basis of the system: the minimal solutions when the direct search
finishes, and the row-by-row generators otherwise. The minimal solutions are
listed in increasing lexicographic order of their coordinates, so that the order
does not depend on the path of the search. Equal columns are merged for
the search when there are any. -/
def hilbert {n} (rows : List (Row n)) : List (Vec n) :=
  match (quotientBasis? hilbertFuel rows).orElse fun _ => Hilbert.basis? hilbertFuel rows with
  | some gs => (sortBy (fun a b => lexLe a.1 b.1) (gs.map fun g => (List.ofFn g, g))).map (·.2)
  | none => generateFast rows

theorem hilbert_correct {n} (rows : List (Row n)) : BasisCorrect rows (hilbert rows) := by
  unfold hilbert
  split
  · next gs h =>
    have members : ∀ g, g ∈ gs ↔ g ∈ generate rows := by
      cases merged : quotientBasis? hilbertFuel rows with
      | some qs =>
        obtain rfl : qs = gs := by simpa [merged] using h
        exact mem_quotientBasis merged
      | none =>
        have direct : Hilbert.basis? hilbertFuel rows = some gs := by simpa [merged] using h
        exact fun g => (Hilbert.mem_basis direct g).trans (mem_generate rows g).symm
    apply ((generate_correct rows).of_mem members).of_mem
    intro g
    simp only [List.mem_map, mem_sortBy]
    constructor
    · rintro ⟨⟨_, x⟩, ⟨y, hy, eq⟩, rfl⟩
      obtain rfl : y = x := (Prod.mk.inj eq).2
      exact hy
    · exact fun hg => ⟨(List.ofFn g, g), ⟨g, hg, rfl⟩, rfl⟩
  · exact generateFast_correct rows

-- Callers use the basis through `hilbert_correct` only. Unfolding it would
-- start the search inside the elaborator.
attribute [irreducible] hilbert

end Tamarin.ACBasis
