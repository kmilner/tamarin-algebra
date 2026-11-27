import Std

/-! Executable numeric reference search for homogeneous AC systems. -/
namespace Tamarin.ACBasis

abbrev Vec (n : Nat) := Fin n → Nat

/-- Finite sum over all coordinates. -/
def total {n} (v : Vec n) := (List.ofFn v).sum

private theorem foldl_total {n} (v : Vec n) (a : Nat) :
    Fin.foldl n (fun acc i => acc + v i) a = a + total v := by
  induction n generalizing a with
  | zero => simp [total]
  | succ n ih =>
    rw [Fin.foldl_succ, ih]
    simp only [total, List.ofFn_succ, List.sum_cons]
    omega

/-- `total` as a loop over the coordinates. Summing the list of coordinates
recurses once per coordinate. -/
private def totalLoop {n} (v : Vec n) : Nat := Fin.foldl n (fun acc i => acc + v i) 0

@[csimp] private theorem total_eq_loop : @total = @totalLoop := by
  funext n v
  simp [totalLoop, foldl_total]

def dot {n} (v w : Vec n) := total (fun i => v i * w i)

def spike {n} (j : Fin n) (m : Nat) : Vec n := fun i => if i = j then m else 0

/-- A single row with cancelled coefficients, so each coordinate contributes
to at most one side. -/
structure Row (n : Nat) where
  pos : Vec n
  neg : Vec n
  disjoint : ∀ i, pos i = 0 ∨ neg i = 0

def Row.Holds {n} (r : Row n) (x : Vec n) := dot r.pos x = dot r.neg x

def Row.cap {n} (r : Row n) := (1 :: (List.ofFn r.pos ++ List.ofFn r.neg)).max (by simp)

def Row.bound {n} (r : Row n) := r.cap + n * (r.cap * r.cap)

/-- On a unit-weight side one can spend individual occurrences to balance
one item from the other side. A generator then uses at most the largest
coefficient in any coordinate. Neutral coordinates need at most one. -/
def Row.unitSide {n} (r : Row n) : Prop :=
  (∀ i, r.pos i ≤ 1) ∨ (∀ i, r.neg i ≤ 1)

instance {n} (r : Row n) : Decidable r.unitSide :=
  inferInstanceAs (Decidable ((∀ i, r.pos i ≤ 1) ∨ (∀ i, r.neg i ≤ 1)))

def Row.limits {n} (r : Row n) : Vec n :=
  let cap := r.cap
  let bound := cap + n * (cap * cap)
  let active := if r.unitSide then cap else bound
  fun i => if r.pos i == 0 && r.neg i == 0 then 1 else active

/-- Prepending a coordinate has the same pointwise semantics as finitary case analysis. -/
abbrev prepend {n} (h : Nat) (v : Vec n) : Vec (n+1) := Fin.cases h v

private def prependDirect {n} (h : Nat) (v : Vec n) : Vec (n+1)
  | ⟨0,_⟩ => h
  | ⟨j+1,lt⟩ => v ⟨j,Nat.lt_of_succ_lt_succ lt⟩

/-- `Fin.cases` uses induction on the index. Direct case analysis evaluates
just the requested coordinate of a nested coefficient vector. -/
@[csimp] theorem prepend_eq_direct : @prepend = @prependDirect := by
  funext n h v i
  cases i using Fin.cases <;> rfl

def box : (n : Nat) → Vec n → List (Vec n)
  | 0, _ => [Fin.elim0]
  | n+1, limits =>
    let tail := box n (fun i => limits i.succ)
    (List.range (limits 0 + 1)).flatMap (fun h => tail.map (prepend h))

def Row.generators {n} (r : Row n) : List (Vec n) :=
  (box n r.limits).filter fun v => dot r.pos v == dot r.neg v && (List.ofFn v).any (0 < ·)

/-- Read a vector from a table. A `Vec` built by `prepend`, `mix` or a row
constructor is a closure that recomputes each coordinate on every access, so
the tables are built as data first and only then wrapped. -/
private def reads {n} (table : Vector Nat n) : Vec n := fun i => table[i]

private theorem reads_ofFn {n} (v : Vec n) : reads (Vector.ofFn v) = v := by
  funext i
  simp [reads]

private theorem map_reads {n} (vs : List (Vec n)) : (vs.map Vector.ofFn).map reads = vs := by
  rw [List.map_map, show reads ∘ Vector.ofFn = (id : Vec n → Vec n) from funext reads_ofFn, List.map_id]

private def Row.generatorsStored {n} (r : Row n) : List (Vec n) :=
  let pos := Vector.ofFn r.pos
  let neg := Vector.ofFn r.neg
  (((box n r.limits).map Vector.ofFn).map reads).filter fun v =>
    dot (reads pos) v == dot (reads neg) v && (List.ofFn v).any (0 < ·)

@[csimp] theorem Row.generators_eq_stored : @Row.generators = @Row.generatorsStored := by
  funext n r
  simp only [Row.generators, Row.generatorsStored, map_reads, reads_ofFn]

def Row.boxSize {n} (r : Row n) := (List.ofFn (fun i => r.limits i + 1)).prod

/-- Nonnegative linear combination of a finite generator table. -/
def mix {k n} (g : Fin k → Vec n) (c : Vec k) : Vec n := fun i => dot (fun j => g j i) c

/-- Coefficients common to the two sides cancel coordinate by coordinate. -/
def Row.ofWeights {n} (p q : Vec n) : Row n where
  pos i := p i - q i
  neg i := q i - p i
  disjoint i := by omega

/-- The row induced on coefficients of a previous generator table. -/
def Row.pullback {k n} (r : Row n) (g : Fin k → Vec n) : Row k :=
  .ofWeights (fun i => dot r.pos (g i)) (fun i => dot r.neg (g i))

private def Row.pullbackStored {k n} (r : Row n) (g : Fin k → Vec n) : Row k :=
  let pos := Vector.ofFn r.pos
  let neg := Vector.ofFn r.neg
  let left := Vector.ofFn fun i => dot (reads pos) (g i)
  let right := Vector.ofFn fun i => dot (reads neg) (g i)
  .ofWeights (reads left) (reads right)

@[csimp] theorem Row.pullback_eq_stored : @Row.pullback = @Row.pullbackStored := by
  funext k n r g
  simp only [Row.pullback, Row.pullbackStored, reads_ofFn]

def lift {k n} (g : Fin k → Vec n) (coeffs : List (Vec k)) := coeffs.map (mix g)

private def liftStored {k n} (g : Fin k → Vec n) (coeffs : List (Vec k)) :=
  (coeffs.map fun c => Vector.ofFn (mix g c)).map reads

@[csimp] theorem lift_eq_stored : @lift = @liftStored := by
  funext k n g coeffs
  have split : (coeffs.map fun c => Vector.ofFn (mix g c)) = (coeffs.map (mix g)).map Vector.ofFn := by
    rw [List.map_map]; rfl
  simp only [lift, liftStored, split, map_reads]

def intersect {n} (r : Row n) (gs : List (Vec n)) :=
  lift gs.get (r.pullback gs.get).generators

/-- Index the generator table by position instead of walking the list. -/
private def intersectStored {n} (r : Row n) (gs : List (Vec n)) :=
  let table := gs.toArray
  let g : Fin gs.length → Vec n := fun j => table[j.val]'(by simp [table])
  lift g (r.pullback g).generators

@[csimp] theorem intersect_eq_stored : @intersect = @intersectStored := by
  funext n r gs
  have same : (fun j : Fin gs.length => gs.toArray[j.val]'(by simp)) = gs.get := by
    funext j
    simp
  simp only [intersect, intersectStored, same]

def units (n : Nat) := List.ofFn (fun i : Fin n => spike i 1)

private instance vecDecEq {n} : DecidableEq (Vec n) := fun a b =>
  decidable_of_iff (∀ i, a i = b i) funext_iff.symm

/-- Discard zero, repetitions and vectors dominated by a smaller nonzero
solution in the table. Doing this between row intersections bounds the next
coefficient dimension by the number of distinct irreducible generators. -/
def minimize {n} (gs : List (Vec n)) : List (Vec n) :=
  (gs.filter fun x => decide (∃ i, 0 < x i) &&
    !gs.any (fun y => decide ((∃ i, 0 < y i) ∧ (∀ i, y i ≤ x i) ∧ y ≠ x))).eraseDups

/-- A vector as a table, with whether it is nonzero and its first and last
nonzero positions. -/
private structure Entry (n : Nat) where
  data : Vector Nat n
  live : Bool
  lo : Nat
  hi : Nat

private def entry {n} (x : Vec n) : Entry n :=
  let data := Vector.ofFn x
  let support := (List.range n).filter fun i => 0 < data.toArray.getD i 0
  ⟨data, decide (∃ i, 0 < x i), support.head?.getD 0, support.getLast?.getD 0⟩

private def probe {n} (d e : Entry n) (i : Nat) : Bool :=
  d.data.toArray.getD i 0 ≤ e.data.toArray.getD i 0

/-- The first vector is nonzero, below the second and different from it. The
two probes reject most pairs before the coordinates are compared. -/
private def below {n} (d e : Entry n) : Bool :=
  d.live && probe d e d.lo && probe d e d.hi &&
    decide (∀ i : Fin n, d.data[i] ≤ e.data[i]) && d.data != e.data

private theorem below_entry {n} (y x : Vec n) :
    below (entry y) (entry x) = decide ((∃ i, 0 < y i) ∧ (∀ i, y i ≤ x i) ∧ y ≠ x) := by
  have at_probe (i : Nat) (le : ∀ j, y j ≤ x j) : probe (entry y) (entry x) i = true := by
    simp only [probe, entry]
    by_cases h : i < n
    · simpa [Array.getD, h] using le ⟨i,h⟩
    · simp [Array.getD, h]
  have data_eq : ((entry y).data != (entry x).data) = decide (y ≠ x) := by
    simp only [entry, bne, decide_not]
    congr 1
    by_cases same : y = x
    · subst same; simp
    · have : Vector.ofFn y ≠ Vector.ofFn x := fun h => same (by
        funext i
        have := congrArg (fun v : Vector Nat n => v[i]) h
        simpa using this)
      simp [same, this]
  by_cases le : ∀ i, y i ≤ x i
  · simp only [below, at_probe _ le, data_eq, Bool.and_true]
    simp [entry, le]
  · have off : decide (∀ i : Fin n, (entry y).data[i] ≤ (entry x).data[i]) = false := by
      simpa [entry] using le
    unfold below
    rw [off]
    simp [le]

private theorem filter_paired {α β : Type} (f : α → β) (q : β → Bool) (xs : List α) :
    ((xs.map fun x => (x, f x)).filter fun z => q z.2).map (·.1) = xs.filter fun x => q (f x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.filter_cons]
    split <;> simp [ih]

/-- Two tables of the same vector. The first and last nonzero positions are
compared before the coordinates. -/
private def sameEntry {n} (d e : Entry n) : Bool :=
  d.lo == e.lo && d.hi == e.hi && d.data == e.data

private theorem sameEntry_entry {n} (a b : Vec n) : sameEntry (entry a) (entry b) = (a == b) := by
  by_cases same : a = b
  · subst same
    simp [sameEntry]
  · have differ : Vector.ofFn a ≠ Vector.ofFn b := fun h => same (by
      funext i
      have := congrArg (fun v : Vector Nat n => v[i]) h
      simpa using this)
    have off : (a == b) = false := by simpa using same
    have data : ((entry a).data == (entry b).data) = false := by simpa [entry] using differ
    rw [sameEntry, data, off, Bool.and_false]

/-- `List.eraseDups` on vectors paired with their tables. -/
private def distinctLoop {n} : List (Vec n × Entry n) → List (Vec n × Entry n) → List (Vec n)
  | [], kept => kept.reverse.map (·.1)
  | p :: ps, kept =>
    if kept.any (fun q => sameEntry p.2 q.2) then distinctLoop ps kept
    else distinctLoop ps (p :: kept)

private theorem distinctLoop_eq {n} (xs acc : List (Vec n)) :
    distinctLoop (xs.map fun g => (g, entry g)) (acc.map fun g => (g, entry g)) =
      List.eraseDupsBy.loop (· == ·) xs acc := by
  induction xs generalizing acc with
  | nil =>
    have back : (acc.map fun g => (g, entry g)).map (·.1) = acc := by
      rw [List.map_map]
      exact List.map_id' acc
    simp only [List.map_nil, distinctLoop, List.eraseDupsBy.loop, List.map_reverse, back]
  | cons a as ih =>
    have test : (acc.map fun g => (g, entry g)).any (fun q => sameEntry (entry a) q.2) =
        acc.any (fun b => a == b) := by
      rw [List.any_map]
      congr 1
      funext b
      exact sameEntry_entry a b
    simp only [List.map_cons, distinctLoop, List.eraseDupsBy.loop, test]
    cases seen : acc.any (fun b => a == b) with
    | true => simpa using ih acc
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih (a :: acc)

/-- `minimize` on tables: each vector is tabulated once, and a pair is
compared coordinate by coordinate only after two probes, both for dominance
and for repetition. The vectors are paired with their tables by a map, whose
stack does not grow with the list. -/
private def minimizeTabled {n} (gs : List (Vec n)) : List (Vec n) :=
  let ps := gs.map fun g => (g, entry g)
  let es := ps.map (·.2)
  distinctLoop (ps.filter fun z => z.2.live && !es.any (fun d => below d z.2)) []

@[csimp] theorem minimize_eq_tabled : @minimize = @minimizeTabled := by
  funext n gs
  simp only [minimize, minimizeTabled]
  have es : (gs.map fun g => (g, entry g)).map (·.2) = gs.map entry := by
    rw [List.map_map]; rfl
  have paired (q : Entry n → Bool) (xs : List (Vec n)) :
      (xs.map fun g => (g, entry g)).filter (fun z => q z.2) =
        (xs.filter fun g => q (entry g)).map fun g => (g, entry g) := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, List.filter_cons]
      split <;> simp [ih]
  rw [es, paired (fun e => e.live && !(gs.map entry).any (fun d => below d e)) gs]
  have start := distinctLoop_eq
    (gs.filter fun g => (entry g).live && !(gs.map entry).any (fun d => below d (entry g))) []
  simp only [List.map_nil] at start
  rw [start]
  change _ = List.eraseDups _
  congr 1
  apply List.filter_congr
  intro x _
  simp only [List.any_map, Function.comp_def, below_entry]
  rfl

def generate {n} : List (Row n) → List (Vec n)
  | [] => minimize (units n)
  | r :: rs => minimize (intersect r (generate rs))

/-- Every coefficient of the row is zero or one. -/
def Row.isUnit {n} (r : Row n) : Bool := decide (∀ i, r.pos i ≤ 1 ∧ r.neg i ≤ 1)

def pair {n} (i j : Fin n) : Vec n := fun k => spike i 1 k + spike j 1 k

/-- The irreducible solutions of a row with unit coefficients: one unit
vector per neutral coordinate and one vector per pair of opposite coordinates. -/
def Row.pairs {n} (r : Row n) : List (Vec n) :=
  let idx := List.finRange n
  (idx.filter fun i => r.pos i == 0 && r.neg i == 0).map (fun i => spike i 1) ++
    (idx.filter fun i => r.pos i == 1).flatMap fun i =>
      (idx.filter fun j => r.neg j == 1).map (pair i)

/-- Read the generators of a unit row off its support. Other rows keep the
bounded enumeration. -/
def Row.quick {n} (r : Row n) : List (Vec n) := if r.isUnit then r.pairs else r.generators

def intersectQuick {n} (r : Row n) (gs : List (Vec n)) :=
  lift gs.get (r.pullback gs.get).quick

private def intersectQuickStored {n} (r : Row n) (gs : List (Vec n)) :=
  let table := gs.toArray
  let g : Fin gs.length → Vec n := fun j => table[j.val]'(by simp [table])
  lift g (r.pullback g).quick

@[csimp] theorem intersectQuick_eq_stored : @intersectQuick = @intersectQuickStored := by
  funext n r gs
  have same : (fun j : Fin gs.length => gs.toArray[j.val]'(by simp)) = gs.get := by
    funext j
    simp
  simp only [intersectQuick, intersectQuickStored, same]

/-- `generate` with the unit-row shortcut at every intersection. -/
def generateQuick {n} : List (Row n) → List (Vec n)
  | [] => minimize (units n)
  | r :: rs => minimize (intersectQuick r (generateQuick rs))

end Tamarin.ACBasis
