import Tamarin.ACBasis

/-! Row intersection without recomputing linear combinations. The generators
of a unit row are single coefficients and pairs of coefficients, so the lifted
vectors are previous generators and sums of two of them. Other rows use the
pruned search. -/
namespace Tamarin.ACBasis

private theorem mix_spike {k n} (g : Fin k → Vec n) (i : Fin k) : mix g (spike i 1) = g i := by
  funext x
  simp [mix, dot_spike]

private theorem mix_pair {k n} (g : Fin k → Vec n) (i j : Fin k) :
    mix g (pair i j) = fun x => g i x + g j x := by
  funext x
  have add : dot (fun j => g j x) (pair i j) =
      dot (fun j => g j x) (spike i 1) + dot (fun j => g j x) (spike j 1) := by
    simp only [dot, pair, Nat.mul_add, total_add]
  simp [mix, add, dot_spike]

/-- Read a vector from a table. The tables are built as data first and only
then wrapped, so no coordinate is recomputed on access. -/
private def reads {n} (table : Vector Nat n) : Vec n := fun i => table[i]

private theorem reads_ofFn {n} (v : Vec n) : reads (Vector.ofFn v) = v := by
  funext i
  simp [reads]

/-- `intersectCompact` reading the lifted generators of a unit row directly
from the generator table. -/
def intersectFast {n} (r : Row n) (gs : List (Vec n)) : List (Vec n) :=
  let table := gs.toArray
  let g : Fin gs.length → Vec n := fun j => table[j.val]'(by simp [table])
  let p := r.pullback g
  if p.isUnit then
    let idx := List.finRange gs.length
    let right := idx.filter fun j => p.neg j == 1
    let sums := (idx.filter fun i => p.pos i == 1).flatMap fun i =>
      right.map fun j => Vector.ofFn fun x => g i x + g j x
    (idx.filter fun i => p.pos i == 0 && p.neg i == 0).map g ++ sums.map reads
  else lift g p.loose

theorem intersectFast_eq {n} (r : Row n) (gs : List (Vec n)) :
    intersectFast r gs = intersectCompact r gs := by
  have same : (fun j : Fin gs.length => gs.toArray[j.val]'(by simp)) = gs.get := by
    funext j
    simp
  simp only [intersectFast, intersectCompact, same, Row.compact]
  split
  · simp only [lift, Row.pairs, List.map_append, List.map_map, List.map_flatMap, Function.comp_def,
      mix_spike, mix_pair, reads_ofFn]
    have at_index (j : Fin gs.length) : gs.toArray[j.val]'(by simp) = gs.get j := by simp
    simp only [at_index]
  · rfl

/-- `generateCompact` with the direct lift at every unit row. -/
def generateFast {n} : List (Row n) → List (Vec n)
  | [] => minimize (units n)
  | r :: rs => minimize (intersectFast r (generateFast rs))

theorem generateFast_eq {n} (rows : List (Row n)) : generateFast rows = generateCompact rows := by
  induction rows with
  | nil => rfl
  | cons r rs ih => simp only [generateCompact, generateFast, intersectFast_eq, ih]

theorem generateFast_correct {n} (rows : List (Row n)) : BasisCorrect rows (generateFast rows) :=
  generateFast_eq rows ▸ generateCompact_correct rows

end Tamarin.ACBasis
