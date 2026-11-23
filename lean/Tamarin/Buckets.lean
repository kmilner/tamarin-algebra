/-! Duplicate removal and index lookup through an array of buckets. Elements
with different keys are never compared, and the results are those of the list
operations for every key function. -/
namespace Tamarin.Buckets
variable {α : Type} [BEq α] [LawfulBEq α]

private def bucket {β : Type} (buckets : Array (List β)) (i : Nat) : List β := (buckets[i]?).getD []

private theorem bucket_modify_self {β : Type} (buckets : Array (List β)) (i : Nat) (h : i < buckets.size)
    (f : List β → List β) : bucket (buckets.modify i f) i = f (bucket buckets i) := by
  unfold bucket
  rw [Array.getElem?_modify, ite_eq_left rfl, Array.getElem?_eq_getElem h]
  rfl

private theorem bucket_modify_ne {β : Type} (buckets : Array (List β)) {i j : Nat} (h : i ≠ j)
    (f : List β → List β) : bucket (buckets.modify i f) j = bucket buckets j := by
  simp [bucket, Array.getElem?_modify, h]

/-- `List.eraseDupsBy.loop` comparing each element with its own bucket only. -/
def loop (key : α → Nat) : List α → Array (List α) → List α → List α
  | [], _, acc => acc.reverse
  | a :: as, buckets, acc =>
    let i := key a % buckets.size
    if (bucket buckets i).any (fun b => a == b) then loop key as buckets acc
    else loop key as (buckets.modify i (a :: ·)) (a :: acc)

private theorem loop_eq (key : α → Nat) (l : List α) (buckets : Array (List α)) (acc : List α)
    (size : 0 < buckets.size)
    (same : ∀ a, (bucket buckets (key a % buckets.size)).any (fun b => a == b) = acc.any (fun b => a == b)) :
    loop key l buckets acc = List.eraseDupsBy.loop (· == ·) l acc := by
  induction l generalizing buckets acc with
  | nil => rfl
  | cons a as ih =>
    simp only [loop, List.eraseDupsBy.loop, same a]
    cases seen : acc.any (fun b => a == b) with
    | true => simpa using ih buckets acc size same
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply ih
      · simpa using size
      · intro c
        rw [Array.size_modify]
        by_cases hit : key a % buckets.size = key c % buckets.size
        · rw [← hit, bucket_modify_self _ _ (Nat.mod_lt _ size), List.any_cons, List.any_cons, hit, same c]
        · have ne : (c == a) = false := by
            cases h : c == a with
            | false => rfl
            | true => exact (hit (by rw [eq_of_beq h])).elim
          rw [bucket_modify_ne _ hit, List.any_cons, ne, same c, Bool.false_or]

/-- `List.eraseDups` with one bucket per residue of the key. -/
def dedup (key : α → Nat) (xs : List α) : List α :=
  loop key xs (Array.replicate (xs.length + 1) []) []

theorem dedup_eq (key : α → Nat) (xs : List α) : dedup key xs = xs.eraseDups := by
  unfold dedup List.eraseDups List.eraseDupsBy
  apply loop_eq
  · simp
  · intro a
    simp only [bucket, Array.getElem?_replicate]
    split <;> rfl

theorem mem_dedup {key : α → Nat} {xs : List α} {a : α} : a ∈ dedup key xs ↔ a ∈ xs := by
  rw [dedup_eq]
  exact List.mem_eraseDups

/-- The positions of a list, grouped by key. Earlier positions come first in a bucket. -/
def index (key : α → Nat) (size : Nat) : Nat → List α → Array (List (α × Nat))
  | _, [] => Array.replicate size []
  | n, t :: ts => (index key size (n+1) ts).modify (key t % size) ((t, n) :: ·)

/-- `index` as a loop over the positions from the last to the first, so that
its stack does not grow with the list. -/
private def indexLoop (key : α → Nat) (size : Nat) (n : Nat) (ts : List α) : Array (List (α × Nat)) :=
  (ts.zipIdx n).reverse.foldl (fun acc e => acc.modify (key e.1 % size) (e :: ·)) (Array.replicate size [])

omit [BEq α] [LawfulBEq α] in
@[csimp] private theorem index_eq_loop : @index = @indexLoop := by
  funext α key size n ts
  induction ts generalizing n with
  | nil => rfl
  | cons t ts ih =>
    simp only [index, indexLoop, List.zipIdx_cons, List.reverse_cons, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    rw [ih (n+1)]
    rfl

omit [BEq α] [LawfulBEq α] in
private theorem size_index (key : α → Nat) (size n : Nat) (ts : List α) :
    (index key size n ts).size = size := by
  induction ts generalizing n with
  | nil => simp [index]
  | cons t ts ih => simp [index, ih]

/-- The first position recorded for an element, or the default. -/
def lookup (key : α → Nat) (table : Array (List (α × Nat))) (default : Nat) (t : α) : Nat :=
  match (bucket table (key t % table.size)).find? (fun p => p.1 == t) with
  | some p => p.2
  | none => default

theorem lookup_index (key : α → Nat) (size : Nat) (positive : 0 < size) (n : Nat) (ts : List α) (t : α) :
    lookup key (index key size n ts) (n + ts.length) t = n + ts.idxOf t := by
  induction ts generalizing n with
  | nil =>
    have empty : bucket (Array.replicate size ([] : List (α × Nat))) (key t % size) = [] := by
      simp only [bucket, Array.getElem?_replicate]
      split <;> rfl
    simp [lookup, index, empty]
  | cons u ts ih =>
    have step := ih (n+1)
    simp only [lookup, size_index] at step ⊢
    simp only [index]
    rw [List.idxOf_cons]
    by_cases hit : key u % size = key t % size
    · rw [← hit, bucket_modify_self _ _ (by rw [size_index]; exact Nat.mod_lt _ positive), List.find?_cons]
      cases same : u == t with
      | true => simp
      | false =>
        simp only [List.length_cons]
        rw [hit, show n + (ts.length + 1) = n + 1 + ts.length by omega, step]
        simp; omega
    · have ne : (u == t) = false := by
        cases h : u == t with
        | false => rfl
        | true => exact (hit (by rw [eq_of_beq h])).elim
      rw [bucket_modify_ne _ hit, ne]
      simp only [List.length_cons]
      rw [show n + (ts.length + 1) = n + 1 + ts.length by omega, step]
      simp; omega

end Tamarin.Buckets
