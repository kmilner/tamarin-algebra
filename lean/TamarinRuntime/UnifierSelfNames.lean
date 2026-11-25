/-! Names for the range variables of a unifier, chosen from the unifier itself.

The naming export (`Tamarin.UnifierNames`) takes a proposal: a label for every
range variable of each arm. This module makes one for a family with a single
arm, from that arm and the labels of the query, so the caller need not compute
one. It is a proposer: the naming export tests the proposal as it tests any
other, and nothing is promised about what is proposed here.

The labels are those the Maude backend gives the witnesses of a unifier that
its own free unifier finds without help (`composeVFresh` of the empty
substitution with the most general unifier). A range variable that is the
whole image of one query variable and occurs nowhere else stands for that
variable: it gets the variable's own label, which the naming export turns into
the variable itself. Every other range variable stands for the class of query
variables whose image it is. That class has a representative, the variable the
free unifier keeps: among the members of the range variable's sort, the least
by index and then by the caller's order of name hints. The range variable gets
the representative's hint and its index moved up, by the same amount for every
class, to just above the indices of the query variables that are not left
alone; where that overflows, the indices of the representatives go in order to
the least indices those variables do not use.

The arm is read as the naming export's reader reads it: the status row `[1]`,
an empty row, and one row for each query variable in the order of `heads`, its
identifier and sort words followed by tokens of three words, where a token of
kind `0` is a range variable by identifier and sort word. -/
namespace Tamarin.UnifierSelfNames

/-- The start and the length of each row of words that hold every row behind
its length, or `none` when a length overruns the words. -/
def rowSpans (words : Array UInt64) : Option (Array (Nat × Nat)) := Id.run do
  let mut spans : Array (Nat × Nat) := #[]
  let mut pos := 0
  -- Each row takes at least its length word.
  for _ in [0:words.size] do
    if pos < words.size then
      let n := (words.getD pos 0).toNat
      if words.size < pos + 1 + n then return none
      spans := spans.push (pos + 1, n)
      pos := pos + 1 + n
  return if pos == words.size then some spans else none

/-- The position of a range variable among the identifier and sort words of
`range`, or the number of range variables. -/
def position (range : Array UInt64) (id sort : UInt64) : Nat := Id.run do
  for p in [0:range.size / 2] do
    if range.getD (2 * p) 0 == id && range.getD (2 * p + 1) 0 == sort then return p
  return range.size / 2

/-- The `k`-th index, counted from `0`, that is not in `used`. -/
def unusedIndex (used : Array UInt64) (k : Nat) : Nat := Id.run do
  let mut seen := 0
  for c in [0:k + used.size + 1] do
    if !used.contains (UInt64.ofNat c) then
      if seen == k then return c
      seen := seen + 1
  return k + used.size

/-- The labels of the range variables of the arm, two words for each in the
order of `range`, or `none` when the arm is not of the shape the rule is for. -/
def proposeArm (names heads order range reply : Array UInt64) : Option (Array UInt64) := Id.run do
  let some spans := rowSpans reply | return none
  let n := heads.size / 2
  let w := range.size / 2
  if heads.size % 2 != 0 || range.size % 2 != 0 || spans.size != n + 2 then return none
  let (s0, l0) := spans.getD 0 (0, 0)
  if l0 != 1 || reply.getD s0 0 != 1 || (spans.getD 1 (0, 0)).2 != 0 then return none
  -- The label of the query variable in row `i`, which must have one.
  for i in [0:n] do
    if names.size ≤ 2 * (heads.getD (2 * i) 0).toNat + 1 then return none
  let hint (i : Nat) : UInt64 := names.getD (2 * (heads.getD (2 * i) 0).toNat) 0
  let index (i : Nat) : UInt64 := names.getD (2 * (heads.getD (2 * i) 0).toNat + 1) 0
  let sortAt (i : Nat) : UInt64 := heads.getD (2 * i + 1) 0
  -- The occurrences of each range variable, and the rows bound to it alone.
  let mut count : Array Nat := Array.replicate w 0
  let mut members : Array (Array Nat) := Array.replicate w #[]
  for i in [0:n] do
    let (s, l) := spans.getD (i + 2) (0, 0)
    if l < 2 || (l - 2) % 3 != 0 then return none
    if reply.getD s 0 != heads.getD (2 * i) 0 || reply.getD (s + 1) 0 != sortAt i then return none
    for t in [0:(l - 2) / 3] do
      let k := s + 2 + 3 * t
      if reply.getD k 1 == 0 then
        let p := position range (reply.getD (k + 1) 0) (reply.getD (k + 2) 0)
        if w ≤ p then return none
        count := count.modify p (· + 1)
    if l == 5 && reply.getD (s + 2) 1 == 0 then
      let p := position range (reply.getD (s + 3) 0) (reply.getD (s + 4) 0)
      members := members.modify p (·.push i)
  -- The row a range variable stands for alone: it is that row's whole image,
  -- of its sort, and occurs nowhere else.
  let alone (p : Nat) : Option Nat :=
    match members.getD p #[] with
    | #[i] => if count.getD p 0 == 1 && sortAt i == range.getD (2 * p + 1) 0 then some i else none
    | _ => none
  let mut free : Array Bool := Array.replicate n false
  for p in [0:w] do
    if let some i := alone p then free := free.set! i true
  -- The rows that are not left alone, and the largest of their indices.
  let mut used : Array UInt64 := #[]
  for i in [0:n] do
    if !free.getD i false then used := used.push (index i)
  let top : Nat := used.foldl (fun m i => max m i.toNat) 0
  -- The representative of each other range variable: among the rows bound
  -- to it alone that have its sort, the least by index and then by hint.
  let before (i j : Nat) : Bool :=
    index i < index j ||
      (index i == index j && order.getD (hint i).toNat 0 < order.getD (hint j).toNat 0)
  let mut reps : Array Nat := Array.replicate w 0
  for p in [0:w] do
    if (alone p).isNone then
      let mut best : Option Nat := none
      for i in members.getD p #[] do
        if sortAt i == range.getD (2 * p + 1) 0 then
          if (hint i).toNat ≥ order.size then return none
          best := match best with
            | none => some i
            | some b => if before i b then some i else some b
      match best with
      | none => return none
      | some b => reps := reps.set! p b
  -- The indices of the representatives, moved up together, or in order to
  -- the least unused ones where that overflows.
  let mut sources : Array UInt64 := #[]
  for p in [0:w] do
    if (alone p).isNone then
      let i := index (reps.getD p 0)
      if !sources.contains i then sources := sources.push i
  let lo : Nat := sources.foldl (fun m i => min m i.toNat) (UInt64.size - 1)
  let hi : Nat := sources.foldl (fun m i => max m i.toNat) 0
  let uniform := top + 1 + (hi - lo) < UInt64.size
  let moved (i : UInt64) : UInt64 :=
    if uniform then UInt64.ofNat (top + 1 + (i.toNat - lo))
    else UInt64.ofNat (unusedIndex used (sources.foldl (fun c j => if j < i then c + 1 else c) 0))
  let mut out : Array UInt64 := Array.mkEmpty (2 * w)
  for p in [0:w] do
    match alone p with
    | some i => out := (out.push (hint i)).push (index i)
    | none =>
      let r := reps.getD p 0
      let label := (hint r, moved (index r))
      -- The label of a query variable of the sort would make the range
      -- variable stand for it.
      for j in [0:n] do
        if hint j == label.1 && index j == label.2 && sortAt j == range.getD (2 * p + 1) 0 then
          return none
      out := (out.push label.1).push label.2
  return some out

/-- A proposal for the naming export: one row of labels for a family with one
arm, or no row, which proposes nothing. `names` and `heads` are the naming
export's, `order` ranks the caller's hint identifiers by the caller's order of
the hints, `ranges` lists the range variables of each arm, and `reply` is the
unifier's reply with each row behind its length. -/
def propose (names heads order : Array UInt64) (ranges : Array (Array UInt64)) (reply : Array UInt64) :
    Array (Array UInt64) :=
  if ranges.size == 1 then
    match proposeArm names heads order (ranges.getD 0 #[]) reply with
    | some row => #[row]
    | none => #[]
  else #[]

end Tamarin.UnifierSelfNames
