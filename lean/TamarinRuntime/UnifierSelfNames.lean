/-! Names for the range variables of a unifier, chosen from the unifier itself.

The naming export (`Tamarin.UnifierNames`) takes a proposal: a label for every
range variable of each arm. This module makes one for a family with a single
arm, from that arm and the labels of the query, so the caller need not compute
one. It is a proposer: the naming export tests the proposal as it tests any
other, and nothing is promised about what is proposed here.

The labels are those the Maude backend gives the witnesses of a unifier that
its own free unifier finds without help (`composeVFresh` of the empty
substitution with the most general unifier). A range variable that is the
whole image of one query variable of its sort and occurs nowhere else stands
for that variable: it gets the variable's own label, which the naming export
turns into the variable itself. Every other range variable stands for the
class of query variables whose whole image it is. That class has a
representative, the variable the free unifier keeps: among the members of the
range variable's sort, the least by index and then by the caller's order of
name hints. The range variable gets the representative's hint and its index
moved up, by the same amount for every class, to just above the indices of the
query variables that are not left alone; where that overflows, the indices of
the representatives go in order to the least indices those variables do not
use.

What the procedure needs of the arm is read off it by the caller, who reads
the reply anyway: for each query variable, in the order of `heads`, the
position in the range of the range variable that is its whole image (any
larger number when its image is something else), and for each range variable
the number of its occurrences in the arm. The procedure is written as loops
with arrays of small numbers as their state, because it runs once for nearly
every unification request. -/
namespace Tamarin.UnifierSelfNames

/-- The hint and the index of the label of the query variable in row `i`. -/
@[inline] def hintAt (names heads : Array UInt64) (i : Nat) : UInt64 :=
  names.getD (2 * (heads.getD (2 * i) 0).toNat) 0

@[inline] def indexAt (names heads : Array UInt64) (i : Nat) : UInt64 :=
  names.getD (2 * (heads.getD (2 * i) 0).toNat + 1) 0

/-- The position in the range of the range variable that is the whole image of
row `i`, or `w` when there is none. -/
@[inline] def singleAt (singles : Array UInt64) (w i : Nat) : Nat :=
  let p := singles.getD i 0
  -- Compared as a word: a large word is no small number.
  if p < UInt64.ofNat w then p.toNat else w

/-- Row `i` comes before row `j`: a smaller index, or the same index and a
hint the caller orders first. -/
@[inline] def before (names heads order : Array UInt64) (i j : Nat) : Bool :=
  let a := indexAt names heads i
  let b := indexAt names heads j
  a < b || (a == b &&
    order.getD (hintAt names heads i).toNat 0 < order.getD (hintAt names heads j).toNat 0)

/-- The classes of the range variables, from row `i` on: for each, the number
of rows of which it is the whole image, and its representative, the least of
those rows that has its sort (or `n`). `none` when such a row has a hint
without a rank. -/
def classes (names heads order range singles : Array UInt64) (n w i : Nat)
    (members reps : Array Nat) : Option (Array Nat × Array Nat) :=
  if i < n then
    let p := singleAt singles w i
    if p < w then
      let members := members.modify p (· + 1)
      if heads.getD (2 * i + 1) 0 == range.getD (2 * p + 1) 0 then
        if order.size ≤ (hintAt names heads i).toNat then none
        else
          let r := reps.getD p n
          let reps := if r < n && !before names heads order i r then reps else reps.set! p i
          classes names heads order range singles n w (i + 1) members reps
      else classes names heads order range singles n w (i + 1) members reps
    else classes names heads order range singles n w (i + 1) members reps
  else some (members, reps)
termination_by n - i

/-- Which range variables, from position `p` on, stand for one query variable
alone: the whole image of one row of their sort, and nowhere else. With them
the least and the largest index of the representatives of the others, or
`none` when one of the others has no representative. -/
def alone (names heads counts : Array UInt64) (members reps : Array Nat) (n w p : Nat)
    (flags : Array Bool) (lo hi : UInt64) : Option (Array Bool × UInt64 × UInt64) :=
  if p < w then
    let r := reps.getD p n
    if r < n then
      if members.getD p 0 == 1 && counts.getD p 0 == 1 then
        alone names heads counts members reps n w (p + 1) (flags.set! p true) lo hi
      else
        let i := indexAt names heads r
        alone names heads counts members reps n w (p + 1) flags (min lo i) (max hi i)
    else none
  else some (flags, lo, hi)
termination_by w - p

/-- Row `i` is left alone: its whole image is a range variable that stands for
it alone. -/
@[inline] def free (singles : Array UInt64) (flags : Array Bool) (w i : Nat) : Bool :=
  let p := singleAt singles w i
  p < w && flags.getD p false

/-- The largest index, from row `i` on, of a query variable that is not left
alone, and of one that is. -/
def topIndex (names heads singles : Array UInt64) (flags : Array Bool) (n w i : Nat)
    (top topFree : UInt64) : UInt64 × UInt64 :=
  if i < n then
    let index := indexAt names heads i
    if free singles flags w i then
      topIndex names heads singles flags n w (i + 1) top (max topFree index)
    else topIndex names heads singles flags n w (i + 1) (max top index) topFree
  else (top, topFree)
termination_by n - i

/-- How the indices of the representatives move: all by one amount, so that
the least lands on `start`, or, where that overflows, in order onto the least
indices that `used` does not hold. -/
inductive Move where
  | uniform (start lo : UInt64)
  | sparse (used sources : List Nat)

/-- The `k`-th index, counted from `0`, that is not in `used`. -/
def unusedIndex (used : List Nat) (k : Nat) : Nat := Id.run do
  let mut seen := 0
  for c in [0:k + used.length + 1] do
    if !used.contains c then
      if seen == k then return c
      seen := seen + 1
  return k + used.length

def Move.apply : Move → UInt64 → UInt64
  | .uniform start lo, i => start + (i - lo)
  | .sparse used sources, i =>
    UInt64.ofNat (unusedIndex used ((sources.filter (· < i.toNat)).eraseDups.length))

/-- Some row from `j` on that is left alone has this label and sort. The
others have indices that no moved index takes. -/
def labelled (names heads singles : Array UInt64) (flags : Array Bool) (n w : Nat)
    (hint index sort : UInt64) (j : Nat) : Bool :=
  if j < n then
    (free singles flags w j && indexAt names heads j == index && hintAt names heads j == hint &&
      heads.getD (2 * j + 1) 0 == sort) || labelled names heads singles flags n w hint index sort (j + 1)
  else false
termination_by n - j

/-- The labels of the range variables from position `p` on, pushed to `out`.
`topFree` bounds the indices of the query variables that are left alone, and
a moved index above it is no index of theirs. -/
def labels (names heads range singles : Array UInt64) (reps : Array Nat) (flags : Array Bool)
    (move : Move) (topFree : UInt64) (n w p : Nat) (out : Array UInt64) : Option (Array UInt64) :=
  if p < w then
    let r := reps.getD p n
    let hint := hintAt names heads r
    if flags.getD p false then
      labels names heads range singles reps flags move topFree n w (p + 1)
        ((out.push hint).push (indexAt names heads r))
    else
      let index := move.apply (indexAt names heads r)
      -- The label of a query variable of the sort would make the range
      -- variable stand for that variable.
      if index ≤ topFree &&
          labelled names heads singles flags n w hint index (range.getD (2 * p + 1) 0) 0 then none
      else
        labels names heads range singles reps flags move topFree n w (p + 1)
          ((out.push hint).push index)
  else some out
termination_by w - p

/-- The labels of the range variables of the arm, two words for each in the
order of `range`, or `none` when the arm is not of the shape the rule is for. -/
def proposeArm (names heads order range singles counts : Array UInt64) : Option (Array UInt64) :=
  let n := heads.size / 2
  let w := range.size / 2
  if heads.size % 2 != 0 || range.size % 2 != 0 || singles.size != n || counts.size != w then none
  else
    match classes names heads order range singles n w 0 (Array.replicate w 0)
        (Array.replicate w n) with
    | none => none
    | some (members, reps) =>
      match alone names heads counts members reps n w 0 (Array.replicate w false)
          0xFFFFFFFFFFFFFFFF 0 with
      | none => none
      | some (flags, lo, hi) =>
        let (top, topFree) := topIndex names heads singles flags n w 0 0 0
        let move : Move :=
          if top.toNat + 1 + (hi.toNat - lo.toNat) < UInt64.size then .uniform (top + 1) lo
          else
            .sparse ((List.range n).filterMap fun i =>
                if free singles flags w i then none else some (indexAt names heads i).toNat)
              ((List.range w).filterMap fun p =>
                if flags.getD p false then none else some (indexAt names heads (reps.getD p n)).toNat)
        labels names heads range singles reps flags move topFree n w 0 (Array.mkEmpty (2 * w))

/-- A proposal for the naming export: one row of labels for a family with one
arm, or no row, which proposes nothing. `names` and `heads` are the naming
export's, `order` ranks the caller's hint identifiers by the caller's order of
the hints, `ranges` lists the range variables of each arm, `singles` gives for
each query variable the position in the range of the range variable that is its
whole image (or any larger number), and `counts` the occurrences of each range
variable in the arm. -/
def propose (names heads order : Array UInt64) (ranges : Array (Array UInt64))
    (singles counts : Array UInt64) : Array (Array UInt64) :=
  if ranges.size == 1 then
    match proposeArm names heads order (ranges.getD 0 #[]) singles counts with
    | some row => #[row]
    | none => #[]
  else #[]

end Tamarin.UnifierSelfNames
