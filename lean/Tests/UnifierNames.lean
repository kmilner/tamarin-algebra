import TamarinRuntime
import Tamarin.UnifierNames

/-! The tables of the naming export and the reading of a reply of the unifier
through them, on packets. -/
namespace Tamarin.UnifierNamesTests

private abbrev unify := Executable.totalUnify fun _ => false
private abbrev name := Executable.nameUnifiers
private abbrev read := Executable.applyNames

-- x:Fresh = y:Msg has one unifier, which sends both to x. The caller knows x
-- as (hint 1, index 5) and y as (hint 2, index 5).
private def alias := unify #[] #[#[0,0,1],#[0,1,2]] #[0,1]
private def aliasNames : Array UInt64 := #[1,5,2,5]
private def aliasHeads : Array UInt64 := #[0,1,1,2]
#guard alias == #[#[1],#[],#[0,1,0,0,1],#[1,2,0,0,1]]

-- Without a proposal the range variable gets the hint 0 and the least index
-- above the query, and both rows name it by a token of kind 5 + sort.
#guard name aliasNames aliasHeads #[#[0,1]] #[] true false == #[#[1],#[0,1,1,2],#[0,0,1,0,0,6]]
#guard read (name aliasNames aliasHeads #[#[0,1]] #[] true false) true alias ==
  #[#[1],#[],#[0,1,6,6,0],#[1,2,6,6,0]]

-- A proposed label is taken, also the label of y at the sort of x, which no
-- query variable has.
#guard name aliasNames aliasHeads #[#[0,1]] #[#[2,9]] true false == #[#[1],#[0,1,1,2],#[0,0,1,0,2,9]]
#guard read (name aliasNames aliasHeads #[#[0,1]] #[#[2,9]] true false) true alias ==
  #[#[1],#[],#[0,1,6,9,2],#[1,2,6,9,2]]
#guard name aliasNames aliasHeads #[#[0,1]] #[#[2,5]] true false == #[#[1],#[0,1,1,2],#[0,0,1,0,2,5]]

-- The label of x makes the range variable stand for x. It also occurs in the
-- row of y, so the reply has no reading through this table.
#guard name aliasNames aliasHeads #[#[0,1]] #[#[1,5]] true false == #[#[1],#[0,1,1,2],#[0,0,1,1,0,0]]
#guard read (name aliasNames aliasHeads #[#[0,1]] #[#[1,5]] true false) true alias == #[#[0]]

-- x = x binds x to itself. With the label of x the binding is left out, and
-- with a default label it is a renaming.
private def same := unify #[] #[#[0,0,2]] #[0,0]
#guard same == #[#[1],#[],#[0,2,0,0,2]]
#guard name #[1,5] #[0,2] #[#[0,2]] #[#[1,5]] true false == #[#[1],#[0,2],#[0,0,2,1,0,0]]
#guard read (name #[1,5] #[0,2] #[#[0,2]] #[#[1,5]] true false) true same == #[#[1],#[]]
#guard read (name #[1,5] #[0,2] #[#[0,2]] #[] true false) true same == #[#[1],#[],#[0,2,7,6,0]]

-- The default indices are the least ones the query does not use, moved up
-- together: the query uses 1 and 4, so three variables get 0, 2, 3 plus 5.
#guard name #[1,1,1,4] #[0,2,1,2] #[#[7,2,8,2,9,2]] #[] true false ==
  #[#[1],#[0,2,1,2],#[0,7,2,0,0,5,8,2,0,0,7,9,2,0,0,8]]

-- One label for two variables of one sort fails the test, and the default
-- labels are returned. At two sorts they are two variables.
#guard name #[1,1,1,4] #[0,2,1,2] #[#[7,2,8,2]] #[#[3,3,3,3]] true false ==
  #[#[1],#[0,2,1,2],#[0,7,2,0,0,5,8,2,0,0,7]]
#guard name #[1,1,1,4] #[0,2,1,2] #[#[7,2,8,1]] #[#[3,3,3,3]] true false ==
  #[#[1],#[0,2,1,2],#[0,7,2,0,3,3,8,1,0,3,3]]

-- Without the sort of natural numbers an arm with such a variable gets no
-- table, and the proposal has a row for each arm that is kept.
#guard name #[1,1,1,4] #[0,2,1,2] #[#[7,2,8,4],#[7,2]] #[] false false == #[#[1],#[0,2,1,2],#[1,7,2,0,0,5]]
#guard name #[1,1,1,4] #[0,2,1,2] #[#[7,2,8,4],#[7,2]] #[#[2,2]] false false ==
  #[#[1],#[0,2,1,2],#[1,7,2,0,2,2]]

-- x + y with x, y of the sort of natural numbers. A module without that sort
-- reads no arm, and the reading fails when the arm has a table nevertheless
-- or lacks one in a module with the sort.
private def sum := unify #[4,7,2,4,4,4] #[#[0,0,4],#[0,1,4],#[0,2,4],#[4,7,0,1]] #[3,2]
private def sumNames : Array UInt64 := #[1,0,1,1,1,2]
private def sumHeads : Array UInt64 := #[0,4,1,4,2,4]
#guard sum == #[#[1],#[],#[0,4,0,0,4],#[1,4,0,1,4],#[2,4,0,0,4,0,1,4,4,7,2]]
#guard name sumNames sumHeads #[#[0,4,1,4]] #[] false false == #[#[1],#[0,4,1,4,2,4]]
#guard read (name sumNames sumHeads #[#[0,4,1,4]] #[] false false) false sum == #[#[1]]
#guard read (name sumNames sumHeads #[#[0,4,1,4]] #[] false false) true sum == #[#[0]]
#guard read (name sumNames sumHeads #[#[0,4,1,4]] #[] true false) true sum ==
  #[#[1],#[],#[0,4,9,3,0],#[1,4,9,4,0],#[2,4,9,3,0,9,4,0,4,7,2]]
-- Told of no variable of that sort, the export writes a table without one,
-- and the arm cannot be read through it.
#guard read (name sumNames sumHeads #[#[]] #[] false false) false sum == #[#[0]]

-- A query variable at the top of the index space leaves no index above the
-- query. The export declines, unless the caller settles for an index the
-- query does not use.
#guard name #[1,0xFFFFFFFFFFFFFFFF,1,0] #[0,2,1,2] #[#[7,2,8,2]] #[] true false == #[#[0]]
#guard name #[1,0xFFFFFFFFFFFFFFFF,1,0] #[0,2,1,2] #[#[7,2,8,2]] #[] true true ==
  #[#[1],#[0,2,1,2],#[0,7,2,0,0,1,8,2,0,0,2]]
-- The indices are moved up together, so they can pass the top where single
-- ones would fit. That is declined the same way.
#guard name #[1,0xFFFFFFFFFFFFFFFE,1,1] #[0,2,1,2] #[#[7,2,8,2]] #[] true false == #[#[0]]
#guard name #[1,0xFFFFFFFFFFFFFFFE,1,0] #[0,2,1,2] #[#[7,2]] #[] true false ==
  #[#[1],#[0,2,1,2],#[0,7,2,0,0,0xFFFFFFFFFFFFFFFF]]

-- Two query variables of one sort with one label are declined. At two sorts
-- they are two variables for the caller.
#guard name #[1,5,1,5] #[0,2,1,2] #[#[0,2]] #[] true false == #[#[0]]
#guard name #[1,5,1,5] #[0,1,1,2] #[#[0,1]] #[] true false == #[#[1],#[0,1,1,2],#[0,0,1,0,0,6]]

-- A table for an arm the reply does not have, other words for the query
-- variables, or a variable without a target: no reading.
#guard read #[#[1],#[0,1,1,2],#[1,0,1,0,0,6]] true alias == #[#[0]]
#guard read #[#[1],#[0,1,1,1],#[0,0,1,0,0,6]] true alias == #[#[0]]
#guard read #[#[1],#[0,1,1,2],#[0]] true alias == #[#[0]]
#guard read #[#[0]] true alias == #[#[0]]
-- The empty family is read with no table.
#guard read #[#[1],#[]] true #[#[1]] == #[#[1]]
#guard read (name #[] #[] #[] #[] true false) true #[#[1]] == #[#[1]]

/-! The proposer `proposeUnifierNames`, which makes a proposal from the reply
of the unifier itself, sent with each row behind its length. -/

private abbrev propose := Executable.proposeUnifierNames
private def flat (rows : Array (Array UInt64)) : Array UInt64 :=
  rows.foldl (fun acc r => (acc.push r.size.toUInt64) ++ r) #[]

-- x:Fresh = y:Msg: the range variable stands for both, and its representative
-- is x, of its sort. It takes the hint of x and the index above the query.
#guard propose aliasNames aliasHeads #[0,0,0] #[#[0,1]] (flat alias) == #[#[1,6]]
#guard read (name aliasNames aliasHeads #[#[0,1]] #[#[1,6]] true false) true alias ==
  #[#[1],#[],#[0,1,6,6,1],#[1,2,6,6,1]]

-- f(a, b) = f(b, a) with a and b of one sort at one index: the representative
-- is the one whose hint comes first in the caller's order.
private def swap := unify #[2,9,2,2,2,2] #[#[0,0,2],#[0,1,2],#[2,9,0,1],#[2,9,1,0]] #[2,3]
#guard swap == #[#[1],#[],#[0,2,0,0,2],#[1,2,0,0,2]]
#guard propose #[1,3,2,3] #[0,2,1,2] #[0,2,1] #[#[0,2]] (flat swap) == #[#[2,4]]
#guard propose #[1,3,2,3] #[0,2,1,2] #[0,1,2] #[#[0,2]] (flat swap) == #[#[1,4]]
-- Without a rank for a hint nothing is proposed.
#guard propose #[1,3,2,3] #[0,2,1,2] #[0,1] #[#[0,2]] (flat swap) == #[]

-- x = f(y) and z = z: y is moved above the indices of x and y, and z, which
-- is left alone, keeps its own label and its binding is left out.
private def lone := unify #[2,8,1,2,2] #[#[0,0,2],#[0,1,2],#[2,8,1],#[0,2,2]] #[0,2,3,3]
private def loneHeads : Array UInt64 := #[0,2,1,2,2,2]
#guard lone == #[#[1],#[],#[0,2,0,1,2,2,8,1],#[1,2,0,1,2],#[2,2,0,2,2]]
#guard propose #[1,1,2,7,3,9] loneHeads #[0,0,0,0] #[#[1,2,2,2]] (flat lone) == #[#[2,8,3,9]]
#guard read (name #[1,1,2,7,3,9] loneHeads #[#[1,2,2,2]] #[#[2,8,3,9]] true false) true lone ==
  #[#[1],#[],#[0,2,7,8,2,2,8,1],#[1,2,7,8,2]]
-- A moved label that is the label of a query variable of the sort is not
-- proposed.
#guard propose #[1,1,2,7,2,8] loneHeads #[0,0,0,0] #[#[1,2,2,2]] (flat lone) == #[]
-- Where the move overflows, the least index the other variables do not use.
#guard propose #[1,0xFFFFFFFFFFFFFFFF,2,0,3,9] loneHeads #[0,0,0,0] #[#[1,2,2,2]] (flat lone) ==
  #[#[2,1,3,9]]
-- A family with other than one arm, or a reply that is not one, gets no
-- proposal.
#guard propose #[1,1,2,7,3,9] loneHeads #[0,0,0,0] #[#[1,2,2,2],#[1,2]] (flat lone) == #[]
#guard propose #[1,1,2,7,3,9] loneHeads #[0,0,0,0] #[#[1,2,2,2]] ((flat lone).pop) == #[]

end Tamarin.UnifierNamesTests
