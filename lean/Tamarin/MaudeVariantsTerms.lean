import Tamarin.MaudeUnifyAlgorithm

/-!
# Terms of Maude's `get variants`

The terms of the generator of Maude's `get variants` replies
(`Tamarin.MaudeVariantsSearch`) are the dags of the port of Maude's unifier
(`Tamarin.MaudeUnify.Dag`) over a signature whose symbols are numbers: free,
C and AC symbols by their ids, a name constant `k` of sort code `c` as the atom
`8 * k + c`. Variables are slots.

The generator needs more of Maude's sorts than the unifier: the module has the
sort `TOP` above `Msg` and `Node`, and the kind `[TOP]` of ill-sorted terms. The
operators `list`, `cons` and `nil` that wrap the arguments of a fact live there.
`MS` is that sort structure and `Syms` gives each symbol its sorts in it.

Everything here is a plain total function. Nothing is proved: the generator is
a proposer, whose families are checked before they are used.
-/
namespace Tamarin.MaudeVariants
open Tamarin MaudeUnify

/-- The sorts of the `MSG` module and its kind. -/
inductive MS where
  | pub | fresh | msg | node | nat | top | kind
  deriving DecidableEq, Inhabited, Repr

namespace MS

/-- The subsort relation of the module, reflexive; the kind is above nothing. -/
def le (a b : MS) : Bool :=
  a == b || match a, b with
    | .pub, .msg | .fresh, .msg | .nat, .msg => true
    | .pub, .top | .fresh, .top | .nat, .top | .msg, .top | .node, .top => true
    | _, _ => false

def ofSort : SortId → MS
  | .pub => .pub | .fresh => .fresh | .msg => .msg | .node => .node | .nat => .nat

/-- The sort the unifier sees: `TOP` and the kind become `Msg`. Only the
fact wrappers have them, and no equation is indexed under a wrapper. -/
def toSort : MS → SortId
  | .pub => .pub | .fresh => .fresh | .node => .node | .nat => .nat | _ => .msg

end MS

/-- A sort code of the wire (`TotalUnifyWire.sortCode`): pub 0, fresh 1,
msg 2, node 3, nat 4. -/
def sortOfCode : Nat → Option SortId
  | 0 => some .pub | 1 => some .fresh | 2 => some .msg | 3 => some .node | 4 => some .nat
  | _ => none

def codeOfSort : SortId → Nat
  | .pub => 0 | .fresh => 1 | .msg => 2 | .node => 3 | .nat => 4

/-- The sorts of the symbols, by id: the input sorts and output sort of each
free symbol, the sort of each C and AC symbol. -/
structure Syms where
  free : Array (Array MS × MS)
  comm : Array MS
  ac : Array MS
  deriving Inhabited

/-- The atom of the name constant with argument `k` and sort code `c`. -/
def atomOf (k c : Nat) : Nat := 8 * k + c

def atomArg (a : Nat) : Nat := a / 8

def atomSort (a : Nat) : SortId := (sortOfCode (a % 8)).getD .msg

/-- The signature of the generator: every kind of symbol is a number. -/
abbrev Sig (y : Syms) : Signature where
  FreeSym := Nat
  CSym := Nat
  ACSym := Nat
  Atom := Nat
  arity f := (y.free.getD f (#[], .msg)).1.size
  inputSort f i := ((y.free.getD f (#[], .msg)).1.getD i.val .msg).toSort
  outputSort f := (y.free.getD f (#[], .msg)).2.toSort
  cSort f := (y.comm.getD f .msg).toSort
  acSort f := (y.ac.getD f .msg).toSort
  atomSort a := atomSort a

abbrev D (y : Syms) := Dag (Sig y)

instance (y : Syms) : Inhabited (D y) := ⟨.var 0⟩

section
variable {y : Syms}

/-- The top symbol as a key: 0 free, 1 C, 2 AC; `none` for a variable or an atom. -/
def topKey : D y → Option (Nat × Nat)
  | .free f _ => some (0, f)
  | .comm f _ _ => some (1, f)
  | .ac f _ => some (2, f)
  | _ => none

def children : D y → List (D y)
  | .free _ args => args
  | .comm _ a b => [a, b]
  | .ac _ args => args
  | _ => []

/-- Maude's normal form under ranks: AC arguments flattened and sorted, C
arguments ordered. -/
def norm (r : Ranks (Sig y)) (so : Nat → Option SortId) : D y → D y
  | .free f args => .free f (args.attach.map fun ⟨d, _⟩ => norm r so d)
  | .comm f a b => Dag.mkComm r so f (norm r so a) (norm r so b)
  | .ac f args => .ac f (Dag.normAC r so f (args.attach.map fun ⟨d, _⟩ => norm r so d))
  | d => d

/-- `Term::normalize(false)`, which Maude applies to the query before it
numbers the query's variables (`Interpreter::makeDag`): AC and C arguments
sorted by the term order, nested AC products not flattened. -/
def normShallow (r : Ranks (Sig y)) (so : Nat → Option SortId) : D y → D y
  | .free f args => .free f (args.attach.map fun ⟨d, _⟩ => normShallow r so d)
  | .comm f a b => Dag.mkComm r so f (normShallow r so a) (normShallow r so b)
  | .ac f args =>
    .ac f ((args.attach.map fun ⟨d, _⟩ => normShallow r so d).mergeSort
      fun a b => Dag.cmp r so a b != .gt)
  | d => d

/-- The least sort of a dag in the module, the kind if it is ill sorted. -/
def msort (y' : Syms) (vs : Nat → SortId) : Dag (Sig y') → MS
  | .var i => MS.ofSort (vs i)
  | .atom a => MS.ofSort (atomSort a)
  | .free f args =>
    let (ins, out) := y'.free.getD f (#[], .msg)
    if (args.attach.zipIdx.all fun (⟨a, _⟩, i) => (msort y' vs a).le (ins.getD i .msg)) then out
    else .kind
  | .comm f a b =>
    let c := y'.comm.getD f .msg
    if (msort y' vs a).le c && (msort y' vs b).le c then c else .kind
  | .ac f args =>
    let c := y'.ac.getD f .msg
    if args.attach.all fun ⟨a, _⟩ => (msort y' vs a).le c then c else .kind

/-- The slots of a dag added to `acc` by first occurrence, depth first, left
to right (`DagNode::indexVariables`). -/
def dfsVars (acc : Array Nat) : D y → Array Nat
  | .var i => if acc.contains i then acc else acc.push i
  | .atom _ => acc
  | .free _ args => args.attach.foldl (fun acc ⟨d, _⟩ => dfsVars acc d) acc
  | .comm _ a b => dfsVars (dfsVars acc a) b
  | .ac _ args => args.attach.foldl (fun acc ⟨d, _⟩ => dfsVars acc d) acc

/-- Plain instantiation, without normalising. -/
def subst (θ : Nat → D y) : D y → D y
  | .var i => θ i
  | .atom a => .atom a
  | .free f args => .free f (args.attach.map fun ⟨d, _⟩ => subst θ d)
  | .comm f a b => .comm f (subst θ a) (subst θ b)
  | .ac f args => .ac f (args.attach.map fun ⟨d, _⟩ => subst θ d)

/-- Rename the slots. -/
def rename (θ : Nat → Nat) : D y → D y
  | .var i => .var (θ i)
  | .atom a => .atom a
  | .free f args => .free f (args.attach.map fun ⟨d, _⟩ => rename θ d)
  | .comm f a b => .comm f (rename θ a) (rename θ b)
  | .ac f args => .ac f (args.attach.map fun ⟨d, _⟩ => rename θ d)

/-- Remove one occurrence of `x`. -/
def removeOne (x : D y) : List (D y) → Option (List (D y))
  | [] => none
  | z :: zs => if Dag.beq x z then some zs else (removeOne x zs).map (z :: ·)

/-- Remove one occurrence of each element of `xs`. -/
def removeAll (xs ys : List (D y)) : Option (List (D y)) :=
  xs.foldlM (fun acc x => removeOne x acc) ys

/-- Runs of equal adjacent elements: Maude's argument/multiplicity pairs of a
normalised AC node. -/
def runsOf : List (D y) → List (D y × Nat)
  | [] => []
  | d :: ds => match runsOf ds with
    | (e, m) :: rest => if Dag.beq d e then (e, m + 1) :: rest else (d, 1) :: (e, m) :: rest
    | [] => [(d, 1)]

end

end Tamarin.MaudeVariants
