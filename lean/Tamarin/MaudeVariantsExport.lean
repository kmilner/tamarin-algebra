import Tamarin.MaudeVariantsSearch
import Tamarin.Theory

/-!
# Maude's `get variants` reply for a query of the Maude backend

A proposer export: it lists what Maude 3.5.1 lists for
`get variants in MSG : q .` on the module the Maude backend writes, given the
module's equations, the query and Maude's ranks of the module
(`Tamarin.MaudeVariantsSearch`). Nothing is promised about the reply; the
caller uses its family only once the contract export
`tamarin_theory_variant_check` has accepted it.

**Request.** The theory of a Tamarin file (`flags`, `free`, `ac`, as for
`tamarin_theory_unify`), whose symbols give the operators; the rank rows of
`Tamarin.MaudeUnifyExport` (rows 0 to 5) and a row 6 with the ranks of the
module's operators `list`, `cons` and `nil`; `fuel`, a bound on the depth of
every recursion of the search and on its number of layers; node rows; and the
roots: the query, then the left and right side of each equation of the module
in module order. A node row is `0, id, sort` (the variable `x<id>`),
`1, k, sort` (the name constant of argument `k`), `kind, id, children…` for a
symbol of the theory (kind 2 free, 3 C, 4 AC, with at least two children), or
`5, children…` for the arguments of a fact, which stand for
`list(cons(c1, cons(c2, … nil)))`. Children are earlier rows. Each root's
variables are its own: an equation's variables are not the query's. The code
of a variable's name is its identifier.

**Reply.** `#[1]`, then for each variant in Maude's order an empty row and one
row per variable of the query, in Maude's numbering of the query's
variables: `id, sort, tokens…`, the binding's term in postfix, three words a
token: `0, k, sort` for the variant's variable `k` (Maude's `#(k+1)` or
`%(k+1)`), `1, k, sort` for a name constant, `kind, id, arity` for an
application, an AC product as nested binary products. `#[3]` when the search
gave up; `#[0]` for a malformed request.
-/
namespace Tamarin.MaudeVariantsExport
open Tamarin MaudeUnify MaudeVariants

/-- The rank word at `row`, `i`, or 0. -/
def word (w : Array (Array UInt64)) (row i : Nat) : Nat := ((w.getD row #[]).getD i 0).toNat

/-- A wire sort as a sort of the module. -/
def msOfWire (c : UInt64) : MS := ((sortOfCode c.toNat).map MS.ofSort).getD .msg

/-- The symbols of the theory and the three list operators after the free
symbols: `list` at `wrap`, `cons` at `wrap + 1`, `nil` at `wrap + 2`. -/
structure Layout where
  syms : Syms
  wrap : Nat
  /-- Which ids name a free, a C and an AC symbol of the theory. -/
  freeOk : Array Bool
  commOk : Array Bool
  acOk : Array Bool

def layout (sig : Theory.Signature) : Layout :=
  let wrap := Theory.base.toNat + sig.free.size
  let free0 : Array (Array MS × MS) := Array.replicate (wrap + 3) (#[], .msg)
  let comm0 : Array MS := Array.replicate 1 .msg
  let ac0 : Array MS := Array.replicate (Theory.base.toNat + sig.ac.toNat) .msg
  let (free, comm, ac) := sig.symbols.foldl (fun (free, comm, ac) d =>
    let out := msOfWire d.output
    match d.kind with
    | 2 => (free.setIfInBounds d.id.toNat ((d.inputs.map msOfWire).toArray, out), comm, ac)
    | 3 => (free, comm.setIfInBounds d.id.toNat out, ac)
    | _ => (free, comm, ac.setIfInBounds d.id.toNat out)) (free0, comm0, ac0)
  let ok := fun (k n : Nat) => sig.symbols.foldl (fun (a : Array Bool) d =>
    if d.kind.toNat == k then a.setIfInBounds d.id.toNat true else a) (Array.replicate n false)
  let free := free.setIfInBounds wrap (#[.top], .top)
  let free := free.setIfInBounds (wrap + 1) (#[.top, .top], .top)
  let free := free.setIfInBounds (wrap + 2) (#[], .top)
  { syms := { free, comm, ac }, wrap, freeOk := ok 2 wrap, commOk := ok 3 1, acOk := ok 4 ac0.size }

/-- The ranks of the request (rows 0 to 6) on the layout. -/
def rankTable (lay : Layout) (w : Array (Array UInt64)) : RankTable where
  free := (Array.range (lay.wrap + 3)).map fun i =>
    if i < lay.wrap then word w 0 i else word w 6 (i - lay.wrap)
  comm := (w.getD 1 #[]).map (·.toNat)
  ac := (w.getD 2 #[]).map (·.toNat)
  atom := (w.getD 3 #[]).map (·.toNat)
  varSym := (w.getD 4 #[]).map (·.toNat)
  sortIndex := (w.getD 5 #[]).map (·.toNat)

/-- Bound on identifiers of variables and on the number of variables of a
variant: their codes have to stay below the names the narrowing gives the
variant's variables (`narrowName`). -/
def idLimit : Nat := 1 <<< 40

section
variable (lay : Layout)

/-- The fact wrapper of the arguments. -/
def wrapArgs (args : List (D lay.syms)) : D lay.syms :=
  .free lay.wrap [args.foldr (fun a rest => .free (lay.wrap + 1) [a, rest]) (.free (lay.wrap + 2) [])]

/-- The dag of a row from the dags of the earlier rows. A variable `x<id>` of
sort code `c` is the slot `8 * id + c` until the root is numbered. -/
def decodeRow (done : Array (D lay.syms)) (row : Array UInt64) : Option (D lay.syms) := do
  let child := fun (r : UInt64) => done[r.toNat]?
  match row.toList with
  | [0, id, c] => if c ≤ 4 && id.toNat < idLimit then some (.var (8 * id.toNat + c.toNat)) else none
  | [1, k, c] => if c ≤ 4 then some (.atom (atomOf k.toNat c.toNat)) else none
  | 2 :: id :: cs =>
    let f := id.toNat
    guard (lay.freeOk.getD f false && cs.length == (lay.syms.free.getD f (#[], .msg)).1.size)
    return .free f (← cs.mapM child)
  | [3, id, a, b] => do
    guard (lay.commOk.getD id.toNat false)
    return .comm id.toNat (← child a) (← child b)
  | 4 :: id :: cs => do
    guard (lay.acOk.getD id.toNat false && cs.length ≥ 2)
    return .ac id.toNat (← cs.mapM child)
  | 5 :: cs => return wrapArgs lay (← cs.mapM child)
  | _ => none

/-- The dags of the rows, `none` for a malformed row. -/
def decodeRows (rows : Array (Array UInt64)) : Option (Array (D lay.syms)) :=
  rows.foldlM (fun done row => (decodeRow lay done row).map done.push) #[]

/-- A root's variables numbered from 0 by first occurrence: the dag, and the
sort and name code of each slot. -/
def numbered (roots : List (D lay.syms)) : List (D lay.syms) × Array SortId × Array Nat :=
  let vs := roots.foldl dfsVars #[]
  let slotOf : Std.HashMap Nat Nat := vs.zipIdx.foldl (fun m (v, j) => m.insert v j) {}
  (roots.map (rename (slotOf.getD · 0)), vs.map (fun v => (sortOfCode (v % 8)).getD .msg), vs.map (· / 8))

/-- The postfix tokens of a binding over a variant's variables with sorts `vs`,
appended to `acc`. `none` for a list operator. -/
def tokens (vs : Array SortId) (acc : Array UInt64) : D lay.syms → Option (Array UInt64)
  | .var k => some (acc ++ #[0, k.toUInt64, (codeOfSort (vs.getD k .msg)).toUInt64])
  | .atom a => some (acc ++ #[1, (atomArg a).toUInt64, (a % 8).toUInt64])
  | .free f args => do
    guard (f < lay.wrap)
    let acc ← args.attach.foldlM (fun acc ⟨d, _⟩ => tokens vs acc d) acc
    return acc ++ #[2, f.toUInt64, args.length.toUInt64]
  | .comm f a b => do
    let acc ← tokens vs acc a
    let acc ← tokens vs acc b
    return acc ++ #[3, f.toUInt64, 2]
  | .ac f args => do
    guard (args.length ≥ 2)
    let acc ← args.attach.foldlM (fun acc ⟨d, _⟩ => tokens vs acc d) acc
    return acc ++ (Array.replicate (args.length - 1) #[4, f.toUInt64, 2]).flatten

end

/-- The give-up reply. -/
def gaveUp : Array (Array UInt64) := #[#[3]]

/-- The reply listing the variants: each binds the query variables `order`
(slots of the query, with their sorts and name codes). -/
def pack (lay : Layout) (qsorts : Array SortId) (qnames : Array Nat) (order : Array Nat)
    (out : Array (Variant lay.syms)) : Option (Array (Array UInt64)) :=
  out.foldlM (fun acc v => do
    guard (v.sorts.size < idLimit)
    let rows ← (v.subst.zipIdx).mapM fun (d, j) =>
      let q := order.getD j 0
      tokens lay v.sorts #[(qnames.getD q 0).toUInt64, (codeOfSort (qsorts.getD q .msg)).toUInt64] d
    return (acc.push #[]) ++ rows) #[#[1]]

section
variable [Interrupt]

/-- The reply to a decoded request. -/
def answer (lay : Layout) (w : Array (Array UInt64)) (fuel : Nat) (query : D lay.syms)
    (eqs : List (D lay.syms × D lay.syms)) : Array (Array UInt64) :=
  let rt := rankTable lay w
  let eqns := eqs.toArray.map fun (l, r) =>
    match numbered lay [l, r] with
    | ([l', r'], sorts, names) => mkEqn rt sorts names l' r'
    | _ => mkEqn rt #[] #[] l r
  let th := Theory.make rt eqns
  match numbered lay [query] with
  | ([q], qsorts, qnames) =>
    match variants th fuel fuel qsorts qnames q with
    | some (out, order) => (pack lay qsorts qnames order out).getD gaveUp
    | none => gaveUp
  | _ => gaveUp

/-- The export: `#[#[0]]` for a request that does not decode. -/
def run (flags : UInt64) (free : Array UInt64) (ac : UInt64) (w : Array (Array UInt64)) (fuel : UInt64)
    (nodes : Array (Array UInt64)) (roots : Array UInt64) : Array (Array UInt64) :=
  match Theory.Signature.ofWire flags free ac with
  | none => #[#[0]]
  | some sig =>
    let lay := layout sig
    match decodeRows lay nodes, roots.toList with
    | some done, q :: sides =>
      match done[q.toNat]?, (pairs sides).mapM fun (l, r) => do
          return ((← done[l.toNat]?), (← done[r.toNat]?)) with
      | some query, some eqs => if sides.length % 2 == 0 then answer lay w fuel.toNat query eqs else #[#[0]]
      | _, _ => #[#[0]]
    | _, _ => #[#[0]]
where
  pairs : List UInt64 → List (UInt64 × UInt64)
    | a :: b :: rest => (a, b) :: pairs rest
    | _ => []

end

end Tamarin.MaudeVariantsExport
