import Tamarin.SessionTableWire

/-!
# The theory of a Tamarin file

What a theory file says about the algebra: which equational builtins it
enables, the arities of its other function symbols, how many AC symbols it
declares, and its user rewrite rules. From that alone this file builds the
packet words the existing exports read: the declarations, the node rows and the
rule roots, with the rules of the enabled builtins written out below.

Symbol ids are fixed. Free, C and AC symbols have separate id spaces. The
builtins have the small ids below; user free symbol `i` has id `base + i` and
user AC symbol `j` has id `base + j`.

Words of the packet: a declaration is `kind, id, arity, output sort, input
sorts…` with kind 2 free, 3 C, 4 AC; a node row is `0, variable, sort`,
`1, name, sort` or `kind, id, child row…` naming earlier rows; sorts are pub 0,
fresh 1, msg 2, node 3, nat 4.
-/
namespace Tamarin.Theory

/-- Sort codes (`TotalUnifyWire.sortCode`). -/
def msgSort : UInt64 := 2
def natSort : UInt64 := 4

/-! Ids of the builtin free symbols. -/
namespace Free
def exp : UInt64 := 0
def inv : UInt64 := 1
def one : UInt64 := 2
def dhNeutral : UInt64 := 3
def zero : UInt64 := 4
def pmult : UInt64 := 5
def tone : UInt64 := 6
end Free

/-! Ids of the builtin AC symbols. -/
namespace AC
def mult : UInt64 := 0
def xor : UInt64 := 1
def union : UInt64 := 2
def tplus : UInt64 := 3
end AC

/-! Id of the builtin C symbol. -/
namespace C
def em : UInt64 := 0
end C

/-- First id of the user symbols. -/
def base : UInt64 := 16

/-- Bound on the number of user free symbols, on their arities and on the
number of user AC symbols. -/
def limit : Nat := 4096

/-- What the theory file declares. `free` lists the arities of the free
symbols other than the builtins: the user functions and the symbols of the
rule-carrying builtins (pairing, encryption, signatures…), whose equations are
user rules. `ac` is the number of user AC symbols, all of sort msg. -/
structure Signature where
  dh : Bool
  xor : Bool
  bp : Bool
  mset : Bool
  nat : Bool
  free : Array UInt64
  ac : UInt64

/-- Bilinear pairing needs Diffie–Hellman. Counts and arities are at most `limit`. -/
def Signature.valid (sig : Signature) : Bool :=
  (!sig.bp || sig.dh) && sig.free.size ≤ limit && sig.free.all (·.toNat ≤ limit) &&
    sig.ac.toNat ≤ limit

/-- The symbols of the signature as `⟨kind, id, output sort, input sorts⟩`
(kind 2 free, 3 C, 4 AC). Every symbol has sort msg, except the natural-number
symbols `tplus : nat nat → nat` (AC) and `tone : → nat`. -/
def Signature.symbols (sig : Signature) : List Whole.Decl :=
  (if sig.dh then
    [⟨2, Free.exp, msgSort, [msgSort, msgSort]⟩, ⟨2, Free.inv, msgSort, [msgSort]⟩, ⟨2, Free.one, msgSort, []⟩,
     ⟨2, Free.dhNeutral, msgSort, []⟩, ⟨4, AC.mult, msgSort, [msgSort, msgSort]⟩] else []) ++
  (if sig.xor then [⟨4, AC.xor, msgSort, [msgSort, msgSort]⟩, ⟨2, Free.zero, msgSort, []⟩] else []) ++
  (if sig.bp then [⟨2, Free.pmult, msgSort, [msgSort, msgSort]⟩, ⟨3, C.em, msgSort, [msgSort, msgSort]⟩] else []) ++
  (if sig.mset then [⟨4, AC.union, msgSort, [msgSort, msgSort]⟩] else []) ++
  (if sig.nat then [⟨4, AC.tplus, natSort, [natSort, natSort]⟩, ⟨2, Free.tone, natSort, []⟩] else []) ++
  sig.free.toList.mapIdx (fun i arity => ⟨2, base + i.toUInt64, msgSort, List.replicate arity.toNat msgSort⟩) ++
  (List.range sig.ac.toNat).map (fun j => ⟨4, base + j.toUInt64, msgSort, [msgSort, msgSort]⟩)

/-- The declaration words of the signature. -/
def Signature.declarations (sig : Signature) : Array UInt64 :=
  (sig.symbols.flatMap fun d => [d.kind, d.id, d.inputs.length.toUInt64, d.output] ++ d.inputs).toArray

/-- The five flags as one word: dh 1, xor 2, bp 4, mset 8, nat 16. -/
def Signature.flags (sig : Signature) : UInt64 :=
  (if sig.dh then 1 else 0) + (if sig.xor then 2 else 0) + (if sig.bp then 4 else 0) +
    (if sig.mset then 8 else 0) + (if sig.nat then 16 else 0)

/-- How an export reads its signature arguments: `none` unless the flags are
those of a valid signature. -/
def Signature.ofWire (flags : UInt64) (free : Array UInt64) (ac : UInt64) : Option Signature :=
  let sig : Signature := ⟨flags &&& 1 != 0, flags &&& 2 != 0, flags &&& 4 != 0, flags &&& 8 != 0,
    flags &&& 16 != 0, free, ac⟩
  if sig.flags == flags && sig.valid then some sig else none

/-! ## Builtin rules -/

/-- A term of a builtin rule: a variable of sort msg or an application. -/
inductive Term where
  | var (i : UInt64)
  | app (kind id : UInt64) (args : List Term)

def x1 : Term := .var 1
def x2 : Term := .var 2
def x3 : Term := .var 3
def exp (a b : Term) : Term := .app 2 Free.exp [a, b]
def inv (a : Term) : Term := .app 2 Free.inv [a]
def one : Term := .app 2 Free.one []
def dhNeutral : Term := .app 2 Free.dhNeutral []
def mult (a b : Term) : Term := .app 4 AC.mult [a, b]
def xor (a b : Term) : Term := .app 4 AC.xor [a, b]
def zero : Term := .app 2 Free.zero []
def pmult (a b : Term) : Term := .app 2 Free.pmult [a, b]
def em (a b : Term) : Term := .app 3 C.em [a, b]

/-- Diffie–Hellman, oriented left to right. -/
def dhRules : List (Term × Term) := [
  (exp x1 one, x1),
  (exp (exp x1 x2) x3, exp x1 (mult x2 x3)),
  (exp dhNeutral x1, dhNeutral),
  (mult x1 one, x1),
  (inv (inv x1), x1),
  (inv one, one),
  (mult x1 (inv x1), one),
  (mult (inv x1) (inv x2), inv (mult x1 x2)),
  (mult (inv (mult x1 x2)) x2, inv x1),
  (inv (mult (inv x1) x2), mult x1 (inv x2)),
  (mult x1 (mult (inv x1) x2), x2),
  (mult (inv x1) (mult (inv x2) x3), mult (inv (mult x1 x2)) x3),
  (mult (inv (mult x1 x2)) (mult x2 x3), mult (inv x1) x3)]

/-- Exclusive or. -/
def xorRules : List (Term × Term) := [
  (xor x1 zero, x1),
  (xor x1 x1, zero),
  (xor x1 (xor x1 x2), x2)]

/-- Bilinear pairing. -/
def bpRules : List (Term × Term) := [
  (pmult one x1, x1),
  (pmult x3 (pmult x2 x1), pmult (mult x3 x2) x1),
  (em x1 (pmult x2 x3), exp (em x1 x3) x2)]

/-- The rules of the enabled builtins. Multisets and natural numbers have none. -/
def Signature.builtinRules (sig : Signature) : List (Term × Term) :=
  (if sig.dh then dhRules else []) ++ (if sig.xor then xorRules else []) ++
    (if sig.bp then bpRules else [])

mutual
/-- The rows of a term appended to `rows` in postorder: its root is the last row. -/
def Term.rows : Term → Array (Array UInt64) → Array (Array UInt64)
  | .var i, rows => rows.push #[0, i, msgSort]
  | .app kind id args, rows =>
    let (rows, children) := Term.argRows args rows #[]
    rows.push (#[kind, id] ++ children)

/-- The rows of the arguments, and the row of each argument's root. -/
def Term.argRows : List Term → Array (Array UInt64) → Array UInt64 → Array (Array UInt64) × Array UInt64
  | [], rows, roots => (rows, roots)
  | t :: ts, rows, roots =>
    let rows := t.rows rows
    Term.argRows ts rows (roots.push (rows.size - 1).toUInt64)
end

/-- Node rows and root pairs of a list of rules. -/
def ruleRows : List (Term × Term) → Array (Array UInt64) × Array UInt64 → Array (Array UInt64) × Array UInt64
  | [], acc => acc
  | (lhs, rhs) :: rest, (rows, roots) =>
    let rows := lhs.rows rows
    let l := rows.size - 1
    let rows := rhs.rows rows
    ruleRows rest (rows, roots ++ #[l.toUInt64, (rows.size - 1).toUInt64])

/-! ## Tables and packets -/

/-- A signature with the user rules: node rows (indices local, from 0) and
`(lhs, rhs)` root pairs into them. -/
structure Table extends Signature where
  nodes : Array (Array UInt64)
  rules : Array UInt64

/-- The words of a call. -/
structure Packet where
  ds : Array UInt64
  ns : Array (Array UInt64)
  es : Array UInt64

/-- Index `i` of a block of rows placed after `off` rows. An index at or past
`bound` names no row of the block and becomes `off + bound`. -/
def place (off bound : Nat) (i : UInt64) : UInt64 := (off + min i.toNat bound).toUInt64

/-- A block of rows placed after `off` rows. Row `k` may name only earlier
rows of the block: any other child index becomes `k` itself, which no row may
name. Variable and name rows have no children. -/
def moveRows (off : Nat) (rows : Array (Array UInt64)) : Array (Array UInt64) :=
  rows.mapIdx fun k row => match row.toList with
    | kind :: id :: children => if kind ≤ 1 then row else (kind :: id :: children.map (place off k)).toArray
    | _ => row

/-- The table packet: the declarations of the signature; the rows of the
builtin rules followed by the user rows; the builtin rule roots followed by the
user rule roots. -/
def Table.packet (T : Table) : Packet :=
  let (rows, roots) := ruleRows T.builtinRules (#[], #[])
  { ds := T.declarations
    ns := rows ++ moveRows rows.size T.nodes
    es := roots ++ T.rules.map (place rows.size T.nodes.size) }

/-- The further rows of a call on the table (terms of the call), numbered
from 0 in `extra`, placed after the table rows. -/
def Table.further (T : Table) (extra : Array (Array UInt64)) : Array (Array UInt64) :=
  moveRows T.packet.ns.size extra

/-- A row index of `extra` as a node index of the call. -/
def Table.term (T : Table) (extra : Array (Array UInt64)) (i : UInt64) : UInt64 :=
  place T.packet.ns.size extra.size i

/-! ## What a call reads -/

/-- The query of a unification or matching call: equations between the roots
`roots` of `nodes`, over the signature. -/
def Signature.query (sig : Signature) (nodes : Array (Array UInt64)) (roots : Array UInt64) :=
  if sig.valid then TotalUnifyWire.input sig.declarations nodes roots else none

/-- The rules of the table. -/
def Table.input (T : Table) :=
  if T.valid then TableWire.input T.packet.ds T.packet.ns T.packet.es #[] else none

/-- A single-path reduction call: the rules and the term at `root` of `extra`. -/
def Table.pathInput (T : Table) (extra : Array (Array UInt64)) (root : UInt64) :=
  if T.valid then
    TableWire.input T.packet.ds (T.packet.ns ++ T.further extra) T.packet.es #[T.term extra root]
  else none

/-- A session reduction call: the rules and the term at `root` of `extra`. -/
def Table.reduceInput (T : Table) (extra : Array (Array UInt64)) (root : UInt64) :=
  if T.valid then
    SessionReductionWire.input T.packet.ds T.packet.ns T.packet.es (T.further extra) (T.term extra root)
  else none

/-- A variant check call: the rules, the observations at `roots` of `extra`
and the members of `family`, each a list of (variable row, image row) pairs
of `extra`. -/
def Table.checkInput (T : Table) (extra : Array (Array UInt64)) (roots : Array UInt64)
    (family : Array (Array UInt64)) :=
  if T.valid then
    SessionVariantCheckWire.input T.packet.ds T.packet.ns T.packet.es (T.further extra)
      (roots.map (T.term extra)) (family.map (·.map (T.term extra)))
  else none

/-! ## The rules of a table, as terms -/

mutual
/-- A builtin rule term as a term over a decoded dictionary `d`: the variable
`i` is the variable with id `i` of sort msg, and an application is the free, C
or AC application of the declared symbol (`TotalUnifyWire.app`). `none` when a
symbol is not declared in `d` or is applied to the wrong number of arguments. -/
def Term.denote (d : TotalUnifyWire.Dictionary) : Term → Option (Tamarin.Term d.sig)
  | .var i => some (.var ⟨i.toNat, .msg⟩)
  | .app kind id args => do TotalUnifyWire.app d kind id (← Term.denoteArgs d args)

def Term.denoteArgs (d : TotalUnifyWire.Dictionary) : List Term → Option (List (Tamarin.Term d.sig))
  | [] => some []
  | t :: ts => do return (← t.denote d) :: (← Term.denoteArgs d ts)
end

/-- The rules of the enabled builtins as equations over `d`, in order. -/
def Signature.builtinEquations (sig : Signature) (d : TotalUnifyWire.Dictionary) :
    Option (List (Equation d.sig)) :=
  sig.builtinRules.mapM fun (lhs, rhs) => do return ⟨← lhs.denote d, ← rhs.denote d⟩

end Tamarin.Theory
