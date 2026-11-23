import Tamarin.VariantCertificate
import Tamarin.VariantCheckWire
import Tamarin.TableAmbient
import Tamarin.TableWire

/-! A proposer of variant families: folding variant narrowing in the order of
Maude's `VariantSearch` and `VariantFolder`, built from the pieces of the
closure test of the certificate checker. Where the checker asks whether every
normalized narrowing successor of a member is an instance of a member, this
search keeps the successors that are not.

The variants are generated layer by layer. A new variant that is an instance
of a retained one is dropped. A new variant that is kept evicts the retained
variants it subsumes, except its own ancestors, together with their
descendants. A layer is listed when it is complete, so a variant that a later
layer evicts stays listed, as in Maude's plain `get variants`.

Nothing is proved about the result and nothing has to be: the family is a
proposal, and the caller uses it only after the certificate checker accepted
it. -/
namespace Tamarin.VariantFold
open Rewriting VariantJoin MaudeOperations ReferenceVariantFrontier TupleNarrowingFrontier
open VariantCertificate
variable {s : Signature} {n : Nat} {rules : List (Equation s)}
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

/-- A retained variant: its number, the number of the variant it was narrowed
from, and the terms it is compared on (images of the keys, then values). -/
structure Entry (s : Signature) (n : Nat) where
  id : Nat
  parent : Option Nat
  row : List (Term s)
  point : Point s n

inductive Outcome (s : Signature) (n : Nat) where
  | found (members : List (Point s n))
  | exhausted
  | declined

structure Search (rules : List (Equation s)) (bound : ReferenceReduction.Bound rules) (n : Nat) where
  memo : Memo rules bound
  live : Array (Entry s n)
  next : Nat
  fresh : Array Nat
  spent : Nat
  failed : Bool

/-- Whether an instance of the first row is the second one. The complete
matcher is asked only about rows that pass the cheap necessary condition. -/
def above (general specific : List (Term s)) : Bool :=
  plausibleAll general specific && (guessedInstance general specific || instanceOf general specific)

/-- The numbers of a variant and of the variants it descends from. -/
def lineage (live : Array (Entry s n)) : Nat → Nat → List Nat
  | 0, id => [id]
  | fuel + 1, id =>
    match live.find? fun e => e.id == id with
    | some e =>
      match e.parent with
      | some p => id :: lineage live fuel p
      | none => [id]
    | none => [id]

/-- Add a successor of the variant `parent` unless a retained variant
subsumes it. -/
def insert {bound : ReferenceReduction.Bound rules} (query : Fin n → Term s) (keys : List Variable)
    (parent : Nat) (st : Search rules bound n) (images values : List (Term s)) : Search rules bound n :=
  let row := images ++ values
  if st.live.any (fun e => plausibleAll e.row row && guessedInstance e.row row) ||
      st.live.any (fun e => plausibleAll e.row row && instanceOf e.row row) then st
  else
    match VariantCheckWire.assign ((keys.zip images).map fun e => (⟨.var e.1,e.2⟩ : Equation s)) with
    | none => { st with failed := true }
    | some σ =>
      let kin := lineage st.live st.live.size parent
      let swept := st.live.foldl (fun (acc : Array (Entry s n) × List Nat) e =>
        if kin.contains e.id then (acc.1.push e,acc.2)
        else if (e.parent.any acc.2.contains) || above row e.row then (acc.1,e.id :: acc.2)
        else (acc.1.push e,acc.2)) (#[],[])
      { st with
        live := swept.1.push ⟨st.next,some parent,row,frozen σ query values⟩
        next := st.next + 1
        fresh := st.fresh.push st.next }

/-- One narrowing layer of a variant: every successor with normal images,
normalized, is offered to the retained variants. -/
def expand (bound : ReferenceReduction.Bound rules) (query : Fin n → Term s) (keys : List Variable)
    (fuel : Nat) (st : Search rules bound n) (e : Entry s n) : Search rules bound n :=
  let p := e.point
  let keyCells := (keys.map p.assignment.image).map (keyCell rules)
  let valueCells := (List.finRange n).map (valueCell rules fuel p.value)
  let avoid := (TableNarrowing.cells keys p).flatMap Term.variables
  (List.finRange n).foldl (fun (st : Search rules bound n) j =>
    if st.failed || idle (query j) then st
    else
      let found := positionsS (rootsS bound avoid) st.memo.1 (p.value j)
      let st := { st with memo := (found.1,st.memo.2), spent := st.spent + found.2.length }
      found.2.foldl (fun (st : Search rules bound n) b =>
        if st.failed then st
        else
          match quietCells rules b.subst st.memo.2 keyCells with
          | (more,true) =>
            let st := { st with memo := (st.memo.1,more) }
            match settleF rules fuel more j b valueCells with
            | none => { st with failed := true }
            | some values => insert query keys e.id st (imagesF b.subst keyCells) values
          | (more,false) => { st with memo := (st.memo.1,more) }) st) st

/-- The layers, each listed when it is complete. `work`, when nonzero, bounds
the positions at which root branches are looked for plus the branches found. -/
def layers (bound : ReferenceReduction.Bound rules) (query : Fin n → Term s) (keys : List Variable)
    (fuel work : Nat) : Nat → Search rules bound n → List Nat → Nat → List (Point s n) → Outcome s n
  | 0, _, _, _, _ => .exhausted
  | rounds + 1, st, frontier, listed, out =>
    let st := frontier.foldl (fun (st : Search rules bound n) id =>
      if st.failed || (work != 0 && decide (work < st.spent)) then st
      else
        match st.live.find? fun e => e.id == id with
        | none => st
        | some e => expand bound query keys fuel { st with spent := st.spent + charge query e.point } e)
      { st with fresh := #[] }
    if st.failed || (work != 0 && decide (work < st.spent)) then .exhausted
    else
      let out := out ++ ((st.live.filter fun e => decide (listed ≤ e.id)).toList.map (·.point))
      if st.fresh.isEmpty then .found out
      else layers bound query keys fuel work rounds st st.fresh.toList st.next out

/-- Folding variant narrowing from the normalized query. -/
def search (rules : List (Equation s)) (q : List (Term s)) (fuel work : Nat) :
    Outcome s q.length × List Variable :=
  let query := fun i : Fin q.length => q[i.val]
  let keys := keysOf query
  if hb : CheckedReduction.rangeBound rules then
    if rules.all (fun r => CheckedVariants.nonvar r.lhs) then
      let bound := (CheckedReduction.rangeBound_iff rules).mp hb
      match settle rules fuel query with
      | none => (.exhausted,keys)
      | some first =>
        let seed : Entry s q.length :=
          ⟨0,none,keys.map (Substitution.identity (sig := s)).image ++ first,
            frozen .identity query first⟩
        let st : Search rules bound q.length :=
          ⟨(Array.replicate 4096 [],Array.replicate 4096 []),#[seed],1,#[],0,false⟩
        (layers bound query keys fuel work (if work == 0 then 1 <<< 32 else work + 1) st [0] 1
          [seed.point],keys)
    else (.declined,keys)
  else (.declined,keys)

end Tamarin.VariantFold

namespace Tamarin.FoldVariantsWire
open TotalUnifyWire ReferenceVariantFrontier

/-- The reply of the variant proposer in the form of the other variant
exports: status 1 with one row of bindings per variant, status 2 when the
table is outside the search or a variant does not fit the wire, status 3 when
`fuel` rewrite steps or `work` narrowing sites did not suffice, and status 0
for a malformed packet. -/
def run (ds : Array UInt64) (ns : Array (Array UInt64)) (rules roots : Array UInt64)
    (fuel work : UInt64) : Array (Array UInt64) :=
  match TableWire.input ds ns rules roots with
  | none => #[#[0]]
  | some ⟨_,rs,q⟩ =>
    match VariantFold.search (TableAmbient.liftRules rs) (q.map TableAmbient.liftTerm)
        fuel.toNat work.toNat with
    | (.found members,keys) => (TableAmbient.emit q (members.map (Point.answer · keys))).getD #[#[2]]
    | (.exhausted,_) => #[#[3]]
    | (.declined,_) => #[#[2]]

end Tamarin.FoldVariantsWire
