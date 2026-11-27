import Tamarin.MaudeVariantsNarrow

/-!
# Maude's `get variants`: the folder and the search

The listing Maude 3.5.1 prints for `get variants in M : t .`
(`Mixfix/getVariants.cc`, `Higher/variantSearch.cc`, `Higher/variantFolder.cc`):

* the query's variables numbered by first occurrence in the query normalised
  without flattening AC products (`Interpreter::makeDag`,
  `DagNode::indexVariables`); the first variant renames variable `i` to the
  variant variable `i` and reduces the term (`VariantSearch::VariantSearch`);
* the frontier expanded layer by layer, each member still retained narrowed
  in frontier order (`VariantSearch::expandLayer`);
* each new variant offered to the folder (`VariantFolder::insertVariant`): it
  is dropped when a retained variant, ancestors included, subsumes it (one
  matcher for the term and every binding); otherwise it evicts every retained
  variant other than its ancestors that it subsumes, and their descendants,
  and is retained;
* after each layer, the retained variants not yet listed, in order of
  creation (`VariantFolder::findNextSurvivingVariant`); the search ends when a
  layer lists nothing.

The variant term, its printing, the `rewrites:` counts and the variable family
(`#` or `%`) are not computed beyond what the order of the listing needs:
the caller reads the bindings only.
-/
namespace Tamarin.MaudeVariants
open Tamarin MaudeUnify

variable {y : Syms}

/-- A variant kept by the folder, with its index of creation and its parent's. -/
structure Retained (y : Syms) where
  idx : Nat
  parent : Option Nat
  v : Variant y
  /-- The term and the bindings, as a tuple. -/
  tup : Tuple y

/-- The tuple of the folder: the term, then the bindings. -/
def Variant.tuple (v : Variant y) : Tuple y := Tuple.make (#[v.term] ++ v.subst) v.sorts

section
variable [Interrupt]

/-- `VariantFolder::subsumes`: `b` is an instance of `a`, term and bindings
matched at once. -/
def subsumesV (a b : Tuple y) : Bool := a.subsumes b

/-- The indices of the ancestors of a variant with parent `parent`. -/
def ancestors (folder : Array (Retained y)) : Nat → Option Nat → List Nat
  | 0, _ => []
  | _ + 1, none => []
  | n + 1, some i => i :: ancestors folder n ((folder.find? (·.idx == i)).bind (·.parent))

/-- `VariantFolder::insertVariant`: the folder with `v` retained, or `none`
when a retained variant subsumes it. -/
def insertVariant (folder : Array (Retained y)) (v : Variant y) (idx : Nat) (parent : Option Nat) :
    Option (Array (Retained y)) :=
  let tup := v.tuple
  if folder.any fun r => subsumesV r.tup tup then none else
  let anc := ancestors folder (folder.size + 1) parent
  let (_, kept) := folder.foldl (fun (evicted, kept) r =>
    Interrupt.guard (evicted, kept) fun _ =>
    if anc.contains r.idx then (evicted, kept.push r) else
    let parentGone := match r.parent with | some q => evicted.contains q | none => false
    if parentGone || subsumesV tup r.tup then (r.idx :: evicted, kept) else (evicted, kept.push r))
    (([] : List Nat), (#[] : Array (Retained y)))
  some (kept.push { idx, parent, v, tup })

/-- The state of the search between layers. -/
structure SearchSt (y : Syms) where
  folder : Array (Retained y)
  frontier : Array Nat
  next : Nat
  cache : UCache y

/-- Offer the children of the frontier member `i` to the folder. -/
def offerKids (i : Nat) (kids : List (Variant y)) (st : SearchSt y) : SearchSt y :=
  kids.foldl (fun st kv =>
    let idx := st.next
    let st := { st with next := idx + 1 }
    match insertVariant st.folder kv idx (some i) with
    | some f => { st with folder := f, frontier := st.frontier.push idx }
    | none => st) st

/-- Expand a layer: each member of `frontier` that is still retained is
narrowed, in order. `none` when a narrowing step gave up. -/
def expandLayer (th : Theory y) (fuel : Nat) (frontier : List Nat) (st : SearchSt y) : Option (SearchSt y) :=
  frontier.foldlM (fun st i =>
    Interrupt.guard none fun _ =>
    match st.folder.find? (·.idx == i) with
    | none => some st
    | some r => (narrow th fuel st.cache r.v).map fun (kids, cache) =>
      offerKids i kids.toList { st with cache }) st

/-- The layers from `st` on, at most `layers` of them: the variants listed
after each, appended to `out`. `none` when a step gave up or the layers ran
out. -/
def layersFrom (th : Theory y) (fuel : Nat) : Nat → Nat → SearchSt y → Array (Variant y) → Option (Array (Variant y))
  | 0, _, _, _ => none
  | n + 1, last, st, out =>
    if st.frontier.isEmpty then some out else
    Interrupt.guard none fun _ =>
    (expandLayer th fuel st.frontier.toList { st with frontier := #[] }).bind fun st' =>
      let listed := st'.folder.filter (·.idx > last)
      if listed.isEmpty then some out else
      layersFrom th fuel n (listed.foldl (fun m r => max m r.idx) last) st' (out ++ listed.map (·.v))

end

/-- The query prepared for the search: the root variant, and for each of its
variables (in Maude's numbering) the query variable it stands for. -/
def root [Interrupt] (th : Theory y) (fuel : Nat) (qsorts : Array SortId) (qnames : Array Nat) (query : D y) :
    Option (Variant y × Array Nat) :=
  let rq : Ranks (Sig y) := th.rt.ranks (qnames.getD · 0)
  let soq := fun i => qsorts[i]?
  let q0 := norm rq soq query
  let order := dfsVars #[] (normShallow rq soq query)
  let slotOf : Array Nat := order.zipIdx.foldl (fun a (v, j) => a.setIfInBounds v j)
    (Array.replicate qsorts.size 0)
  let sorts := order.map fun i => qsorts.getD i .msg
  let vs := fun j => sorts.getD j .msg
  (nf th vs fuel (norm th.rt.vranks (fun j => sorts[j]?) (rename (slotOf.getD · 0) q0))).map fun term =>
    ({ subst := (Array.range order.size).map .var, term, sorts }, order)

/-- Maude's listing of the variants of `query`, whose slot `i` is a query
variable of sort `qsorts[i]` and name code `qnames[i]`: the variants in order,
and the query variable each binding is for. `none` when the search gave up:
a unification or a reduction ran out of `fuel`, or there were more than
`layers` layers. -/
def variants [Interrupt] (th : Theory y) (fuel layers : Nat) (qsorts : Array SortId) (qnames : Array Nat)
    (query : D y) : Option (Array (Variant y) × Array Nat) := do
  let (r, order) ← root th fuel qsorts qnames query
  let st : SearchSt y :=
    { folder := #[{ idx := 0, parent := none, v := r, tup := r.tuple }], frontier := #[0], next := 1, cache := {} }
  let out ← layersFrom th fuel layers 0 st #[r]
  return (out, order)

end Tamarin.MaudeVariants
