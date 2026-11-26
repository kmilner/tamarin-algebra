import Tamarin.MaudeVariantsMatch
import Std.Data.HashMap

/-!
# One step of Maude's variant narrowing

The equations of the module, reduction and reducibility by them, and one
narrowing step of a variant in the order of Maude 3.5.1
(`Higher/variantNarrowingSearchState.cc`):

* the positions of the variant's term breadth first, each distinct argument of
  an AC node once, variables skipped (`PositionState`);
* at each position the equations indexed under its top symbol, in module order;
* each equation's left side unified with the subterm by the port of Maude's
  unifier, the equation's variables in the first slots and the variant's after
  them, those of the term first (`NarrowingUnificationProblem`);
* a unifier dropped when it binds a variable of the term to a reducible term
  (`collectUnifiers`), the others filtered by subsumption on the variables of
  the term (`UnifierFilter`);
* the survivors in order, each giving a new variant unless its substitution is
  reducible (`findNextVariant`); the new term is reduced to normal form.

Variables of a variant are numbered from 0; variable `k` has the name code `k`
in the term order (`vranks`), so within a variant the codes increase with the
number, as Maude's names `#1, #2, …` (or `%1, …`) do.
-/
namespace Tamarin.MaudeVariants
open Tamarin MaudeUnify

/-- Maude's ranks of the module's symbols (see `Tamarin.MaudeUnifyExport`):
the free, C and AC symbols by id, the name operators by sort code, the
variable symbols and sort indices of the kind at 0 and of each sort at its code
plus one. -/
structure RankTable where
  free : Array Nat
  comm : Array Nat
  ac : Array Nat
  atom : Array Nat
  varSym : Array Nat
  sortIndex : Array Nat
  deriving Inhabited

def optCode : Option SortId → Nat
  | none => 0
  | some s => codeOfSort s + 1

variable {y : Syms}

/-- The ranks of the table with the name code `name j` for slot `j`. -/
def RankTable.ranks (rt : RankTable) (name : Nat → Nat) : Ranks (Sig y) where
  atom a := rt.atom.getD (a % 8) 0
  atomArg a := atomArg a
  free f := rt.free.getD f 0
  comm f := rt.comm.getD f 0
  ac f := rt.ac.getD f 0
  varSym o := rt.varSym.getD (optCode o) 0
  name := name
  sortIndex o := rt.sortIndex.getD (optCode o) 0

/-- The ranks inside a variant: variable `k` has the name code `k`. -/
def RankTable.vranks (rt : RankTable) : Ranks (Sig y) := rt.ranks id

/-- An equation of the module with its variables in Maude's slots: by first
occurrence in the normalised left side, then the right side
(`PreEquation::check`). `names` are the codes of their names. -/
structure Eqn (y : Syms) where
  lhs : D y
  rhs : D y
  sorts : Array SortId
  names : Array Nat
  top : Option (Nat × Nat)

/-- The module: the symbols' sorts and ranks and the variant equations in
module order, also indexed by top symbol. -/
structure Theory (y : Syms) where
  rt : RankTable
  eqs : Array (Eqn y)
  byTop : Std.HashMap (Nat × Nat) (Array (Eqn y))

/-- The equation with left side `lhs` and right side `rhs` over the slots
`0 … n-1` with the given sorts and name codes, its slots renumbered in
Maude's order. -/
def mkEqn (rt : RankTable) (sorts : Array SortId) (names : Array Nat) (lhs rhs : D y) : Eqn y :=
  let n := sorts.size
  let r0 : Ranks (Sig y) := rt.ranks fun i => names.getD i 0
  let so0 := fun i => sorts[i]?
  let l0 := norm r0 so0 lhs
  let order := dfsVars (dfsVars #[] l0) (norm r0 so0 rhs)
  let order := order ++ ((Array.range n).filter fun i => !order.contains i)
  let slotOf : Array Nat := order.zipIdx.foldl (fun a (v, j) => a.setIfInBounds v j) (Array.replicate n 0)
  let sorts' := order.map fun v => sorts.getD v .msg
  let names' := order.map fun v => names.getD v 0
  let r1 : Ranks (Sig y) := rt.ranks fun i => names'.getD i 0
  let so1 := fun i => sorts'[i]?
  let lhs' := norm r1 so1 (rename (slotOf.getD · 0) lhs)
  { lhs := lhs', rhs := norm r1 so1 (rename (slotOf.getD · 0) rhs), sorts := sorts', names := names',
    top := topKey lhs' }

def Theory.make (rt : RankTable) (eqs : Array (Eqn y)) : Theory y :=
  { rt, eqs, byTop := eqs.foldl (fun m e => match e.top with
      | some k => m.insert k ((m.getD k #[]).push e)
      | none => m) {} }

def Theory.at (th : Theory y) (key : Option (Nat × Nat)) : Array (Eqn y) :=
  match key with
  | some k => th.byTop.getD k #[]
  | none => #[]

section
variable [Interrupt]

/-- The match context of an equation's left side against a dag whose slots
have the sorts `vs`. -/
def Eqn.mc (e : Eqn y) (vs : Nat → SortId) : MC := { psort := (e.sorts.getD · .msg), ssort := vs }

/-- Whether some equation applies at the top of `t`, with extension at an AC top. -/
def reducibleTop (th : Theory y) (vs : Nat → SortId) (t : D y) : Bool :=
  (th.at (topKey t)).any fun e => (mtop (e.mc vs) e.sorts.size e.lhs t).isSome

/-- `DagNode::reducibleByVariantEquation`: some subterm is an instance of an
equation's left side. -/
def reducible (th : Theory y) (vs : Nat → SortId) : D y → Bool
  | .var _ => false
  | .atom _ => false
  | .free f args => args.attach.any (fun ⟨d, _⟩ => reducible th vs d) || reducibleTop th vs (.free f args)
  | .comm f a b => reducible th vs a || reducible th vs b || reducibleTop th vs (.comm f a b)
  | .ac f args => args.attach.any (fun ⟨d, _⟩ => reducible th vs d) || reducibleTop th vs (.ac f args)

/-- One rewrite at the top with the first equation (in module order) whose
left side matches, the result normalised. -/
def rewriteTop (th : Theory y) (vs : Nat → SortId) (t : D y) : Option (D y) :=
  (th.at (topKey t)).findSome? fun e =>
    (mtop (e.mc vs) e.sorts.size e.lhs t).map fun (σ, rest) =>
      let rhs := subst (fun i => (σ.getD i none).getD (.var 0)) e.rhs
      let res : D y := match rest, t with
        | [], _ => rhs
        | _ :: _, .ac f _ => .ac f (rhs :: rest)
        | _, _ => rhs
      norm th.rt.vranks (fun i => some (vs i)) res

/-- The normal form by innermost rewriting: arguments first, then the
equations of the top symbol. The theory is convergent modulo AC, so the
normal form does not depend on the strategy. `none` when `fuel`, a bound on
the depth of the recursion and on the rewrites at one node, runs out. -/
def nf (th : Theory y) (vs : Nat → SortId) : Nat → D y → Option (D y)
  | 0, _ => none
  | n + 1, t =>
    Interrupt.guard none fun _ =>
    let so := fun i => some (vs i)
    let r := th.rt.vranks
    let inner : Option (D y) := match t with
      | .free f args => (args.mapM (nf th vs n)).map fun as => .free f as
      | .comm f a b => do
        let a' ← nf th vs n a
        let b' ← nf th vs n b
        pure (Dag.mkComm r so f a' b')
      | .ac f args => (args.mapM (nf th vs n)).map fun as => .ac f (Dag.normAC r so f as)
      | d => some d
    inner.bind fun t' => match rewriteTop th vs t' with
      | some u => nf th vs n u
      | none => some t'

end

/-! ### Variants and positions -/

/-- A variant: the image of each query variable and the term, over the
variant's variables `0 … sorts.size - 1`. -/
structure Variant (y : Syms) where
  subst : Array (D y)
  term : D y
  sorts : Array SortId

def Variant.sortFn (v : Variant y) : Nat → SortId := fun i => v.sorts.getD i .msg

/-- The children of a position: the arguments of a free or C node, the
distinct arguments of an AC node, each with its index (into the runs for an
AC node). The path is kept reversed. -/
def kids (path : List Nat) : D y → List (List Nat × D y)
  | .free _ args => args.zipIdx.map fun (a, j) => (j :: path, a)
  | .comm _ a b => [(0 :: path, a), (1 :: path, b)]
  | .ac _ args => (runsOf args).zipIdx.map fun ((a, _), j) => (j :: path, a)
  | _ => []

/-- The positions of `t` breadth first, with their reversed paths
(`PositionState::exploreNextPosition`). -/
def positions (t : D y) : Array (List Nat × D y) :=
  go (Dag.size t + 1) #[([], t)] #[]
where
  go : Nat → Array (List Nat × D y) → Array (List Nat × D y) → Array (List Nat × D y)
    | 0, _, acc => acc
    | n + 1, level, acc =>
      if level.isEmpty then acc else go n (level.flatMap fun (p, d) => (kids p d).toArray) (acc ++ level)

/-- Replace the subterm at `path` by `repl`, instantiating the rest with `θ`
(`PositionState::rebuildAndInstantiateDag`). An AC argument with
multiplicity has one occurrence replaced. -/
def rebuild (θ : Nat → D y) (t : D y) (path : List Nat) (repl : D y) : D y :=
  match path with
  | [] => repl
  | j :: rest =>
    match t with
    | .free f args => .free f (args.zipIdx.map fun (a, i) => if i == j then rebuild θ a rest repl else subst θ a)
    | .comm f a b =>
      if j == 0 then .comm f (rebuild θ a rest repl) (subst θ b) else .comm f (subst θ a) (rebuild θ b rest repl)
    | .ac f args =>
      match (runsOf args)[j]? with
      | some (e, _) =>
        let others := (removeOne e args).getD args
        .ac f (rebuild θ e rest repl :: others.map (subst θ))
      | none => subst θ t
    | d => subst θ d

/-! ### The narrowing step -/

/-- A unifier of an equation's left side with a subterm: the images of the
equation's variables and of the variant's (in the order of `Frame.tv`), the
sorts of its variables, and where and with which right side it applies. -/
structure Unifier (y : Syms) where
  eImgs : Array (D y)
  tImgs : Array (D y)
  sorts : Array SortId
  path : List Nat
  rhs : D y

/-- A variant prepared for narrowing: its variables by first occurrence, those
of the term first (`tv`), the place of each variable in that order (`tvIdx`),
and the number of variables of the term (`nInt`), the interesting ones. -/
structure Frame (y : Syms) where
  v : Variant y
  tv : Array Nat
  tvIdx : Array Nat
  nInt : Nat

def Frame.of (v : Variant y) : Frame y :=
  let tvTerm := dfsVars #[] v.term
  let tv := v.subst.foldl dfsVars tvTerm
  { v, tv, nInt := tvTerm.size,
    tvIdx := tv.zipIdx.foldl (fun a (k, j) => a.setIfInBounds k j) (Array.replicate v.sorts.size 0) }

/-- `subsumes a b`: the interesting bindings of `b` are an instance of those
of `a` (`UnifierFilter`). -/
def Unifier.subsumes [Interrupt] (nInt : Nat) (a b : Unifier y) : Bool :=
  mtPairs { psort := (a.sorts.getD · .msg), ssort := (b.sorts.getD · .msg) } a.sorts.size
    (a.tImgs.extract 0 nInt).toList (b.tImgs.extract 0 nInt).toList

/-- Offer a unifier to the filter: dropped if a retained one subsumes it,
otherwise it evicts those it subsumes and is appended. -/
def offer [Interrupt] (nInt : Nat) (filter : Array (Unifier y)) (u : Unifier y) : Array (Unifier y) :=
  if filter.any (·.subsumes nInt u) then filter
  else (filter.filter fun old => !u.subsumes nInt old).push u

section
variable [Interrupt]

/-- The code of the name of slot `j` of a narrowing problem with `ne` slots of
the equation (names `names`) and the variant's variables `tv` after them:
an equation variable has its own code, below every variant variable's. -/
def narrowName (names : Array Nat) (tv : Array Nat) (ne : Nat) (j : Nat) : Nat :=
  if j < ne then names.getD j 0
  else if j < ne + tv.size then (1 <<< 40) + tv.getD (j - ne) 0
  else (1 <<< 41) + j

/-- The unifiers of the equation `e` at the subterm `node` of the variant,
those that bind a variable of the term to a reducible term dropped, offered
in order to the filter. `none` when the unifier gave up. -/
def offerAt (th : Theory y) (fuel : Nat) (fr : Frame y) (path : List Nat) (node : D y) (e : Eqn y)
    (filter : Array (Unifier y)) : Option (Array (Unifier y)) :=
  let ne := e.sorts.size
  let tvSorts := fr.tv.toList.map fr.v.sortFn
  let sorts : List SortId := e.sorts.toList ++ tvSorts
  let r1 : Ranks (Sig y) := th.rt.ranks (narrowName e.names fr.tv ne)
  let tgt := rename (fun k => ne + fr.tvIdx.getD k 0) node
  match MaudeUnify.unify r1 fuel sorts [(e.lhs, tgt)] with
  | .gaveUp => none
  | .fail => some filter
  | .ok answers =>
    some <| answers.foldl (fun filter a =>
      Interrupt.guard filter fun _ =>
      let outSorts := a.sorts.toArray
      let soN := fun j => outSorts[j]?
      let vsN := fun j => outSorts.getD j .msg
      let imgs := a.images.toArray.map (norm th.rt.vranks soN)
      let u : Unifier y := { eImgs := imgs.extract 0 ne, tImgs := imgs.extract ne (ne + fr.tv.size),
                             sorts := outSorts, path, rhs := e.rhs }
      if (u.tImgs.extract 0 fr.nInt).any (reducible th vsN) then filter
      else offer fr.nInt filter u) filter

/-- The filter after every position and equation. -/
def collect (th : Theory y) (fuel : Nat) (fr : Frame y) :
    List (List Nat × D y) → Array (Unifier y) → Option (Array (Unifier y))
  | [], filter => some filter
  | (path, node) :: rest, filter =>
    let step := (th.at (topKey node)).foldl (fun acc e => acc.bind fun filter =>
      Interrupt.guard none fun _ => offerAt th fuel fr path.reverse node e filter) (some filter)
    step.bind (collect th fuel fr rest)

/-- The variant a surviving unifier gives, or `some none` when its
substitution is reducible; `none` when the reduction ran out of fuel. -/
def child (th : Theory y) (fuel : Nat) (fr : Frame y) (u : Unifier y) : Option (Option (Variant y)) :=
  Interrupt.guard none fun _ =>
  let vsN := fun j => u.sorts.getD j .msg
  let soN := fun j => u.sorts[j]?
  let θ := fun k => u.tImgs.getD (fr.tvIdx.getD k 0) (.var 0)
  let newSubst := fr.v.subst.map fun d => norm th.rt.vranks soN (subst θ d)
  if newSubst.any (reducible th vsN) then some none else
  let repl := subst (fun j => u.eImgs.getD j (.var 0)) u.rhs
  (nf th vsN fuel (rebuild θ fr.v.term u.path repl)).map fun t =>
    some { subst := newSubst, term := t, sorts := u.sorts }

/-- One narrowing step of `v`: the new variants in Maude's order. `none` when
the unifier or a reduction gave up. -/
def narrow (th : Theory y) (fuel : Nat) (v : Variant y) : Option (Array (Variant y)) := do
  let fr := Frame.of v
  let filter ← collect th fuel fr (positions v.term).toList #[]
  filter.foldlM (fun out u => (child th fuel fr u).map fun c => match c with
    | some w => out.push w
    | none => out) #[]

end

end Tamarin.MaudeVariants
