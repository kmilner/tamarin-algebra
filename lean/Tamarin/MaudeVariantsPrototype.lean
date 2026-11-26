import Tamarin.MaudeUnifyAlgorithm

/-!
# Prototype: Maude's `get variants` reply, computed on top of the port of Maude's unifier

UNPROVED PROTOTYPE. Nothing in `TamarinCI` or `TamarinRuntime` imports this
module. It uses `partial def` throughout and carries no theorems; it exists to
pin down, against captured Maude replies, exactly what Maude 3.5.1's folding
variant narrowing (`VariantSearch`, `VariantNarrowingSearchState`,
`UnifierFilter`, `VariantFolder`) does, so that a proved version can follow it.

What it reproduces (Maude source in brackets):

* the initial variant: the query's variables, numbered by first occurrence in
  the query normalised with Maude's term order, renamed to `#1, #2, …`, the
  term reduced (`VariantSearch::VariantSearch`);
* layer-by-layer expansion of the surviving variants, the first layer in
  family `%`, then alternating (`VariantSearch::expandLayer`);
* one narrowing step of a variant: positions of its term breadth first,
  each distinct AC argument once (`PositionState`, `stackPhysicalArguments`);
  at each non-variable position the variant equations of its top symbol in
  module order; each equation's left side unified with the subterm by the port
  of Maude's unifier, the equation's variables in the first slots and the
  variant's variables after them, those of the term first
  (`NarrowingUnificationProblem`); unifiers that bind a variable of the term
  to a reducible term dropped (`VariantNarrowingSearchState::collectUnifiers`);
  the others filtered by subsumption on the variables of the term
  (`UnifierFilter`); the survivors in order, each giving a new variant unless
  its substitution is reducible (`VariantNarrowingSearchState::findNextVariant`);
* the new variant term reduced to normal form (`expandVariant`);
* folding: a new variant subsumed by a retained one is dropped; a new one
  evicts every retained non-ancestor it subsumes, and their descendants
  (`VariantFolder::insertVariant`);
* the listing: after each layer, the surviving variants not yet printed, in
  order of creation (`VariantFolder::findNextSurvivingVariant`).

Variables are numbered within a variant: variable `k` is printed `#(k+1)` or
`%(k+1)` by the variant's family. All variables of one variant are of one
family, so the codes of their names, which order them in Maude's term order,
increase with `k`.
-/
namespace Tamarin.MaudeVariantsPrototype
open Tamarin Tamarin.MaudeUnify

instance : Inhabited SortId := ⟨.msg⟩

structure FD where
  inputs : Array SortId
  output : SortId

instance : Inhabited FD := ⟨⟨#[], .msg⟩⟩

abbrev Sig (free : Array FD) (comm ac atoms : Array SortId) : Signature where
  FreeSym := Nat
  CSym := Nat
  ACSym := Nat
  Atom := Nat
  arity f := (free.getD f { inputs := #[], output := .msg }).inputs.size
  inputSort f i := (free.getD f { inputs := #[], output := .msg }).inputs.getD i.val .msg
  outputSort f := (free.getD f { inputs := #[], output := .msg }).output
  cSort f := comm.getD f .msg
  acSort f := ac.getD f .msg
  atomSort a := atoms.getD a .msg

/-- The sorts of the MSG module and its kind, for sort checks of matching. -/
inductive MS where
  | pub | fresh | msg | node | nat | top | kind
  deriving DecidableEq, Inhabited, Repr

def MS.le (a b : MS) : Bool :=
  a == b || match a, b with
    | .pub, .msg | .fresh, .msg | .nat, .msg => true
    | .pub, .top | .fresh, .top | .nat, .top | .msg, .top | .node, .top => true
    | _, _ => false

def MS.ofSort : SortId → MS
  | .pub => .pub | .fresh => .fresh | .msg => .msg | .node => .node | .nat => .nat

def MS.ofCode : Nat → MS
  | 0 => .pub | 1 => .fresh | 2 => .msg | 3 => .node | 4 => .nat | _ => .top

def MS.name : MS → String
  | .pub => "Pub" | .fresh => "Fresh" | .msg => "Msg" | .node => "Node" | .nat => "TamNat"
  | .top => "TOP" | .kind => "[TOP]"

def sortOfCode : Nat → SortId
  | 0 => .pub | 1 => .fresh | 2 => .msg | 3 => .node | _ => .nat

def sortName (x : SortId) : String := (MS.ofSort x).name

def optCode : Option SortId → Nat
  | none => 0
  | some x => match x with
    | .pub => 1 | .fresh => 2 | .msg => 3 | .node => 4 | .nat => 5

/-- Raw terms of the problem file. -/
inductive R where
  | v (i : Nat)
  | a (i : Nat)
  | f (i : Nat) (args : Array R)
  | c (i : Nat) (l r : R)
  | ac (i : Nat) (args : Array R)
  deriving Inhabited

structure REq where
  sorts : Array SortId
  names : Array Nat
  lhs : R
  rhs : R
  deriving Inhabited

structure Prob where
  id : String := ""
  free : Array FD := #[]
  freeMS : Array (Array MS × MS) := #[]
  comm : Array SortId := #[]
  ac : Array SortId := #[]
  atoms : Array SortId := #[]
  rf : Array Nat := #[]
  rc : Array Nat := #[]
  ra : Array Nat := #[]
  rt : Array Nat := #[]
  rg : Array Nat := #[]
  rv : Array Nat := #[]
  rs : Array Nat := #[]
  fnames : Array String := #[]
  cnames : Array String := #[]
  anames : Array String := #[]
  tnames : Array (String × Nat) := #[]
  eqs : Array REq := #[]
  qvars : Array (SortId × Nat × String) := #[]
  query : R := .v 0
  deriving Inhabited

abbrev S (p : Prob) : Signature := Sig p.free p.comm p.ac p.atoms
abbrev D (p : Prob) := Dag (S p)

instance (p : Prob) : Inhabited (D p) := ⟨.var 0⟩

section
variable (p : Prob)

def ranks (name : Nat → Nat) : Ranks (S p) where
  atom a := p.rt.getD a 0
  atomArg a := p.rg.getD a 0
  free f := p.rf.getD f 0
  comm f := p.rc.getD f 0
  ac f := p.ra.getD f 0
  varSym o := p.rv.getD (optCode o) 0
  name := name
  sortIndex o := p.rs.getD (optCode o) 0

/-- Maude's theory normal form under ranks: AC arguments flattened and sorted,
C arguments ordered. -/
partial def norm (r : Ranks (S p)) (so : Nat → Option SortId) : D p → D p
  | .free f args => .free f (args.map (norm r so))
  | .comm f a b => Dag.mkComm r so f (norm r so a) (norm r so b)
  | .ac f args => .ac f (Dag.normAC r so f (args.map (norm r so)))
  | d => d

partial def ofR (slot : Nat → Nat) : R → D p
  | .v i => .var (slot i)
  | .a i => .atom i
  | .f i args => .free i (args.toList.map (ofR slot))
  | .c i l rr => .comm i (ofR slot l) (ofR slot rr)
  | .ac i args => .ac i (args.toList.map (ofR slot))

/-- The least sort of a dag, the kind if it is ill sorted. -/
partial def msort (vs : Nat → SortId) : D p → MS
  | .var i => MS.ofSort (vs i)
  | .atom a => MS.ofSort (p.atoms.getD a .msg)
  | .free f args =>
    let (ins, out) := p.freeMS.getD f (#[], .msg)
    if (args.zipIdx.all fun (a, i) => (msort vs a).le (ins.getD i .msg)) then out else .kind
  | .comm f a b =>
    let c := MS.ofSort (p.comm.getD f .msg)
    if (msort vs a).le c && (msort vs b).le c then c else .kind
  | .ac f args =>
    let c := MS.ofSort (p.ac.getD f .msg)
    if args.all fun a => (msort vs a).le c then c else .kind

/-- Variables by first occurrence, depth first, left to right. -/
partial def dfsVars (acc : Array Nat) : D p → Array Nat
  | .var i => if acc.contains i then acc else acc.push i
  | .atom _ => acc
  | .free _ args => args.foldl (dfsVars) acc
  | .comm _ a b => dfsVars (dfsVars acc a) b
  | .ac _ args => args.foldl (dfsVars) acc

partial def inst (θ : Nat → D p) : D p → D p
  | .var i => θ i
  | .atom a => .atom a
  | .free f args => .free f (args.map (inst θ))
  | .comm f a b => .comm f (inst θ a) (inst θ b)
  | .ac f args => .ac f (args.map (inst θ))

def beqD (a b : D p) : Bool := Dag.beq a b

/-- The top symbol as a key: 0 free, 1 C, 2 AC. -/
def topKey : D p → Option (Nat × Nat)
  | .free f _ => some (0, f)
  | .comm f _ _ => some (1, f)
  | .ac f _ => some (2, f)
  | _ => none

/-! ### Matching modulo AC and C (boolean, or the first match) -/

abbrev Sb := Array (Option (D p))

structure MC where
  psort : Nat → SortId
  ssort : Nat → SortId

def isVar : D p → Bool
  | .var _ => true
  | _ => false

/-- Remove one occurrence of `x`. -/
def removeOne (x : D p) : List (D p) → Option (List (D p))
  | [] => none
  | y :: ys => if beqD p x y then some ys else (removeOne x ys).map (y :: ·)

def removeAll (xs ys : List (D p)) : Option (List (D p)) :=
  xs.foldlM (fun acc x => removeOne p x acc) ys

/-- Runs of equal adjacent elements. -/
def runsOf : List (D p) → List (D p × Nat)
  | [] => []
  | d :: ds => match runsOf ds with
    | (e, m) :: rest => if beqD p d e then (e, m + 1) :: rest else (d, 1) :: (e, m) :: rest
    | [] => [(d, 1)]

mutual
partial def mt {α : Type} (c : MC) (pt t : D p) (σ : Sb p) (k : Sb p → Option α) : Option α :=
  match pt with
  | .var i =>
    match σ.getD i none with
    | some b => if beqD p b t then k σ else none
    | none => if (msort p c.ssort t).le (MS.ofSort (c.psort i)) then k (σ.set! i (some t)) else none
  | .atom a => match t with
    | .atom b => if a == b then k σ else none
    | _ => none
  | .free f ps => match t with
    | .free g ts => if f == g && ps.length == ts.length then mtList c ps ts σ k else none
    | _ => none
  | .comm f a b => match t with
    | .comm g x y =>
      if f == g then
        (mt c a x σ fun σ => mt c b y σ k) <|> (mt c a y σ fun σ => mt c b x σ k)
      else none
    | _ => none
  | .ac f ps => match t with
    | .ac g ts => if f == g then mac c f ps ts σ false (fun σ rest => if rest.isEmpty then k σ else none) else none
    | _ => none

partial def mtList {α : Type} (c : MC) (ps ts : List (D p)) (σ : Sb p) (k : Sb p → Option α) : Option α :=
  match ps, ts with
  | [], [] => k σ
  | q :: qs, t :: ts => mt c q t σ fun σ => mtList c qs ts σ k
  | _, _ => none

/-- AC matching of the arguments `ps` of a pattern against the subject
arguments `ss`; with `ext` the subject may keep arguments over, passed to `k`. -/
partial def mac {α : Type} (c : MC) (f : Nat) (ps ss : List (D p)) (σ : Sb p) (ext : Bool)
    (k : Sb p → List (D p) → Option α) : Option α :=
  match ps.findIdx? (fun d => !isVar p d) with
  | some i =>
    let q := ps[i]!
    let rest := ps.eraseIdx i
    let rec tryEach (before : List (D p)) (prev : Option (D p)) : List (D p) → Option α
      | [] => none
      | s :: more =>
        let skip := match prev with | some x => beqD p x s | none => false
        if skip then tryEach (before ++ [s]) prev more else
        (mt c q s σ fun σ' => mac c f rest (before ++ more) σ' ext k) <|>
          tryEach (before ++ [s]) (some s) more
    tryEach [] none ss
  | none =>
    -- only variables: bound ones take their factors, unbound ones share the rest
    let vs : List Nat := ps.filterMap fun d => match d with | .var i => some i | _ => none
    let groups : List (Nat × Nat) := vs.foldl (fun acc v =>
      match acc.findIdx? (·.1 == v) with
      | some j => acc.modify j fun (x, m) => (x, m + 1)
      | none => acc ++ [(v, 1)]) []
    let bound := groups.filter fun (x, _) => (σ.getD x none).isSome
    let unbound := groups.filter fun (x, _) => (σ.getD x none).isNone
    let need : List (D p) := bound.flatMap fun (x, m) =>
      let b := (σ.getD x none).get!
      let parts := match b with
        | .ac g bs => if g == f then bs else [b]
        | _ => [b]
      (List.replicate m parts).flatten
    match removeAll p need ss with
    | none => none
    | some ss' => distribute c f unbound ss' σ ext k

partial def distribute {α : Type} (c : MC) (f : Nat) (vars : List (Nat × Nat)) (ss : List (D p)) (σ : Sb p)
    (ext : Bool) (k : Sb p → List (D p) → Option α) : Option α :=
  match vars with
  | [] => if ss.isEmpty then k σ [] else if ext then k σ ss else none
  | (x, m) :: more =>
    let rs := runsOf p ss
    let last := more.isEmpty && !ext
    -- choices of counts for each run
    let rec choose (rs : List (D p × Nat)) (taken left : List (D p)) : Option α :=
      match rs with
      | [] =>
        if taken.isEmpty then none else
        let b : D p := match taken with | [t] => t | _ => .ac f taken
        if (msort p c.ssort b).le (MS.ofSort (c.psort x)) then
          distribute c f more left (σ.set! x (some b)) ext k
        else none
      | (e, n) :: rest =>
        let maxc := n / m
        let rec go (j : Nat) (fuel : Nat) : Option α :=
          match fuel with
          | 0 => none
          | fuel + 1 =>
            if j > maxc then none else
            if last && j * m != n then go (j + 1) fuel else
            choose rest (taken ++ List.replicate j e) (left ++ List.replicate (n - j * m) e) <|> go (j + 1) fuel
        go 0 (maxc + 2)
    choose rs [] []
end

/-- Match at the top, with extension when the pattern is an AC product. -/
def mtop (c : MC) (nv : Nat) (lhs t : D p) : Option (Sb p × List (D p)) :=
  let σ0 : Sb p := Array.replicate nv none
  match lhs, t with
  | .ac f ps, .ac g ts => if f == g then mac p c f ps ts σ0 true (fun σ rest => some (σ, rest)) else none
  | _, _ => mt p c lhs t σ0 (fun σ => some (σ, []))

/-- Simultaneous matching of pattern/subject pairs, without extension. -/
def mtPairs (c : MC) (nv : Nat) (pairs : List (D p × D p)) : Bool :=
  (mtList p c (pairs.map (·.1)) (pairs.map (·.2)) (Array.replicate nv none) (fun σ => some σ)).isSome

/-! ### Equations, reduction and reducibility -/

structure Eqn where
  lhs : D p
  rhs : D p
  sorts : Array SortId
  names : Array Nat
  top : Option (Nat × Nat)
  idx : Nat

/-- The equations with their variables in Maude's slots: by first occurrence in
the normalised left side (`PreEquation::check`), then the right side. -/
def mkEqn (idx : Nat) (e : REq) : Eqn p :=
  let n := e.sorts.size
  let r0 := ranks p fun i => e.names.getD i 0
  let so0 := fun i => e.sorts[i]?
  let l0 := norm p r0 so0 (ofR p id e.lhs)
  let r0' := norm p r0 so0 (ofR p id e.rhs)
  let order := dfsVars p (dfsVars p #[] l0) r0'
  let order := order ++ ((Array.range n).filter fun i => !order.contains i)
  let slotOf : Array Nat := order.zipIdx.foldl (fun a (v, j) => a.setIfInBounds v j) (Array.replicate n 0)
  let sorts := order.map fun v => e.sorts.getD v .msg
  let names := order.map fun v => e.names.getD v 0
  let r1 := ranks p fun i => names.getD i 0
  let so1 := fun i => sorts[i]?
  let lhs := norm p r1 so1 (ofR p (slotOf.getD · 0) e.lhs)
  { lhs, rhs := norm p r1 so1 (ofR p (slotOf.getD · 0) e.rhs), sorts, names, top := topKey p lhs, idx }

/-- The ranks inside a variant: variable `k` has name code `k`. -/
def vranks : Ranks (S p) := ranks p id

def children : D p → List (D p)
  | .free _ args => args
  | .comm _ a b => [a, b]
  | .ac _ args => args
  | _ => []

partial def reducible (eqs : Array (Eqn p)) (vs : Nat → SortId) (t : D p) : Bool :=
  (children p t).any (reducible eqs vs) ||
    let key := topKey p t
    key.isSome && eqs.any fun e => e.top == key &&
      (mtop p { psort := (e.sorts.getD · .msg), ssort := vs } e.sorts.size e.lhs t).isSome

def rewriteTop (eqs : Array (Eqn p)) (vs : Nat → SortId) (t : D p) : Option (D p) := Id.run do
  let key := topKey p t
  if key.isNone then return none
  let so := fun i => some (vs i)
  for e in eqs do
    if e.top == key then
      match mtop p { psort := (e.sorts.getD · .msg), ssort := vs } e.sorts.size e.lhs t with
      | some (σ, rest) =>
        let rhs := inst p (fun i => (σ.getD i none).getD (.var 0)) e.rhs
        let res : D p := match rest, t with
          | [], _ => rhs
          | _, .ac f _ => .ac f (rhs :: rest)
          | _, _ => rhs
        return some (norm p (vranks p) so res)
      | none => pure ()
  return none

/-- Normal form by innermost rewriting, with the number of rewrites (the
theory is convergent modulo AC, so the normal form does not depend on the
strategy; the count follows Maude's eager strategy: arguments first, then the
equations of the top symbol in module order). -/
partial def nfc (eqs : Array (Eqn p)) (vs : Nat → SortId) (t : D p) : D p × Nat :=
  let so := fun i => some (vs i)
  let sumc := fun (rs : List (D p × Nat)) => rs.foldl (fun n x => n + x.2) 0
  let (t', c) : D p × Nat := match t with
    | .free f args => let rs := args.map (nfc eqs vs); (.free f (rs.map (·.1)), sumc rs)
    | .comm f a b =>
      let (a', ca) := nfc eqs vs a
      let (b', cb) := nfc eqs vs b
      (Dag.mkComm (vranks p) so f a' b', ca + cb)
    | .ac f args =>
      let rs := args.map (nfc eqs vs)
      (.ac f (Dag.normAC (vranks p) so f (rs.map (·.1))), sumc rs)
    | d => (d, 0)
  match rewriteTop p eqs vs t' with
  | some u => let (u', cu) := nfc eqs vs u; (u', c + 1 + cu)
  | none => (t', c)

/-! ### Variants -/

structure Variant where
  subst : Array (D p)
  term : D p
  sorts : Array SortId
  family : Nat

def Variant.sortFn (v : Variant p) : Nat → SortId := fun i => v.sorts.getD i .msg

/-- `subsumes a b`: the retained variant `a` is at least as general as `b`
(`VariantFolder::subsumes`): one matcher for the term and every binding. -/
def subsumesV (a b : Variant p) : Bool :=
  a.subst.size == b.subst.size &&
    mtPairs p { psort := (Variant.sortFn p a), ssort := (Variant.sortFn p b) } a.sorts.size
      ((a.term, b.term) :: (a.subst.toList.zip b.subst.toList))

/-- Breadth-first positions: path (argument indices, AC ones into the runs)
and subterm (`PositionState::exploreNextPosition`). -/
partial def positions (t : D p) : Array (List Nat × D p) := Id.run do
  let mut q : Array (List Nat × D p) := #[([], t)]
  let mut i := 0
  while i < q.size do
    let (path, n) := q[i]!
    match n with
    | .free _ args => for (a, j) in args.zipIdx do q := q.push (path ++ [j], a)
    | .comm _ a b => q := q.push (path ++ [0], a); q := q.push (path ++ [1], b)
    | .ac _ args => for ((a, _), j) in (runsOf p args).zipIdx do q := q.push (path ++ [j], a)
    | _ => pure ()
    i := i + 1
  return q

/-- Replace the subterm at `path` by `repl`, instantiating the rest with `θ`
(`PositionState::rebuildAndInstantiateDag`). -/
partial def rebuild (θ : Nat → D p) (t : D p) (path : List Nat) (repl : D p) : D p :=
  match path with
  | [] => repl
  | j :: rest =>
    match t with
    | .free f args => .free f (args.zipIdx.map fun (a, i) => if i == j then rebuild θ a rest repl else inst p θ a)
    | .comm f a b => if j == 0 then .comm f (rebuild θ a rest repl) (inst p θ b) else .comm f (inst p θ a) (rebuild θ b rest repl)
    | .ac f args =>
      let rs := runsOf p args
      let (e, _) := rs[j]!
      let others := (removeOne p e args).getD args
      .ac f (rebuild θ e rest repl :: others.map (inst p θ))
    | d => d

structure Unifier where
  eImgs : Array (D p)
  tImgs : Array (D p)
  sorts : Array SortId
  path : List Nat
  rhs : D p

inductive Err where
  | gaveUp (msg : String)

/-- One step of variant narrowing of `v` (`VariantNarrowingSearchState`):
the new variants in Maude's order. -/
def narrow (eqs : Array (Eqn p)) (fuel : Nat) (v : Variant p) (family : Nat) :
    Except String (Array (Variant p) × Nat) := do
  let tvTerm := dfsVars p #[] v.term
  let nInt := tvTerm.size
  let tv := v.subst.foldl (dfsVars p) tvTerm
  let tvIdx : Array Nat := tv.zipIdx.foldl (fun a (k, j) => a.setIfInBounds k j) (Array.replicate v.sorts.size 0)
  let mut filter : Array (Unifier p) := #[]
  for (path, node) in positions p v.term do
    let key := topKey p node
    if key.isNone then continue
    for e in eqs do
      if e.top != key then continue
      let ne := e.sorts.size
      let nOrig := ne + tv.size
      let sorts : List SortId := e.sorts.toList ++ tv.toList.map (Variant.sortFn p v)
      let sortsA := sorts.toArray
      let nameOf := fun j => if j < ne then e.names.getD j 0
        else if j < nOrig then 1000000 + tv.getD (j - ne) 0 else 1000000000 + j
      let r1 := ranks p nameOf
      let so1 := fun j => sortsA[j]?
      let lhs := norm p r1 so1 e.lhs
      let tgt := norm p r1 so1 (inst p (fun k => .var (ne + tvIdx.getD k 0)) node)
      match @MaudeUnify.unify (S p) _ _ _ _ r1 Interrupt.never fuel sorts [(lhs, tgt)] with
      | .gaveUp => throw s!"port gave up at equation {e.idx}"
      | .fail => pure ()
      | .ok answers =>
        for a in answers do
          let outSorts := a.sorts.toArray
          let soN := fun j => outSorts[j]?
          let vsN := fun j => outSorts.getD j .msg
          let imgs := a.images.toArray.map (norm p (vranks p) soN)
          let u : Unifier p := { eImgs := imgs.extract 0 ne, tImgs := imgs.extract ne nOrig,
                                 sorts := outSorts, path, rhs := e.rhs }
          -- reducibility of the bindings of the variables of the term
          if (u.tImgs.extract 0 nInt).any (reducible p eqs vsN) then continue
          -- subsumption on the variables of the term (UnifierFilter)
          let subsumes := fun (a b : Unifier p) =>
            mtPairs p { psort := (a.sorts.getD · .msg), ssort := (b.sorts.getD · .msg) } a.sorts.size
              ((a.tImgs.extract 0 nInt).toList.zip (b.tImgs.extract 0 nInt).toList)
          if filter.any (subsumes · u) then continue
          filter := (filter.filter fun old => !subsumes u old).push u
  let mut out : Array (Variant p) := #[]
  let mut rewrites := 0
  for u in filter do
    let vsN := fun j => u.sorts.getD j .msg
    let soN := fun j => u.sorts[j]?
    let θ := fun k => u.tImgs.getD (tvIdx.getD k 0) (.var 0)
    let newSubst := v.subst.map fun d => norm p (vranks p) soN (inst p θ d)
    if newSubst.any (reducible p eqs vsN) then continue
    let repl := inst p (fun j => u.eImgs.getD j (.var 0)) u.rhs
    let (t, c) := nfc p eqs vsN (rebuild p θ v.term u.path repl)
    rewrites := rewrites + 1 + c
    out := out.push { subst := newSubst, term := t, sorts := u.sorts, family }
  return (out, rewrites)

structure Retained where
  idx : Nat
  parent : Option Nat
  v : Variant p

/-- `VariantFolder::insertVariant`. -/
def insertVariant (folder : Array (Retained p)) (v : Variant p) (idx : Nat) (parent : Option Nat) :
    Option (Array (Retained p)) := Id.run do
  if folder.any fun r => subsumesV p r.v v then return none
  let mut ancestors : Array Nat := #[]
  let mut cur := parent
  let mut guard := folder.size + 1
  while guard > 0 do
    guard := guard - 1
    match cur with
    | none => break
    | some i =>
      ancestors := ancestors.push i
      cur := (folder.find? (·.idx == i)).bind (·.parent)
  let mut evicted : Array Nat := #[]
  let mut kept : Array (Retained p) := #[]
  for r in folder do
    if ancestors.contains r.idx then kept := kept.push r; continue
    let parentGone := match r.parent with | some q => evicted.contains q | none => false
    if parentGone || subsumesV p v r.v then
      evicted := evicted.push r.idx
    else kept := kept.push r
  return some (kept.push { idx, parent, v })

/-! ### Printing -/

partial def showD (vname : Nat → String) : D p → String
  | .var i => vname i
  | .atom a => let (n, k) := p.tnames.getD a ("?", 0); s!"{n}({k})"
  | .free f args =>
    let n := p.fnames.getD f "?"
    if args.isEmpty then n else s!"{n}({", ".intercalate (args.map (showD vname))})"
  | .comm f a b => s!"{p.cnames.getD f "?"}({showD vname a}, {showD vname b})"
  | .ac f args => s!"{p.anames.getD f "?"}({", ".intercalate (args.map (showD vname))})"

def Variant.vname (v : Variant p) (k : Nat) : String :=
  s!"{if v.family == 0 then "#" else "%"}{k + 1}:{sortName (Variant.sortFn p v k)}"

/-- The whole search: the lines of Maude's reply. -/
def search (fuel : Nat) : Except String (Array String) := do
  let eqs := p.eqs.zipIdx.map fun (e, i) => mkEqn p i e
  -- the query: variables by first occurrence in the normalised query
  let qn := p.qvars.size
  let rq := ranks p fun i => (p.qvars.getD i (.msg, 0, "")).2.1
  let soq := fun i => (p.qvars[i]?).map (·.1)
  let q0 := norm p rq soq (ofR p id p.query)
  let order := dfsVars p #[] q0
  let slotOf : Array Nat := order.zipIdx.foldl (fun a (v, j) => a.setIfInBounds v j) (Array.replicate qn 0)
  let sorts := order.map fun i => (p.qvars.getD i (.msg, 0, "")).1
  let qnames := order.map fun i => (p.qvars.getD i (.msg, 0, "")).2.2
  let vs := fun j => sorts.getD j .msg
  let (term, c0) := nfc p eqs vs (norm p (vranks p) (fun j => sorts[j]?) (inst p (fun i => .var (slotOf.getD i 0)) q0))
  let root : Variant p := { subst := (Array.range order.size).map .var, term, sorts, family := 0 }
  let mut folder : Array (Retained p) := #[{ idx := 0, parent := none, v := root }]
  let mut frontier : Array Nat := #[0]
  let mut current := 1
  let mut useFirst := false
  let mut last : Option Nat := none
  let mut lines : Array String := #[]
  let mut count := 0
  let mut rewrites := c0
  let mut guard := 100000
  while guard > 0 do
    guard := guard - 1
    let pick := fun (f : Array (Retained p)) => f.find? fun r => match last with | none => true | some l => r.idx > l
    let mut next := pick folder
    if next.isNone then
      if frontier.isEmpty then break
      -- expand the layer
      let family := if useFirst then 0 else 1
      let mut newFrontier : Array Nat := #[]
      for i in frontier do
        match folder.find? (·.idx == i) with
        | none => pure ()
        | some r =>
          let (kids, c) ← narrow p eqs fuel r.v family
          rewrites := rewrites + c
          for kv in kids do
            let idx := current
            current := current + 1
            match insertVariant p folder kv idx (some i) with
            | some f => folder := f; newFrontier := newFrontier.push idx
            | none => pure ()
      frontier := newFrontier
      useFirst := !useFirst
      next := pick folder
      if next.isNone then break
    match next with
    | none => break
    | some r =>
      last := some r.idx
      count := count + 1
      let v := r.v
      lines := lines.push ""
      lines := lines.push s!"Variant {count}"
      lines := lines.push s!"rewrites: {rewrites}"
      lines := lines.push s!"{(msort p (Variant.sortFn p v) v.term).name}: {showD p (Variant.vname p v) v.term}"
      for (d, j) in v.subst.zipIdx do
        lines := lines.push s!"{qnames.getD j "?"}:{sortName (sorts.getD j .msg)} --> {showD p (Variant.vname p v) d}"
  lines := lines.push ""
  lines := lines.push (if count == 0 then "No variants." else "No more variants.")
  lines := lines.push s!"rewrites: {rewrites}"
  return lines

end

/-! ### Problem files -/

def toks (s : String) : Array String :=
  ((s.replace "(" " ( ").replace ")" " ) ").splitOn " " |>.filter (· ≠ "") |>.toArray

partial def parseR (ts : Array String) (i : Nat) : R × Nat :=
  let t := ts[i]!
  if t == "(" then
    let hd := ts[i+1]!
    let rec args (j : Nat) (acc : Array R) : Array R × Nat :=
      if ts[j]! == ")" then (acc, j + 1) else
      let (x, j') := parseR ts j
      args j' (acc.push x)
    let (xs, j) := args (i + 2) #[]
    let k := (hd.drop 1).toNat!
    match hd.front with
    | 'f' => (.f k xs, j)
    | 'c' => (.c k xs[0]! xs[1]!, j)
    | 'A' => (.ac k xs, j)
    | _ => panic! s!"bad head {hd}"
  else
    let k := (t.drop 1).toNat!
    match t.front with
    | 'v' => (.v k, i + 1)
    | 'a' => (.a k, i + 1)
    | 'f' => (.f k #[], i + 1)
    | _ => panic! s!"bad token {t}"

def nums (ws : List String) : Array Nat := (ws.map String.toNat!).toArray

def parseTerm (s : String) : R := (parseR (toks s) 0).1

def decls (rest : List String) : List (List Nat) :=
  (((" ".intercalate rest).splitOn "|").filter (fun (d : String) => d.toList.any (· != ' '))).map fun d =>
    ((d.splitOn " ").filter (· ≠ "")).map String.toNat!

def solveOne (p : Prob) (fuel : Nat) : IO Unit := do
  IO.println s!"BEGIN {p.id}"
  let t0 ← IO.monoNanosNow
  match search p fuel with
  | .ok lines => for l in lines do IO.println l
  | .error e => IO.println s!"ERROR {e}"
  let t1 ← IO.monoNanosNow
  IO.println s!"END {p.id} {(t1 - t0) / 1000}"

partial def loop (h : IO.FS.Stream) (p : Prob) (fuel : Nat) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then return
  let line : String := String.ofList (line.toList.filter (· != '\n'))
  let ws := (line.splitOn " ").filter (· ≠ "")
  match ws with
  | "PROBLEM" :: id :: _ => loop h { id := id } fuel
  | "FREE" :: rest =>
    let ds := (decls rest).map fun xs => ({ inputs := (xs.drop 1).toArray.map sortOfCode, output := sortOfCode xs.head! } : FD)
    loop h { p with free := ds.toArray } fuel
  | "FREEMS" :: rest =>
    let ds := (decls rest).map fun xs => ((xs.drop 1).toArray.map MS.ofCode, MS.ofCode xs.head!)
    loop h { p with freeMS := ds.toArray } fuel
  | "COMM" :: rest => loop h { p with comm := (nums rest).map sortOfCode } fuel
  | "AC" :: rest => loop h { p with ac := (nums rest).map sortOfCode } fuel
  | "ATOMS" :: rest => loop h { p with atoms := (nums rest).map sortOfCode } fuel
  | "RF" :: rest => loop h { p with rf := nums rest } fuel
  | "RC" :: rest => loop h { p with rc := nums rest } fuel
  | "RA" :: rest => loop h { p with ra := nums rest } fuel
  | "RT" :: rest => loop h { p with rt := nums rest } fuel
  | "RG" :: rest => loop h { p with rg := nums rest } fuel
  | "RV" :: rest => loop h { p with rv := nums rest } fuel
  | "RS" :: rest => loop h { p with rs := nums rest } fuel
  | "FNAMES" :: rest => loop h { p with fnames := rest.toArray } fuel
  | "CNAMES" :: rest => loop h { p with cnames := rest.toArray } fuel
  | "ANAMES" :: rest => loop h { p with anames := rest.toArray } fuel
  | "TNAMES" :: rest =>
    let xs := rest.toArray
    loop h { p with tnames := (Array.range (xs.size / 2)).map fun i => (xs[2*i]!, xs[2*i+1]!.toNat!) } fuel
  | "EQ" :: _ =>
    -- EQ sorts... | names... | lhs = rhs
    match (String.ofList (line.toList.drop 3)).splitOn " | " with
    | [ss, ns, body] =>
      match body.splitOn " = " with
      | [l, rr] =>
        let e : REq := { sorts := (nums ((ss.splitOn " ").filter (· ≠ ""))).map sortOfCode,
                         names := nums ((ns.splitOn " ").filter (· ≠ "")),
                         lhs := parseTerm l, rhs := parseTerm rr }
        loop h { p with eqs := p.eqs.push e } fuel
      | _ => panic! "bad EQ body"
    | _ => panic! "bad EQ"
  | "QVARS" :: rest =>
    let xs := rest.toArray
    let vs := (Array.range (xs.size / 3)).map fun i =>
      (sortOfCode xs[3*i]!.toNat!, xs[3*i+1]!.toNat!, xs[3*i+2]!)
    loop h { p with qvars := vs } fuel
  | "QUERY" :: _ => loop h { p with query := parseTerm (String.ofList (line.toList.drop 6)) } fuel
  | "END" :: _ =>
    solveOne p fuel
    (← IO.getStdout).flush
    loop h {} fuel
  | _ => loop h p fuel

def main (args : List String) : IO Unit := do
  let fuel := (args.getD 0 "1000000").toNat!
  loop (← IO.getStdin) {} fuel

end Tamarin.MaudeVariantsPrototype
