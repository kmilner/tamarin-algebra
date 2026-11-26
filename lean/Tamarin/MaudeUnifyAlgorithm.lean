import Tamarin.MaudeUnifyFactor

/-!
# Maude's unification algorithm

A port of the unification of Maude 3.5.1 for signatures with free, C and AC
symbols without identities: `UnificationProblem`, `PendingUnificationStack`,
the `computeSolvedForm` of variables, free, C and AC dag nodes,
`CUI_UnificationSubproblem`, `ACU_UnificationSubproblem2` (with the basis of
`intContejeanDevie.cc` and the selections of `nextSelection`), the cycle check
and the instantiation of solved forms, and the naming of free variables.

The state is Maude's `UnificationContext`: one slot per variable, bound or
not, the original variables first and the fresh ones after them, together
with the pending theory problems. Every recursion is bounded by fuel; running
out of fuel is the outcome `gaveUp`, distinct from failure.
-/
namespace Tamarin.MaudeUnify

/-- The theory of a pending problem: an AC symbol or a C symbol. -/
inductive Theory (s : Signature) where
  | ac (f : s.ACSym)
  | comm (f : s.CSym)

/-- A pending theory problem. -/
structure Pend (s : Signature) where
  th : Theory s
  lhs : Dag s
  rhs : Dag s

/-- The unification context: bindings and sorts of the slots (`none` is the
error sort of a fresh variable) and the pending problems, latest first. -/
structure St (s : Signature) where
  vals : Array (Option (Dag s))
  sorts : Array (Option SortId)
  pending : List (Pend s)

/-- Outcomes of a computation that can fail or run out of fuel. -/
inductive Res (α : Type) where
  | ok (a : α)
  | fail
  | gaveUp

namespace Res
variable {α β : Type}

def bind : Res α → (α → Res β) → Res β
  | .ok a, f => f a
  | .fail, _ => .fail
  | .gaveUp, _ => .gaveUp

def map (f : α → β) : Res α → Res β
  | .ok a => .ok (f a)
  | .fail => .fail
  | .gaveUp => .gaveUp

/-- Concatenate the lists of a list of computations; a failed one contributes
nothing, one that gave up makes the whole give up. -/
def concatMap (f : α → Res (List β)) : List α → Res (List β)
  | [] => .ok []
  | a :: as =>
    match f a with
    | .gaveUp => .gaveUp
    | .fail => concatMap f as
    | .ok bs => (concatMap f as).map (bs ++ ·)

end Res

variable {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

namespace Theory
def beq : Theory s → Theory s → Bool
  | .ac f, .ac g => decide (f = g)
  | .comm f, .comm g => decide (f = g)
  | _, _ => false

/-- `unificationPriority`: C before AC. -/
def priority : Theory s → Nat
  | .comm _ => 1
  | .ac _ => 10
end Theory

namespace St

def value (st : St s) (i : Nat) : Option (Dag s) := st.vals.getD i none

def sortOf (st : St s) (i : Nat) : Option SortId := st.sorts.getD i none

def bind (st : St s) (i : Nat) (v : Option (Dag s)) : St s := { st with vals := st.vals.setIfInBounds i v }

/-- `makeFreshVariable`: a new slot of the error sort. -/
def fresh (st : St s) : St s × Nat :=
  ({ st with vals := st.vals.push none, sorts := st.sorts.push none }, st.vals.size)

def push (st : St s) (th : Theory s) (l r : Dag s) : St s := { st with pending := ⟨th, l, r⟩ :: st.pending }

/-- Follow variable-to-variable bindings, at most `k` of them. -/
def follow (st : St s) : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x =>
    match st.value x with
    | some (.var y) => st.follow k y
    | _ => x

/-- `lastVariableInChain`. -/
def lastVar (st : St s) (x : Nat) : Nat := st.follow st.vals.size x

end St

variable (r : Ranks s)

/-- Maude's term order in a context. -/
def order (st : St s) (x y : Dag s) : Ordering := Dag.cmp r st.sortOf x y

/-- The term order with equality decided syntactically: two different dags
never compare equal, whatever the ranks. With Maude's ranks this is Maude's
order. -/
def orderEq (st : St s) (x y : Dag s) : Ordering :=
  if x = y then .eq else
  match order r st x y with
  | .eq => .lt
  | o => o

/-- A C node with sorted arguments in a context. -/
def mkComm' (st : St s) (f : s.CSym) (a b : Dag s) : Dag s := Dag.mkComm r st.sortOf f a b

/-- Whether some slot of a binding is a variable whose chain ends at `new`
(`safeVirtualReplacement`'s occurs test). -/
def chainsTo (st : St s) (nb : Dag s) (new : Nat) : Bool :=
  nb.vars.any fun i => match st.value i with
    | some (.var _) => st.lastVar i == new
    | _ => false

mutual
/-- `DagNode::computeSolvedForm`. -/
def csf : Nat → St s → Dag s → Dag s → Res (St s)
  | 0, _, _, _ => .gaveUp
  | k + 1, st, l, rt =>
    if !l.ground then csf2 k st l rt
    else if !rt.ground then csf2 k st rt l
    else if Dag.same l rt then .ok st else .fail

/-- `computeSolvedForm2`, dispatched on the theory of the left side. -/
def csf2 : Nat → St s → Dag s → Dag s → Res (St s)
  | 0, _, _, _ => .gaveUp
  | k + 1, st, l, rt =>
    match l with
    | .var x => varCsf k st x rt
    | .atom a => constCsf k st (.atom a) rt
    | .free f args => freeCsf k st f args rt
    | .ac f args => acCsf k st f args rt
    | .comm f a b => commCsf k st f a b rt

/-- `VariableDagNode::computeSolvedForm2`. -/
def varCsf : Nat → St s → Nat → Dag s → Res (St s)
  | 0, _, _, _ => .gaveUp
  | k + 1, st, x, rt =>
    match rt with
    | .var y =>
      let lv0 := st.lastVar x
      let rv0 := st.lastVar y
      if lv0 = rv0 then .ok st else
      let (lv, rv) := if r.sortIndex (st.sortOf lv0) > r.sortIndex (st.sortOf rv0) then (rv0, lv0) else (lv0, rv0)
      match st.value lv with
      | none => safeRepl k st lv rv
      | some lt =>
        match st.value rv with
        | none => safeRepl k st rv lv
        | some rt' => (safeRepl k st lv rv).bind fun st => csf k st lt rt'
    | _ => csf2 k st rt (.var x)

/-- `VariableDagNode::safeVirtualReplacement`. -/
def safeRepl : Nat → St s → Nat → Nat → Res (St s)
  | 0, _, _, _ => .gaveUp
  | k + 1, st, old, new =>
    let st := st.bind old (some (.var new))
    match st.value new with
    | none => .ok st
    | some nb =>
      if nb.ground then .ok st
      else if chainsTo st nb new then csf2 k (st.bind new none) nb (.var new)
      else .ok st

/-- A free constant (an atom) against another dag. -/
def constCsf : Nat → St s → Dag s → Dag s → Res (St s)
  | 0, _, _, _ => .gaveUp
  | k + 1, st, c, rt =>
    match rt with
    | .var y =>
      let rv := st.lastVar y
      match st.value rv with
      | some val => csf k st c val
      | none => .ok (st.bind rv (some c))
    | _ => .fail

/-- `FreeDagNode::computeSolvedForm2`. -/
def freeCsf : Nat → St s → s.FreeSym → List (Dag s) → Dag s → Res (St s)
  | 0, _, _, _, _ => .gaveUp
  | k + 1, st, f, args, rt =>
    match rt with
    | .free g bs => if f = g then csfList k st args bs else .fail
    | .var y =>
      let rv := st.lastVar y
      match st.value rv with
      | some val => csf k st (.free f args) val
      | none =>
        if (Dag.free f args).ground then .ok (st.bind rv (some (.free f args)))
        else (purifyArgs k st args rv).bind fun (st, ps) => .ok (st.bind rv (some (.free f ps)))
    | _ => .fail

/-- Unify argument lists pairwise. -/
def csfList : Nat → St s → List (Dag s) → List (Dag s) → Res (St s)
  | 0, _, _, _ => .gaveUp
  | _ + 1, st, [], [] => .ok st
  | k + 1, st, a :: as, b :: bs => (csf k st a b).bind fun st => csfList k st as bs
  | _ + 1, _, _, _ => .fail

/-- `FreeDagNode::purifyAndOccurCheck` on the arguments of a free node that
is about to be bound to slot `rep`. Alien arguments are abstracted by fresh
variables; a direct occurrence of `rep` fails. -/
def purifyArgs : Nat → St s → List (Dag s) → Nat → Res (St s × List (Dag s))
  | 0, _, _, _ => .gaveUp
  | _ + 1, st, [], _ => .ok (st, [])
  | k + 1, st, a :: as, rep =>
    let headRes : Res (St s × Dag s) :=
      match a with
      | .var y => if st.lastVar y = rep then .fail else .ok (st, a)
      | .atom _ => .ok (st, a)
      | .free g bs =>
        if (Dag.free g bs).ground then .ok (st, a)
        else (purifyArgs k st bs rep).map fun (st, ps) => (st, .free g ps)
      | _ =>
        let (st, av) := st.fresh
        (csf k st a (.var av)).map fun st => (st, .var av)
    headRes.bind fun (st, a') => (purifyArgs k st as rep).map fun (st, ps) => (st, a' :: ps)

/-- `ACU_DagNode::computeSolvedForm2`. -/
def acCsf : Nat → St s → s.ACSym → List (Dag s) → Dag s → Res (St s)
  | 0, _, _, _, _ => .gaveUp
  | k + 1, st, f, args, rt =>
    match rt with
    | .ac g _ => if f = g then .ok (st.push (.ac f) (.ac f args) rt) else .fail
    | .var y =>
      let rv := st.lastVar y
      match st.value rv with
      | some val => csf2 k st (.ac f args) val
      | none => .ok (st.push (.ac f) (.ac f args) rt)
    | _ => .fail

/-- `CUI_DagNode::makePurifiedVersion`. -/
def purifyC : Nat → St s → s.CSym → Dag s → Dag s → Res (St s × Dag s)
  | 0, _, _, _, _ => .gaveUp
  | k + 1, st, f, a, b =>
    let left : Res (St s × Dag s) :=
      match a with
      | .var _ => .ok (st, a)
      | _ => let (st, av) := st.fresh; (csf k st a (.var av)).map fun st => (st, .var av)
    left.bind fun (st, a') =>
      let right : Res (St s × Dag s) :=
        if b = a then .ok (st, a') else
        match b with
        | .var _ => .ok (st, b)
        | _ => let (st, bv) := st.fresh; (csf k st b (.var bv)).map fun st => (st, .var bv)
      right.map fun (st, b') => (st, mkComm' r st f a' b')

/-- `CUI_DagNode::computeSolvedForm2` for a commutative symbol. -/
def commCsf : Nat → St s → s.CSym → Dag s → Dag s → Dag s → Res (St s)
  | 0, _, _, _, _, _ => .gaveUp
  | k + 1, st, f, l0, l1, rt =>
    match rt with
    | .comm g r0 r1 =>
      if f ≠ g then .fail else
      let (l0, l1, r0, r1) := if orderEq r st l0 r0 = .gt then (r0, r1, l0, l1) else (l0, l1, r0, r1)
      let both := fun (st : St s) => (csf k st l0 r0).bind fun st => csf k st l1 r1
      let pushed := Res.ok (st.push (.comm f) (.comm f l0 l1) (.comm f r0 r1))
      if l0 = r0 then csf k st l1 r1 else
      match orderEq r st l1 r0 with
      | .eq => csf k st l0 r1
      | .lt => if l0 = l1 ∨ r0 = r1 then both st else pushed
      | .gt =>
        match orderEq r st l1 r1 with
        | .eq => csf k st l0 r0
        | .lt => pushed
        | .gt => if r0 = r1 then both st else pushed
    | .var y =>
      let rv := st.lastVar y
      match st.value rv with
      | some val => commCsf k st f l0 l1 val
      | none => (purifyC k st f l0 l1).bind fun (st, p) => .ok (st.bind rv (some p))
    | _ => .fail
end

/-! ### The AC subproblem -/

def topOf : Dag s → Option (Top s)
  | .var _ => none
  | .atom a => some (.atom a)
  | .free f _ => some (.free f)
  | .comm f _ _ => some (.comm f)
  | .ac f _ => some (.ac f)

/-- `setMultiplicity`: add `m` occurrences of a dag (a variable replaced by
its representative) to a row over the subterms, appending a new subterm. -/
def addOcc (st : St s) (subs : List (Dag s)) (row : List Int) (d : Dag s) (m : Int) :
    List (Dag s) × List Int :=
  let d := match d with
    | .var x => Dag.var (st.lastVar x)
    | d => d
  match subs.findIdx? (· = d) with
  | some i => (subs, row.modify i (· + m))
  | none => (subs ++ [d], row ++ [m])

/-- Drop the subterms after the first `n` whose multiplicity is zero
(`killCancelledSubterms`). -/
def killNew : Nat → List (Dag s) → List Int → List (Dag s) × List Int
  | 0, xs, cs =>
    let kept := (xs.zip cs).filter fun p => p.2 ≠ 0
    (kept.map (·.1), kept.map (·.2))
  | n + 1, x :: xs, c :: cs =>
    let rest := killNew n xs cs
    (x :: rest.1, c :: rest.2)
  | _ + 1, xs, cs => (xs, cs)

/-- Add the occurrences of the arguments of a dag at the symbol, with a
multiplicity; a dag of another head counts as one argument. -/
def addArgs (st : St s) (f : s.ACSym) (m : Int) (acc : List (Dag s) × List Int) (d : Dag s) :
    List (Dag s) × List Int :=
  match d with
  | .ac g args => if g = f then args.foldl (fun acc a => addOcc st acc.1 acc.2 a m) acc
                  else addOcc st acc.1 acc.2 d m
  | _ => addOcc st acc.1 acc.2 d m

/-- `addUnification`: the row of one problem `l =? rt` of the symbol, the
right side first; new subterms that cancel are dropped again. -/
def addUnif (st : St s) (f : s.ACSym) (subs : List (Dag s)) (rows : List (List Int)) (l rt : Dag s) :
    List (Dag s) × List (List Int) :=
  let afterR := addArgs st f (-1) (subs, List.replicate subs.length 0) rt
  let afterL := addArgs st f 1 afterR l
  let k := killNew subs.length afterL.1 afterL.2
  if k.2.any (· ≠ 0) then (k.1, rows ++ [k.2]) else (k.1, rows)

/-- `unsolve`: the bindings of slots to products of the symbol become rows. -/
def unsolve (f : s.ACSym) : Nat → St s → List (Dag s) → List (List Int) → St s × List (Dag s) × List (List Int)
  | 0, st, subs, rows => (st, subs, rows)
  | k + 1, st, subs, rows =>
    let i := st.vals.size - (k + 1)
    match st.value i with
    | some (.ac g args) =>
      if g = f then
        let st := st.bind i none
        let start := (subs, List.replicate subs.length (0 : Int))
        let acc := args.foldl (fun (acc : List (Dag s) × List Int) a => addOcc st acc.1 acc.2 a 1) start
        let acc := addOcc st acc.1 acc.2 (.var i) (-1)
        unsolve f k st acc.1 (rows ++ [acc.2])
      else unsolve f k st subs rows
    | _ => unsolve f k st subs rows

/-- The bound and stable symbol of an alien: one thing, with its top symbol. -/
def single (f : s.ACSym) (d : Dag s) : Option Nat × Option (Top s) :=
  match topOf d with
  | some (.ac g) => if g = f then (none, none) else (some 1, some (.ac g))
  | some top => (some 1, some top)
  | none => (none, none)

/-- `sortBound`: a sort that cannot hold a product takes one thing. -/
def sortBound (f : s.ACSym) : Option SortId → Option Nat
  | none => none
  | some srt => if Subsort.check (s.acSort f) srt then none else some 1

/-- `classify`: the bound and the stable symbol of a subterm. -/
def classify (st : St s) (f : s.ACSym) (t : Dag s) : Option Nat × Option (Top s) :=
  match t with
  | .var x =>
    match st.value x with
    | some d => if (topOf d).isSome then single f d else (sortBound f (st.sortOf x), none)
    | none => (sortBound f (st.sortOf x), none)
  | t => single f t

/-- The fresh variable of each selected element, reusing a variable subterm
that only that element assigns, with multiplicity one (`reuseVariable`).
`j` is the position of the first element of `todo` in the selection. Returns
the witnesses and the positions of the reused subterms. -/
def witnesses (subs : List (Dag s)) (sel : List (List Nat)) :
    List (List Nat) → Nat → St s → St s × List (Dag s) × List Nat
  | [], _, st => (st, [], [])
  | e :: rest, j, st =>
    let reuse := (subs.zipIdx).find? fun (t, i) =>
      e.getD i 0 = 1 && (match t with | .var _ => true | _ => false) &&
        (sel.zipIdx).all fun (e', j') => j' = j || e'.getD i 0 = 0
    let (st, w, used) : St s × Dag s × List Nat := match reuse with
      | some (t, i) => (st, t, [i])
      | none => let (st, v) := st.fresh; (st, .var v, [])
    let (st, ws, us) := witnesses subs sel rest (j + 1) st
    (st, w :: ws, used ++ us)

/-- What the selected elements assign to subterm `i`, and whether it is a
product of the symbol. -/
def assign (st : St s) (f : s.ACSym) (sel : List (List Nat)) (ws : List (Dag s)) (i : Nat) : Dag s × Bool :=
  let picks := (sel.zip ws).filter fun (e, _) => 0 < e.getD i 0
  match picks with
  | [(e, w)] => if e.getD i 0 = 1 then (w, false)
                else (.ac f (Dag.normAC r st.sortOf f (List.replicate (e.getD i 0) w)), true)
  | _ => (.ac f (Dag.normAC r st.sortOf f (picks.flatMap fun (e, w) => List.replicate (e.getD i 0) w)), true)

/-- `buildSolution` after the witnesses are allocated: each subterm that is
not a reused witness is unified with what the selection assigns to it; an
unbound variable that receives a product is bound to it directly. -/
def buildFrom (k : Nat) (f : s.ACSym) (sel : List (List Nat)) (ws : List (Dag s)) (reused : List Nat) :
    St s → List (Dag s × Nat) → Res (St s)
  | st, [] => .ok st
  | st, (t, i) :: rest =>
    if i ∈ reused then buildFrom k f sel ws reused st rest else
    let (d, inTheory) := assign r st f sel ws i
    let next : Res (St s) := match t with
      | .var x =>
        let rv := st.lastVar x
        if (st.value rv).isNone && inTheory then .ok (st.bind rv (some d)) else csf r k st t d
      | _ => csf r k st t d
    next.bind fun st => buildFrom k f sel ws reused st rest

/-- Steps granted to the Diophantine search of one AC subproblem. -/
def basisFuel : Nat := 10000000

/-- `ACU_UnificationSubproblem2::solve`: the states of all its solutions, in order. -/
def acStates (k : Nat) (st : St s) (f : s.ACSym) (unifs : List (Dag s × Dag s)) : Res (List (St s)) :=
  let (subs, rows) := unifs.foldl (fun (acc : List (Dag s) × List (List Int)) (l, rt) =>
    addUnif st f acc.1 acc.2 l rt) ([], [])
  if rows.isEmpty then .ok [st] else
  let (st, subs, rows) := unsolve f st.vals.size st subs rows
  let n := subs.length
  let cls := subs.map (classify st f)
  let upper : Vector (Option Nat) n := Vector.ofFn fun i => (cls.getD i (none, none)).1
  let stable := cls.map (·.2)
  match Dioph.basis (colsOf n rows) upper basisFuel with
  | none => .gaveUp
  | some sols =>
    let basis := basisList stable sols
    Res.concatMap (fun (S : List (Select.Elem n)) =>
      let sel := S.map (·.vec.toList)
      let (st, ws, reused) := witnesses subs sel sel 0 st
      (buildFrom r k f sel ws reused st subs.zipIdx).map fun st => [st])
      (Select.all upper basis)

/-- `CUI_UnificationSubproblem::solve`: each problem forwards, then reversed. -/
def commStates (k : Nat) : St s → List (Dag s × Dag s) → Res (List (St s))
  | st, [] => .ok [st]
  | st, (l, rt) :: rest =>
    match l, rt with
    | .comm f l0 l1, .comm g r0 r1 =>
      if f = g then
        let fwd := (csf r k st l0 r0).bind fun st => csf r k st l1 r1
        let rev := (csf r k st l0 r1).bind fun st => csf r k st l1 r0
        Res.concatMap (fun (o : Res (St s)) => o.bind fun st => commStates k st rest) [fwd, rev]
      else .gaveUp
    | _, _ => .gaveUp

/-- The theory to solve next: lowest priority, then earliest pushed. -/
def chooseStep (best : Option (Theory s)) (p : Pend s) : Option (Theory s) :=
  match best with
  | none => some p.th
  | some b => if p.th.priority < b.priority then some p.th else some b

def chooseTheory (st : St s) : Option (Theory s) :=
  st.pending.reverse.foldl chooseStep none

/-- `PendingUnificationStack::solve`: all solved forms, in Maude's order. -/
def run : Nat → St s → Res (List (St s))
  | 0, _ => .gaveUp
  | k + 1, st =>
    match chooseTheory st with
    | none => .ok [st]
    | some th =>
      let unifs := (st.pending.filter fun p => p.th.beq th).map fun p => (p.lhs, p.rhs)
      let st' := { st with pending := st.pending.filter fun p => !p.th.beq th }
      let states := match th with
        | .ac f => acStates r k st' f unifs
        | .comm _ => commStates r k st' unifs
      states.bind (Res.concatMap (run k))

/-! ### Solved forms -/

/-- The outcome of the depth-first search for cycles. -/
inductive Walk where
  | cycle (c : List Nat)
  | done (status : Array Nat) (order : List Nat)
  | gaveUp

/-- `findCycleFrom`: depth-first search through the bindings, recording each
slot after the slots its binding mentions (`variableOrder`). `path` holds the
slots being explored, latest first. Status 1 is being explored, 2 explored. -/
def explore (st : St s) : Nat → Array Nat → List Nat → List Nat → Nat → Walk
  | 0, _, _, _, _ => .gaveUp
  | k + 1, status, order, path, i =>
    match status.getD i 0 with
    | 2 => .done status order
    | 1 => .cycle (i :: (path.takeWhile (· ≠ i)).reverse)
    | _ =>
      match st.value i with
      | none => .done (status.setIfInBounds i 2) order
      | some d =>
        let go := fun (acc : Walk) (j : Nat) => match acc with
          | .done status order => explore st k status order (i :: path) j
          | other => other
        match d.vars.foldl go (.done (status.setIfInBounds i 1) order) with
        | .done status order => .done (status.setIfInBounds i 2) (order ++ [i])
        | other => other

/-- `findCycle` from the given slots in turn. -/
def exploreAll (st : St s) (k : Nat) (roots : List Nat) : Walk :=
  roots.foldl (fun acc i => match acc with
    | .done status order => explore st k status order [] i
    | other => other) (.done (Array.replicate st.vals.size 0) [])

/-- A cycle of bindings: each slot is bound, its binding mentions the next,
the last's mentions the first, and some binding is not a variable. -/
def isCycle (st : St s) (c : List Nat) : Bool :=
  match c with
  | [] => false
  | first :: _ =>
    let links := c.zip (c.drop 1 ++ [first])
    (links.all fun (a, b) => match st.value a with
      | some d => b ∈ d.vars
      | none => false) &&
    c.any fun a => match st.value a with
      | some (.var _) => false
      | some _ => true
      | none => false

/-- Every bound slot occurs in the order, after every bound slot its binding mentions. -/
def isOrder (st : St s) (order : List Nat) : Bool :=
  let step := fun (acc : Option (Array Bool)) (i : Nat) => match acc with
    | none => none
    | some seen =>
      match st.value i with
      | none => none
      | some d =>
        if d.vars.all (fun j => (st.value j).isNone || seen.getD j false) then
          some (seen.setIfInBounds i true)
        else none
  match order.foldl step (some (Array.replicate st.vals.size false)) with
  | none => false
  | some seen => (List.range st.vals.size).all fun i => (st.value i).isNone || seen.getD i false

/-- Instantiate the bindings in the order (`DagNode::instantiate`). -/
def instantiate (st : St s) (order : List Nat) : St s :=
  order.foldl (fun st i => match st.value i with
    | some d => st.bind i (some (Dag.inst r st.sortOf st.value d))
    | none => st) st

/-- The meet of two sort bounds; `none` when they have no common subsort. -/
def meet (a b : SortId) : Option SortId :=
  if Subsort.check a b then some a else if Subsort.check b a then some b else none

/-- The upper bounds that a dag in a position of sort `srt` puts on the sorts
of the free slots it mentions. `none`: no sorting. -/
def bounds (ub : Array (Option SortId)) : Dag s → SortId → Option (Array (Option SortId))
  | .var x, srt =>
    match ub.getD x none with
    | none => some (ub.setIfInBounds x (some srt))
    | some c => (meet c srt).map fun m => ub.setIfInBounds x (some m)
  | .atom a, srt => if Subsort.check (s.atomSort a) srt then some ub else none
  | .free f args, srt =>
    if Subsort.check (s.outputSort f) srt then
      (args.attach.zipIdx).foldl (fun acc p => acc.bind fun ub =>
        bounds ub p.1.1 (if h : p.2 < s.arity f then s.inputSort f ⟨p.2, h⟩ else .msg)) (some ub)
    else none
  | .comm f a b, srt =>
    if Subsort.check (s.cSort f) srt then
      (bounds ub a (s.cSort f)).bind fun ub => bounds ub b (s.cSort f)
    else none
  | .ac f args, srt =>
    if Subsort.check (s.acSort f) srt then
      args.attach.foldl (fun acc a => acc.bind fun ub => bounds ub a.1 (s.acSort f)) (some ub)
    else none
termination_by d => sizeOf d
decreasing_by
  all_goals first
    | (have := List.sizeOf_lt_of_mem p.1.2; simp_all; omega)
    | (have := List.sizeOf_lt_of_mem a.2; simp_all; omega)
    | (simp_all; omega)

/-- An answer: the image of each original slot over the output variables,
which are the free slots numbered in slot order, and the sort of each output
variable. -/
structure Answer (s : Signature) where
  images : List (Dag s)
  sorts : List SortId

/-- Rename the free slots to output numbers. -/
def renameOut (names : Array Nat) : Dag s → Dag s
  | .var i => .var (names.getD i 0)
  | .atom a => .atom a
  | .free f args => .free f (args.attach.map fun ⟨d, _⟩ => renameOut names d)
  | .comm f a b => .comm f (renameOut names a) (renameOut names b)
  | .ac f args => .ac f (args.attach.map fun ⟨d, _⟩ => renameOut names d)

/-- The solved form of a final state: the cycle check, the instantiation, the
assignment of maximal sorts to the free slots, and the names of the free
slots. `ok none` when the state has no sorted unifier. -/
def finish (k : Nat) (nOrig : Nat) (st : St s) : Res (Option (Answer s)) :=
  match exploreAll st k (List.range nOrig ++ (List.range st.vals.size).drop nOrig) with
  | .gaveUp => .gaveUp
  | .cycle c => if isCycle st c then .ok none else .gaveUp
  | .done _ order =>
    if !isOrder st order then .gaveUp else
    let st := instantiate r st order
    -- sort bounds: free original slots by their sorts, bound ones through their values
    let ub0 : Array (Option SortId) := (Array.range st.vals.size).map fun i =>
      if i < nOrig ∧ (st.value i).isNone then st.sortOf i else none
    let ub := (List.range nOrig).foldl (fun acc i => acc.bind fun ub =>
      match st.value i, st.sortOf i with
      | some d, some srt => bounds ub d srt
      | _, _ => some ub) (some ub0)
    match ub with
    | none => .ok none
    | some ub =>
      let free := (List.range st.vals.size).filter fun i => (st.value i).isNone
      let names : Array Nat := free.zipIdx.foldl (fun (a : Array Nat) (i, n) => a.setIfInBounds i n)
        (Array.replicate st.vals.size 0)
      let image := fun i => match st.value i with
        | some d => renameOut names d
        | none => .var (names.getD i 0)
      .ok (some ⟨(List.range nOrig).map image, free.map fun i => (ub.getD i none).getD .msg⟩)

/-- The initial state: one unbound slot per original variable, with its sort. -/
def start (sorts : List SortId) : St s := ⟨Array.replicate sorts.length none, (sorts.map some).toArray, []⟩

/-- The equations, solved one after another. -/
def solveAll (k : Nat) (st : St s) (eqs : List (Dag s × Dag s)) : Res (St s) :=
  eqs.foldl (fun (acc : Res (St s)) (p : Dag s × Dag s) => acc.bind fun st => csf r k st p.1 p.2) (.ok st)

/-- All unifiers of dag equations over original slots with the given sorts,
in Maude's order. -/
def unify (k : Nat) (sorts : List SortId) (eqs : List (Dag s × Dag s)) : Res (List (Answer s)) :=
  match solveAll r k (start sorts) eqs with
  | .gaveUp => .gaveUp
  | .fail => .ok []
  | .ok st =>
    (run r k st).bind (Res.concatMap fun st =>
      (finish r k sorts.length st).map fun a => a.toList)

end Tamarin.MaudeUnify
