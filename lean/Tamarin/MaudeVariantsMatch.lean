import Tamarin.MaudeVariantsTerms
import Tamarin.Interrupt

/-!
# Matching modulo AC and C with sorts, for Maude's `get variants`

Maude's variant search matches in three places: the unifier filter and the
variant folder ask whether one substitution is an instance of another
(`UnifierFilter`, `VariantFolder::subsumes`), and reducibility asks whether a
subterm is an instance of an equation's left side, with extension at an AC top
(`DagNode::reducibleByVariantEquation`). Here is one backtracking matcher for
all three.

A pattern variable of sort `S` matches a subject whose least sort is below `S`
(`msort`); the kind is below no sort. Pattern and subject have separate slots:
the pattern's are bound by the matcher, the subject's are rigid. Both sides
are in Maude's normal form, so equality modulo AC and C is syntactic equality.

The matcher is written with continuations: `k` receives each match and decides
whether to stop. Every function takes `fuel`, a bound on the depth of its
recursion that callers choose far above the size of any problem; at 0 the
branch finds nothing. The loops over the arguments of an AC subject ask the
caller whether to go on (`Interrupt.guard`).
-/
namespace Tamarin.MaudeVariants
open Tamarin MaudeUnify

variable {y : Syms}

/-- A partial assignment of the pattern's slots. -/
abbrev Sb (y : Syms) := Array (Option (D y))

/-- The sorts of the pattern's slots and of the subject's. -/
structure MC where
  psort : Nat → SortId
  ssort : Nat → SortId

/-- The depth bound callers give the matcher: no problem comes near it. -/
def matchFuel : Nat := 1 <<< 30

def isVar : D y → Bool
  | .var _ => true
  | _ => false

/-- Whether the subject `t` may be assigned to the pattern slot `x`. -/
@[inline] def fits (c : MC) (x : Nat) (t : D y) : Bool :=
  (msort y c.ssort t).le (MS.ofSort (c.psort x))

/-- The pattern variables of the arguments of an AC pattern with their
multiplicities, in order of first occurrence. -/
def groupVars (ps : List (D y)) : List (Nat × Nat) :=
  ps.foldl (fun acc d => match d with
    | .var v =>
      match acc.findIdx? (·.1 == v) with
      | some j => acc.modify j fun (x, m) => (x, m + 1)
      | none => acc ++ [(v, 1)]
    | _ => acc) []

/-- The factors a bound AC pattern variable stands for. -/
def factors (f : Nat) (b : D y) : List (D y) :=
  match b with
  | .ac g bs => if g == f then bs else [b]
  | _ => [b]

section
variable [Interrupt]

mutual
/-- Match `pt` against `t` under `σ`, passing every match to `k` until `k`
returns a value. -/
def mt {α : Type} (c : MC) : Nat → D y → D y → Sb y → (Sb y → Option α) → Option α
  | 0, _, _, _, _ => none
  | n + 1, pt, t, σ, k =>
    match pt with
    | .var i =>
      match σ.getD i none with
      | some b => if Dag.beq b t then k σ else none
      | none => if fits c i t then k (σ.set! i (some t)) else none
    | .atom a => match t with
      | .atom b => if a == b then k σ else none
      | _ => none
    | .free f ps => match t with
      | .free g ts => if f == g && ps.length == ts.length then mtList c n ps ts σ k else none
      | _ => none
    | .comm f a b => match t with
      | .comm g u v =>
        if f == g then
          (mt c n a u σ fun σ => mt c n b v σ k) <|> (mt c n a v σ fun σ => mt c n b u σ k)
        else none
      | _ => none
    | .ac f ps => match t with
      | .ac g ts => if f == g then mac c n f ps ts σ false (fun σ rest => if rest.isEmpty then k σ else none) else none
      | _ => none

/-- Match the patterns `ps` against the subjects `ts`, pairwise. -/
def mtList {α : Type} (c : MC) : Nat → List (D y) → List (D y) → Sb y → (Sb y → Option α) → Option α
  | 0, _, _, _, _ => none
  | n + 1, ps, ts, σ, k =>
    match ps, ts with
    | [], [] => k σ
    | q :: qs, t :: ts => mt c n q t σ fun σ => mtList c n qs ts σ k
    | _, _ => none

/-- AC matching of the arguments `ps` of a pattern of `f` against the
subject's arguments `ss`. With `ext` the subject may keep arguments over,
which `k` receives. -/
def mac {α : Type} (c : MC) : Nat → Nat → List (D y) → List (D y) → Sb y → Bool →
    (Sb y → List (D y) → Option α) → Option α
  | 0, _, _, _, _, _, _ => none
  | n + 1, f, ps, ss, σ, ext, k =>
    match ps.findIdx? (fun d => !isVar d) with
    | some i => tryEach c n f (ps[i]?.getD (.var 0)) (ps.eraseIdx i) [] none ss σ ext k
    | none =>
      -- only variables: bound ones take their factors, unbound ones share the rest
      let groups := groupVars ps
      let bound := groups.filter fun (x, _) => (σ.getD x none).isSome
      let unbound := groups.filter fun (x, _) => (σ.getD x none).isNone
      let need : List (D y) := bound.flatMap fun (x, m) =>
        (List.replicate m (factors f ((σ.getD x none).getD (.var 0)))).flatten
      match removeAll need ss with
      | none => none
      | some ss' => distribute c n f unbound ss' σ ext k

/-- Try the non-variable pattern argument `q` against each subject argument
in turn, skipping a subject equal to the one tried before it; `before` holds
the arguments passed over, reversed. -/
def tryEach {α : Type} (c : MC) : Nat → Nat → D y → List (D y) → List (D y) → Option (D y) →
    List (D y) → Sb y → Bool → (Sb y → List (D y) → Option α) → Option α
  | 0, _, _, _, _, _, _, _, _, _ => none
  | n + 1, f, q, rest, before, prev, ss, σ, ext, k =>
    match ss with
    | [] => none
    | s :: more =>
      Interrupt.guard none fun _ =>
      let skip := match prev with | some x => Dag.beq x s | none => false
      if skip then tryEach c n f q rest (s :: before) prev more σ ext k else
      (mt c n q s σ fun σ' => mac c n f rest (before.reverseAux more) σ' ext k) <|>
        tryEach c n f q rest (s :: before) (some s) more σ ext k

/-- Share the subject arguments `ss` among the unbound pattern variables
`vars` (each with its multiplicity in the pattern). -/
def distribute {α : Type} (c : MC) : Nat → Nat → List (Nat × Nat) → List (D y) → Sb y → Bool →
    (Sb y → List (D y) → Option α) → Option α
  | 0, _, _, _, _, _, _ => none
  | n + 1, f, vars, ss, σ, ext, k =>
    match vars with
    | [] => if ss.isEmpty then k σ [] else if ext then k σ ss else none
    | (x, m) :: more =>
      chooseRun c n f x m (more.isEmpty && !ext) more (runsOf ss) [] [] 0 σ ext k

/-- Choose how many copies `j` of each run the variable `x` of multiplicity
`m` takes; `taken` and `left` collect the choices so far. When `last`, the
variable has to take every remaining argument. -/
def chooseRun {α : Type} (c : MC) : Nat → Nat → Nat → Nat → Bool → List (Nat × Nat) →
    List (D y × Nat) → List (D y) → List (D y) → Nat → Sb y → Bool →
    (Sb y → List (D y) → Option α) → Option α
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, f, x, m, last, more, rs, taken, left, j, σ, ext, k =>
    Interrupt.guard none fun _ =>
    match rs with
    | [] =>
      if taken.isEmpty then none else
      let b : D y := match taken with | [t] => t | _ => .ac f taken
      if fits c x b then distribute c n f more left (σ.set! x (some b)) ext k else none
    | (e, cnt) :: rest =>
      if j * m > cnt then none else
      let here : Option α :=
        if last && j * m != cnt then none
        else chooseRun c n f x m last more rest (taken ++ List.replicate j e)
          (left ++ List.replicate (cnt - j * m) e) 0 σ ext k
      here <|> chooseRun c n f x m last more rs taken left (j + 1) σ ext k
end

/-- The first match of the left side `lhs` (with `nv` slots) against `t` at
the top, with extension when both are products of one AC symbol: the
assignment and the arguments of `t` left over. -/
def mtop (c : MC) (nv : Nat) (lhs t : D y) : Option (Sb y × List (D y)) :=
  let σ0 : Sb y := Array.replicate nv none
  match lhs, t with
  | .ac f ps, .ac g ts =>
    if f == g then mac c matchFuel f ps ts σ0 true (fun σ rest => some (σ, rest)) else none
  | _, _ => mt c matchFuel lhs t σ0 (fun σ => some (σ, []))

/-- Whether the patterns (with `nv` slots) match their subjects
simultaneously, without extension. -/
def mtPairs (c : MC) (nv : Nat) (ps ts : List (D y)) : Bool :=
  (mtList c matchFuel ps ts (Array.replicate nv none) (fun σ => some σ)).isSome

end

end Tamarin.MaudeVariants
