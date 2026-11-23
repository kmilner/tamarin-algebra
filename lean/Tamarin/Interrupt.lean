/-!
# Interruptible searches

A long search asks its caller from time to time whether to go on. The caller
is a function `poll : Unit → Bool` that an export receives as an argument.
An export runs its search only when `poll ()` is `false`, and the searches
carry the function, with that fact, as an instance argument `[Interrupt]`.

Logically nothing changes. A function on `Unit` has one value, so under an
instance every further question has the answer `false`, and the combinators
below are defined as the plain computation they guard: `guard d x` is `x ()`
and `map f xs` is `xs.map f`. No proof about a search has to mention them.
All instances are equal (`Interrupt.eq_never`), so a theorem proved for the
default instance holds for every instance.

Only the compiled code asks. Each combinator is replaced (`@[csimp]`) by an
equal one that calls `poll` and returns its default without computing when
the reply is `true`. Inside Lean that branch is dead. It exists for a caller
outside Lean whose `poll` is not a function: the C bridge passes a closure
that starts to reply `true` when the request was cancelled or a work budget
ran out. A run in which that closure replied `false` every time is a run
with the constant function, so its result is the one the theorems describe.
The bridge discards the result of every other run. What the truncated
computation returns is therefore irrelevant, and it returns quickly because
every guarded loop stops at its next question.
-/
namespace Tamarin

/-- The caller asks the search to stop. No caller that is a function does. -/
def Interrupt.Stop (_ : Unit) : Prop := False

/-- The caller of the search in progress: a way to decide, each time it is
asked, that the search does not have to stop. It is an instance argument, so
a search receives it from the search that called it without naming it. The
audited modules declare no class of their own. An instance of this type is
one of the standard class `Decidable`, as an instance of `DecidableEq` is,
and the compiler specializes a search for it in the same way. -/
abbrev Interrupt := (u : Unit) → Decidable (Interrupt.Stop u)

namespace Interrupt

/-- Ask the caller. -/
@[inline] def poll [i : Interrupt] (u : Unit) : Bool := @decide (Stop u) (i u)

theorem quiet [Interrupt] : poll () = false := decide_eq_false id

/-- The caller that is never asked: every search runs to its end. -/
@[instance_reducible] def never : Interrupt := fun _ => isFalse id

/-- A search that received no caller is not interrupted. -/
instance (priority := low) : Interrupt := never

theorem eq_never (i : Interrupt) : i = never := funext fun _ => Subsingleton.elim _ _

variable {α β : Type}

/-- The computation `x ()`. The compiled code first asks the caller and
returns `dflt` instead when told to stop. -/
@[reducible] def guard [Interrupt] (_dflt : α) (x : Unit → α) : α := x ()

@[inline] private def guardAsking [Interrupt] (dflt : α) (x : Unit → α) : α :=
  if poll () then dflt else x ()

@[csimp] private theorem guard_eq_asking : @guard = @guardAsking := by
  funext α i dflt x
  simp [guard, guardAsking, quiet]

/-- `xs.map f`. The compiled code asks the caller before every element and
ends the list when told to stop. -/
@[reducible] def map [Interrupt] (f : α → β) (xs : List α) : List β := xs.map f

private def mapAsking [Interrupt] (f : α → β) : List α → Array β → List β
  | [], acc => acc.toList
  | x :: xs, acc => if poll () then acc.toList else mapAsking f xs (acc.push (f x))

private theorem mapAsking_eq [Interrupt] (f : α → β) (xs : List α) (acc : Array β) :
    mapAsking f xs acc = acc.toList ++ xs.map f := by
  induction xs generalizing acc with
  | nil => simp [mapAsking]
  | cons x xs ih => simp [mapAsking, Interrupt.quiet, ih]

private def mapImpl [Interrupt] (f : α → β) (xs : List α) : List β := mapAsking f xs #[]

@[csimp] private theorem map_eq_asking : @map = @mapImpl := by
  funext α β i f xs
  simp [map, mapImpl, mapAsking_eq]

/-- `xs.flatMap f`, asking before every element. -/
@[reducible] def flatMap [Interrupt] (f : α → List β) (xs : List α) : List β := xs.flatMap f

private def flatMapAsking [Interrupt] (f : α → List β) : List α → Array β → List β
  | [], acc => acc.toList
  | x :: xs, acc => if poll () then acc.toList else flatMapAsking f xs (acc ++ f x)

private theorem flatMapAsking_eq [Interrupt] (f : α → List β) (xs : List α) (acc : Array β) :
    flatMapAsking f xs acc = acc.toList ++ xs.flatMap f := by
  induction xs generalizing acc with
  | nil => simp [flatMapAsking]
  | cons x xs ih => simp [flatMapAsking, Interrupt.quiet, ih]

private def flatMapImpl [Interrupt] (f : α → List β) (xs : List α) : List β := flatMapAsking f xs #[]

@[csimp] private theorem flatMap_eq_asking : @flatMap = @flatMapImpl := by
  funext α β i f xs
  simp [flatMap, flatMapImpl, flatMapAsking_eq]

/-- `xs.filterMap f`, asking before every element. -/
@[reducible] def filterMap [Interrupt] (f : α → Option β) (xs : List α) : List β := xs.filterMap f

private def filterMapAsking [Interrupt] (f : α → Option β) : List α → Array β → List β
  | [], acc => acc.toList
  | x :: xs, acc =>
    if poll () then acc.toList
    else match f x with
      | some y => filterMapAsking f xs (acc.push y)
      | none => filterMapAsking f xs acc

private theorem filterMapAsking_eq [Interrupt] (f : α → Option β) (xs : List α) (acc : Array β) :
    filterMapAsking f xs acc = acc.toList ++ xs.filterMap f := by
  induction xs generalizing acc with
  | nil => simp [filterMapAsking]
  | cons x xs ih =>
    cases h : f x <;> simp [filterMapAsking, Interrupt.quiet, ih, h]

private def filterMapImpl [Interrupt] (f : α → Option β) (xs : List α) : List β := filterMapAsking f xs #[]

@[csimp] private theorem filterMap_eq_asking : @filterMap = @filterMapImpl := by
  funext α β i f xs
  simp [filterMap, filterMapImpl, filterMapAsking_eq]

/-- `xs.filter p`, asking before every element. -/
@[reducible] def filter [Interrupt] (p : α → Bool) (xs : List α) : List α := xs.filter p

private def filterAsking [Interrupt] (p : α → Bool) : List α → Array α → List α
  | [], acc => acc.toList
  | x :: xs, acc =>
    if poll () then acc.toList
    else if p x then filterAsking p xs (acc.push x) else filterAsking p xs acc

private theorem filterAsking_eq [Interrupt] (p : α → Bool) (xs : List α) (acc : Array α) :
    filterAsking p xs acc = acc.toList ++ xs.filter p := by
  induction xs generalizing acc with
  | nil => simp [filterAsking]
  | cons x xs ih =>
    cases h : p x <;> simp [filterAsking, Interrupt.quiet, ih, h]

private def filterImpl [Interrupt] (p : α → Bool) (xs : List α) : List α := filterAsking p xs #[]

@[csimp] private theorem filter_eq_asking : @filter = @filterImpl := by
  funext α i p xs
  simp [filter, filterImpl, filterAsking_eq]

/-- `xs.findSome? f`, asking before every element. -/
@[reducible] def findSome? [Interrupt] (f : α → Option β) (xs : List α) : Option β := xs.findSome? f

private def findSomeAsking [Interrupt] (f : α → Option β) : List α → Option β
  | [] => none
  | x :: xs =>
    if poll () then none
    else match f x with
      | some y => some y
      | none => findSomeAsking f xs

@[csimp] private theorem findSome_eq_asking : @findSome? = @findSomeAsking := by
  funext α β i f xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : f x <;> simp [findSome?, findSomeAsking, Interrupt.quiet, h]
    simpa [findSome?] using ih

/-- An export hands its caller's `poll` to a search. The search runs when the
first reply is `false`, and the export answers `stopped` otherwise. -/
@[inline] def run (poll : Unit → Bool) (stopped : α) (search : Interrupt → α) : α :=
  if h : poll () = false then
    search fun u =>
      if again : poll u = true then isTrue (absurd again (by cases u; simp [h])) else isFalse id
  else stopped

theorem run_quiet {poll : Unit → Bool} (h : poll () = false) (stopped : α) (search : Interrupt → α) :
    run poll stopped search = search never := by
  simp only [run, h, ↓reduceDIte]
  exact congrArg search (eq_never _)

theorem run_stopped {poll : Unit → Bool} (h : poll () = true) (stopped : α) (search : Interrupt → α) :
    run poll stopped search = stopped := by
  simp [run, h]

end Interrupt
end Tamarin
