import Tamarin.ReferenceMatching
import Tamarin.FreshSubstitution

/-! Matching by a search that is not verified, followed by a verified test of
its answer. The search binds variables from left to right and backtracks, so
a binding made by one equation prunes the next. Its answer is turned into a
sorted substitution, and the test compares every instantiated pattern with its
subject modulo the axioms. Only the test enters a proof: a wrong or missing
answer of the search can make the caller fall back to the complete matcher,
never accept a pair that does not match. -/
namespace Tamarin.GuessedMatching
open Rewriting
variable {s : Signature}

abbrev Binds (s : Signature) := List (Variable × Term s)

/-- Every entry of a list with the others, in order. -/
def splits {α : Type} : List α → List (α × List α)
  | [] => []
  | x :: xs => (x,xs) :: (splits xs).map fun (y,ys) => (y,x :: ys)

/-- Every way to take some entries out of a list: the taken ones and the rest. -/
def choices {α : Type} : List α → List (List α × List α)
  | [] => [([],[])]
  | x :: xs => (choices xs).flatMap fun (taken,rest) => [(x :: taken,rest),(taken,x :: rest)]

section
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

def bound? (bs : Binds s) (v : Variable) : Option (Term s) :=
  (bs.find? fun e => e.1 = v).map (·.2)

def same (a b : Term s) : Bool := decide (a = b) || ReferenceMatching.equal a b

/-- Remove one entry equal to the term. -/
def take (t : Term s) : List (Term s) → Option (List (Term s))
  | [] => none
  | x :: xs => if same t x then some xs else (take t xs).map (x :: ·)

def takeAll : List (Term s) → List (Term s) → Option (List (Term s))
  | [], rest => some rest
  | t :: ts, rest => (take t rest).bind (takeAll ts)

abbrev Search (s : Signature) := Binds s → (Binds s → Option (Binds s)) → Option (Binds s)

/-- Match the pairs one after the other. -/
def seq (step : Term s → Term s → Search s) : List (Term s × Term s) → Search s
  | [], bs, k => k bs
  | (p,t) :: rest, bs, k => step p t bs fun bs' => seq step rest bs' k

/-- Match every pattern operand with an operand of the subject of its own. -/
def operands (step : Term s → Term s → Search s) : List (Term s) → List (Term s) → Binds s →
    (List (Term s) → Binds s → Option (Binds s)) → Option (Binds s)
  | [], subject, bs, k => k subject bs
  | p :: ps, subject, bs, k =>
    (splits subject).findSome? fun (t,others) =>
      step p t bs fun bs' => operands step ps others bs' k

/-- Give every variable operand a nonempty part of what is left of the
subject. A variable that is already bound takes the operands of its image. -/
def spread (f : s.ACSym) : List Variable → List (Term s) → Search s
  | [], subject, bs, k => if subject.isEmpty then k bs else none
  | v :: vs, subject, bs, k =>
    match bound? bs v with
    | some t =>
      match takeAll (ACRepresentation.flatten f t) subject with
      | some rest => spread f vs rest bs k
      | none => none
    | none =>
      if vs.isEmpty then
        match subject with
        | [] => none
        | t :: ts =>
          let u := ACRepresentation.fold f t ts
          if u.checkSort v.sort then k ((v,u) :: bs) else none
      else
        (choices subject).findSome? fun (taken,rest) =>
          match taken with
          | [] => none
          | t :: ts =>
            let u := ACRepresentation.fold f t ts
            if u.checkSort v.sort then spread f vs rest ((v,u) :: bs) k else none

def variableOf : Term s → Option Variable
  | .var v => some v
  | _ => none

/-- The search. The first argument bounds the depth of the pattern. -/
def go : Nat → Term s → Term s → Search s
  | 0, _, _, _, _ => none
  | _+1, .var v, t, bs, k =>
    match bound? bs v with
    | some u => if same u t then k bs else none
    | none => if t.checkSort v.sort then k ((v,t) :: bs) else none
  | _+1, .atom a, .atom b, bs, k => if a = b then k bs else none
  | fuel+1, .free f xs, .free g ys, bs, k =>
    if h : f = g then seq (go fuel) (List.ofFn fun i => (xs i,ys (h ▸ i))) bs k else none
  | fuel+1, .comm f a b, .comm g c d, bs, k =>
    if f = g then
      (go fuel a c bs fun bs' => go fuel b d bs' k) <|> (go fuel a d bs fun bs' => go fuel b c bs' k)
    else none
  | fuel+1, .ac f a b, .ac g c d, bs, k =>
    if f = g then
      let pattern := ACRepresentation.flatten f (.ac f a b)
      let subject := ACRepresentation.flatten f (.ac g c d)
      let solid := pattern.filter fun p => (variableOf p).isNone
      let open_ := pattern.filterMap variableOf
      if subject.length < pattern.length then none
      else operands (go fuel) solid subject bs fun rest bs' =>
        let (known,fresh) := open_.partition fun v => (bound? bs' v).isSome
        spread f (known ++ fresh) rest bs' k
    else none
  | _+1, _, _, _, _ => none

def guess (pairs : List (Term s × Term s)) : Option (Binds s) :=
  seq (go 4096) pairs [] some

/-- The substitution of the bindings that have the sort of their variable. -/
def substOf (bs : Binds s) : Substitution s :=
  Substitution.fromBindings (bs.filter fun e => e.2.checkSort e.1.sort) (by
    intro v t member
    exact Term.checkSort_sound _ _ (by simpa using (List.mem_filter.mp member).2))

/-- Whether the substitution turns every pattern into its subject. -/
def fits (θ : Substitution s) (pairs : List (Term s × Term s)) : Bool :=
  pairs.all fun e => ReferenceMatching.equal (θ.apply e.1) e.2

theorem fits_sound {θ : Substitution s} {pairs : List (Term s × Term s)} (h : fits θ pairs = true) :
    ∀ e ∈ pairs, EquivB (θ.apply e.1) e.2 :=
  fun e member => (ReferenceMatching.equal_iff ..).mp (List.all_eq_true.mp h e member)

/-- A guessed substitution that passes the test. -/
def find (pairs : List (Term s × Term s)) : Option (Substitution s) :=
  match guess pairs with
  | some bs => if fits (substOf bs) pairs then some (substOf bs) else none
  | none => none

theorem find_sound {pairs : List (Term s × Term s)} {θ : Substitution s} (h : find pairs = some θ) :
    ∀ e ∈ pairs, EquivB (θ.apply e.1) e.2 := by
  unfold find at h
  split at h
  · split at h
    · next ok => cases h; exact fits_sound ok
    · contradiction
  · contradiction

end
end Tamarin.GuessedMatching
