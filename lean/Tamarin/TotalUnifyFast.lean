import Tamarin.TotalUnifyDecline

/-! A faster evaluation of `TotalUnifyWire.run` for queries that free
factoring solves completely, and for those whose residual has an equation
with clashing roots.

The terms of a decoded query are lowered to `FTerm`, which keeps the kind,
identifier and sorts of every application at its node and its arguments in
a list. Free factoring is run on the lowered query by the same steps as
`FreeFactoring.factor`, recording its bindings instead of composing
substitutions, and the images of the query variables are read from the
bindings. Everything is proved equal to the definition it replaces. -/
namespace Tamarin.TotalUnifyFast
open TotalUnifyWire

/-- Equality of variables, field by field. -/
def varEq (v w : Variable) : Bool := v.id == w.id && v.sort == w.sort

@[simp] theorem varEq_eq (v w : Variable) : varEq v w = (v == w) := by
  cases v; cases w
  rw [Bool.eq_iff_iff]
  simp [varEq]

/-- A term with the declaration of every application at its node. -/
inductive FTerm where
  | var (v : Variable)
  | atom (id : UInt64) (sort : SortId)
  | app (kind id : UInt64) (out : SortId) (ins : List SortId) (args : List FTerm)

namespace FTerm

mutual
/-- Syntactic equality. -/
def beq : FTerm → FTerm → Bool
  | .var v, .var w => varEq v w
  | .atom i k, .atom j l => i == j && k == l
  | .app k i o ins args, .app k' i' o' ins' args' =>
    k == k' && i == i' && o == o' && ins == ins' && beqAll args args'
  | _, _ => false
def beqAll : List FTerm → List FTerm → Bool
  | [], [] => true
  | a :: as, b :: bs => beq a b && beqAll as bs
  | _, _ => false
end

mutual
theorem beq_iff : ∀ a b : FTerm, beq a b = true ↔ a = b
  | .var v, .var w => by simp [beq]
  | .atom i k, .atom j l => by simp [beq]
  | .app k i o ins args, .app k' i' o' ins' args' => by
    simp only [beq, Bool.and_eq_true, beq_iff_eq, beqAll_iff args args', app.injEq, and_assoc]
  | .var _, .atom .. | .var _, .app .. | .atom .., .var _ | .atom .., .app ..
  | .app .., .var _ | .app .., .atom .. => by simp [beq]
theorem beqAll_iff : ∀ as bs : List FTerm, beqAll as bs = true ↔ as = bs
  | [], [] => by simp [beqAll]
  | a :: as, b :: bs => by
    simp only [beqAll, Bool.and_eq_true, beq_iff a b, beqAll_iff as bs, List.cons.injEq]
  | [], _ :: _ | _ :: _, [] => by simp [beqAll]
end

mutual
/-- Whether the variable occurs. -/
def occurs (v : Variable) : FTerm → Bool
  | .var w => varEq v w
  | .atom .. => false
  | .app _ _ _ _ args => occursAll v args
def occursAll (v : Variable) : List FTerm → Bool
  | [] => false
  | t :: ts => occurs v t || occursAll v ts
end

mutual
/-- `Term.checkSort` with the sorts read from the nodes. -/
def check : FTerm → SortId → Bool
  | .var v, s => Subsort.check v.sort s
  | .atom _ k, s => Subsort.check k s
  | .app _ _ out ins args, s => Subsort.check out s && checkAll args ins
def checkAll : List FTerm → List SortId → Bool
  | t :: ts, k :: ks => check t k && checkAll ts ks
  | _, _ => true
end

mutual
/-- Substitute every variable. -/
def subst (σ : Variable → FTerm) : FTerm → FTerm
  | .var v => σ v
  | .atom i k => .atom i k
  | .app k i o ins args => .app k i o ins (substAll σ args)
def substAll (σ : Variable → FTerm) : List FTerm → List FTerm
  | [] => []
  | t :: ts => subst σ t :: substAll σ ts
end

mutual
/-- `FreeFactoring.weight`. -/
def weight : FTerm → Nat
  | .var _ | .atom .. => 1
  | .app _ _ _ _ args => 1 + weightAll args
def weightAll : List FTerm → Nat
  | [] => 0
  | t :: ts => weight t + weightAll ts
end

mutual
/-- `Term.variables`. -/
def vars : FTerm → List Variable
  | .var v => [v]
  | .atom .. => []
  | .app _ _ _ _ args => varsAll args
def varsAll : List FTerm → List Variable
  | [] => []
  | t :: ts => vars t ++ varsAll ts
end

mutual
/-- The words of a term, as `TotalUnifyWire.write` gives them. -/
def emit : FTerm → Array UInt64 → Option (Array UInt64)
  | .var v, acc => (WordEncoding.pack v.id).map fun id => ((acc.push 0).push id).push (sortCode v.sort)
  | .atom i k, acc => some (((acc.push 1).push i).push (sortCode k))
  | .app k i _ _ args, acc => do
    let acc ← emitAll args acc
    let n ← WordEncoding.pack args.length
    return ((acc.push k).push i).push n
def emitAll : List FTerm → Array UInt64 → Option (Array UInt64)
  | [], acc => some acc
  | t :: ts, acc => do emitAll ts (← emit t acc)
end

mutual
/-- Replace one variable. -/
def replace (v : Variable) (t : FTerm) : FTerm → FTerm
  | .var w => if varEq w v then t else .var w
  | .atom i k => .atom i k
  | .app k i o ins args => .app k i o ins (replaceAll v t args)
def replaceAll (v : Variable) (t : FTerm) : List FTerm → List FTerm
  | [] => []
  | u :: us => replace v t u :: replaceAll v t us
end

mutual
/-- `NarrowingClash.possible`. -/
def possible : FTerm → SortId → Bool
  | .var v, k => Subsort.check v.sort k || Subsort.check k v.sort
  | .atom _ a, k => Subsort.check a k
  | .app _ _ out ins args, k => Subsort.check out k && possibleAll args ins
def possibleAll : List FTerm → List SortId → Bool
  | t :: ts, k :: ks => possible t k && possibleAll ts ks
  | _, _ => true
end

/-- `Term.rootSort`. -/
def rootSort : FTerm → SortId
  | .var v => v.sort
  | .atom _ k => k
  | .app _ _ o _ _ => o

/-- `NarrowingClash.heads`. -/
def heads : FTerm → FTerm → Bool
  | .var _, _ | _, .var _ => true
  | .atom i k, .atom j l => i == j && k == l
  | .app k f .., .app k' g .. => k == k' && f == g
  | _, _ => false

/-- `ForcedOperands.leaves`. -/
def leaves : FTerm → Nat
  | .app k _ _ _ [a, b] => if k == 4 then leaves a + leaves b else 1
  | _ => 1

/-- A product at the root. -/
def product : FTerm → Bool
  | .app k .. => k == 4
  | _ => false

end FTerm

section Lower
variable {d : Dictionary}

/-- The lowered term. One declaration lookup per application. -/
def lower : Term d.sig → FTerm
  | .var v => .var v
  | .atom a => .atom a.val.1 a.val.2
  | .free f xs =>
    let dl := info f
    .app 2 f.val (sortOf dl.output) (dl.inputs.map sortOf)
      (List.ofFn (n := dl.inputs.length) fun i => lower (xs i))
  | .comm f a b =>
    let k := sortOf (info f).output
    .app 3 f.val k [k, k] [lower a, lower b]
  | .ac f a b =>
    let k := sortOf (info f).output
    .app 4 f.val k [k, k] [lower a, lower b]

theorem lower_free (f : d.sig.FreeSym) (xs : Fin (d.sig.arity f) → Term d.sig) :
    lower (.free f xs) = .app 2 f.val (d.sig.outputSort f) (List.ofFn (d.sig.inputSort f))
      (List.ofFn fun i => lower (xs i)) := by
  simp only [lower]
  congr 1
  apply List.ext_getElem <;> simp

end Lower

namespace FTerm

theorem occursAll_eq (v : Variable) (l : List FTerm) : occursAll v l = l.any (occurs v) := by
  induction l with
  | nil => rfl
  | cons t ts ih => simp [occursAll, ih]

theorem substAll_eq (σ : Variable → FTerm) (l : List FTerm) : substAll σ l = l.map (subst σ) := by
  induction l with
  | nil => rfl
  | cons t ts ih => simp [substAll, ih]

theorem weightAll_eq (l : List FTerm) : weightAll l = (l.map weight).sum := by
  induction l with
  | nil => rfl
  | cons t ts ih => simp [weightAll, ih]

theorem varsAll_eq (l : List FTerm) : varsAll l = (l.map vars).flatten := by
  induction l with
  | nil => rfl
  | cons t ts ih => simp [varsAll, ih]

theorem checkAll_ofFn {n : Nat} (g : Fin n → FTerm) (h : Fin n → SortId) :
    checkAll (List.ofFn g) (List.ofFn h) = (List.finRange n).all fun i => check (g i) (h i) := by
  induction n with
  | zero => simp [checkAll]
  | succ n ih =>
    simp only [List.ofFn_succ, checkAll, List.finRange_succ, List.all_cons, List.all_map,
      Function.comp_def]
    rw [ih]

mutual
theorem subst_var : ∀ t : FTerm, subst .var t = t
  | .var _ => rfl
  | .atom .. => rfl
  | .app k i o ins args => by simp only [subst, substAll_var args]
theorem substAll_var : ∀ l : List FTerm, substAll .var l = l
  | [] => rfl
  | t :: ts => by simp only [substAll, subst_var t, substAll_var ts]
end

mutual
theorem subst_subst (σ τ : Variable → FTerm) : ∀ t : FTerm,
    subst τ (subst σ t) = subst (fun v => subst τ (σ v)) t
  | .var _ => rfl
  | .atom .. => rfl
  | .app k i o ins args => by simp only [subst, substAll_subst σ τ args]
theorem substAll_subst (σ τ : Variable → FTerm) : ∀ l : List FTerm,
    substAll τ (substAll σ l) = substAll (fun v => subst τ (σ v)) l
  | [] => rfl
  | t :: ts => by simp only [substAll, subst_subst σ τ t, substAll_subst σ τ ts]
end

end FTerm

section Lower
variable {d : Dictionary}
open FTerm

theorem lower_occurs (v : Variable) (t : Term d.sig) : (lower t).occurs v = true ↔ t.Occurs v := by
  induction t with
  | var w => simp [lower, occurs, Term.Occurs]
  | atom a => simp [lower, occurs, Term.Occurs]
  | free f xs ih =>
    rw [lower_free]
    simp only [occurs, occursAll_eq, List.any_eq_true, List.mem_ofFn, Term.Occurs]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, h⟩
      exact ⟨i, (ih i).mp h⟩
    · rintro ⟨i, h⟩
      exact ⟨_, ⟨i, rfl⟩, (ih i).mpr h⟩
  | comm f a b ia ib | ac f a b ia ib =>
    simp [lower, occurs, occursAll, Term.Occurs, ia, ib]

theorem lower_check (t : Term d.sig) (k : SortId) : (lower t).check k = t.checkSort k := by
  induction t generalizing k with
  | var w => simp [lower, check, Term.checkSort]
  | atom a => simp [lower, check, Term.checkSort]
  | free f xs ih =>
    rw [lower_free]
    simp only [check, Term.checkSort, checkAll_ofFn, ih]
  | comm f a b ia ib | ac f a b ia ib =>
    simp [lower, check, checkAll, Term.checkSort, ia, ib, Bool.and_assoc]

theorem lower_inj {a b : Term d.sig} (h : lower a = lower b) : a = b := by
  induction a generalizing b with
  | var v => cases b <;> simp_all [lower]
  | atom x =>
    cases b <;> simp [lower] at h
    next y => exact congrArg Term.atom (Subtype.ext (Prod.ext h.1 h.2))
  | free f xs ih =>
    cases b with
    | free g ys =>
      rw [lower_free, lower_free] at h
      simp only [app.injEq, true_and] at h
      obtain ⟨hf, -, -, hargs⟩ := h
      obtain rfl : f = g := Subtype.ext hf
      have each (i : Fin (d.sig.arity f)) : lower (xs i) = lower (ys i) := by
        have := congrArg (fun l => l[i.val]?) hargs
        simpa using this
      congr 1
      funext i
      exact ih i (each i)
    | _ => simp [lower] at h
  | comm f x y ix iy =>
    cases b with
    | comm g u w =>
      simp only [lower, app.injEq, true_and, List.cons.injEq, and_true] at h
      obtain ⟨hf, -, -, hx, hy⟩ := h
      obtain rfl : f = g := Subtype.ext hf
      rw [ix hx, iy hy]
    | _ => simp [lower] at h
  | ac f x y ix iy =>
    cases b with
    | ac g u w =>
      simp only [lower, app.injEq, true_and, List.cons.injEq, and_true] at h
      obtain ⟨hf, -, -, hx, hy⟩ := h
      obtain rfl : f = g := Subtype.ext hf
      rw [ix hx, iy hy]
    | _ => simp [lower] at h

theorem lower_beq (a b : Term d.sig) : beq (lower a) (lower b) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp [(beq_iff _ _).mpr rfl]
  · have : beq (lower a) (lower b) = false := by
      cases e : beq (lower a) (lower b)
      · rfl
      · exact absurd (lower_inj ((beq_iff _ _).mp e)) h
    simp [this, h]

theorem lower_subst (σ : Variable → Term d.sig) (t : Term d.sig) :
    lower (t.subst σ) = (lower t).subst (fun v => lower (σ v)) := by
  induction t with
  | var w => rfl
  | atom a => rfl
  | free f xs ih =>
    simp only [Term.subst]
    rw [lower_free, lower_free]
    simp only [subst, substAll_eq, List.map_ofFn, Function.comp_def, ih]
  | comm f a b ia ib | ac f a b ia ib =>
    simp [lower, Term.subst, subst, substAll, ia, ib]

theorem lower_weight (t : Term d.sig) : (lower t).weight = FreeFactoring.weight t := by
  induction t with
  | var w => rfl
  | atom a => rfl
  | free f xs ih =>
    rw [lower_free]
    simp only [weight, weightAll_eq, List.map_ofFn, Function.comp_def, ih, FreeFactoring.weight]
  | comm f a b ia ib | ac f a b ia ib =>
    simp [lower, weight, weightAll, FreeFactoring.weight, ia, ib]
    omega

theorem lower_vars (t : Term d.sig) : (lower t).vars = t.variables := by
  induction t with
  | var w => rfl
  | atom a => rfl
  | free f xs ih =>
    rw [lower_free]
    simp only [vars, varsAll_eq, List.map_ofFn, Function.comp_def, ih, Term.variables]
  | comm f a b ia ib | ac f a b ia ib =>
    simp [lower, vars, varsAll, Term.variables, ia, ib]


/-- The words of tokens. -/
def tokenWords (ts : List Token) : Array UInt64 := (ts.flatMap Token.words).toArray

theorem tokenWords_append (xs ys : List Token) : tokenWords (xs ++ ys) = tokenWords xs ++ tokenWords ys := by
  simp [tokenWords]

private theorem push3 (acc : Array UInt64) (a b c : UInt64) :
    ((acc.push a).push b).push c = acc ++ #[a,b,c] := by
  apply Array.toList_inj.mp
  simp

private theorem emitAll_map (ts : List (Term d.sig))
    (ih : ∀ t ∈ ts, ∀ acc, (lower t).emit acc = (write t).map fun c => acc ++ tokenWords c)
    (acc : Array UInt64) :
    emitAll (ts.map lower) acc = (ts.mapM write).map fun cs => acc ++ tokenWords cs.flatten := by
  induction ts generalizing acc with
  | nil => simp [emitAll, tokenWords]
  | cons t ts step =>
    simp only [List.map_cons, emitAll, List.mapM_cons]
    rw [ih t List.mem_cons_self]
    cases write t with
    | none => rfl
    | some c =>
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, bind_pure_comp]
      rw [step (fun u hu => ih u (List.mem_cons_of_mem _ hu))]
      cases ts.mapM write with
      | none => rfl
      | some cs => simp [tokenWords_append, Array.append_assoc]

theorem lower_emit (t : Term d.sig) (acc : Array UInt64) :
    (lower t).emit acc = (write t).map fun c => acc ++ tokenWords c := by
  induction t generalizing acc with
  | var v =>
    simp only [lower, emit, write]
    cases WordEncoding.pack v.id <;> simp [tokenWords, Token.words, push3]
  | atom a => simp [lower, emit, write, tokenWords, Token.words, push3]
  | free f xs ih =>
    rw [lower_free]
    have list : (List.ofFn fun i => lower (xs i)) = (List.ofFn xs).map lower := by
      rw [List.map_ofFn]; rfl
    have codes : (List.finRange (d.sig.arity f)).mapM (fun i => write (xs i)) = (List.ofFn xs).mapM write := by
      have : List.ofFn xs = (List.finRange (d.sig.arity f)).map xs := by
        simp only [List.finRange, List.map_ofFn]; rfl
      rw [this, List.mapM_map]
      rfl
    simp only [emit, write, list, bind_pure_comp, Option.bind_eq_bind, codes]
    rw [emitAll_map _ (fun u hu acc => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
      exact ih i acc)]
    have len : ((List.ofFn xs).map lower).length = d.sig.arity f := by simp
    rw [len]
    cases (List.ofFn xs).mapM write with
    | none => rfl
    | some cs =>
      cases WordEncoding.pack (d.sig.arity f) <;> simp [tokenWords, Token.words, push3]
  | comm f l r il ir | ac f l r il ir =>
    simp only [lower, emit, emitAll, write, il, ir, bind_pure_comp, Option.bind_eq_bind,
      List.length_cons, List.length_nil]
    cases write l with
    | none => rfl
    | some a =>
      cases write r with
      | none => rfl
      | some b =>
        have two : (2 : Nat) < UInt64.size := by decide
        simp [tokenWords, Token.words, push3, WordEncoding.pack, two]
end Lower


namespace FTerm

mutual
theorem replace_eq (v : Variable) (t : FTerm) : ∀ u : FTerm,
    replace v t u = u.subst (fun w => if w = v then t else .var w)
  | .var w => by by_cases h : w = v <;> simp [replace, subst, h]
  | .atom .. => rfl
  | .app k i o ins args => by simp only [replace, subst, replaceAll_eq v t args]
theorem replaceAll_eq (v : Variable) (t : FTerm) : ∀ us : List FTerm,
    replaceAll v t us = substAll (fun w => if w = v then t else .var w) us
  | [] => rfl
  | u :: us => by simp only [replaceAll, substAll, replace_eq v t u, replaceAll_eq v t us]
end

end FTerm

/-! ### Free factoring on lowered terms -/

/-- An equation of lowered terms. -/
abbrev FEq := FTerm × FTerm

/-- `FreeFactoring.Frame` with the bindings listed, the latest first. -/
structure FFrame where
  todo : List FEq
  kept : List FEq
  binds : List (Variable × FTerm)

open FTerm

def swap (v : Variable) (t u : FTerm) : FTerm := if u.occurs v then FTerm.replace v t u else u

def rewrite (v : Variable) (t : FTerm) (eqs : List FEq) : List FEq :=
  eqs.map fun e => (swap v t e.1, swap v t e.2)

def bindable (v : Variable) (t : FTerm) : Bool := !(t.occurs v) && t.check v.sort

def bind (v : Variable) (t : FTerm) (rest kept : List FEq) (bs : List (Variable × FTerm)) : FFrame :=
  ⟨rewrite v t (rest ++ kept), [], (v, t) :: bs⟩

def settle (a b : FTerm) (rest kept : List FEq) (bs : List (Variable × FTerm)) : FFrame :=
  if beq a b then ⟨rest, kept, bs⟩
  else
    let defer : FFrame := ⟨rest, (a, b) :: kept, bs⟩
    match a, b with
    | .var v, t =>
      if bindable v t then bind v t rest kept bs
      else
        match t with
        | .var w => if bindable w (.var v) then bind w (.var v) rest kept bs else defer
        | _ => defer
    | t, .var v => if bindable v t then bind v t rest kept bs else defer
    | .app k f _ _ xs, .app k' g _ _ ys =>
      if k == 2 && k' == 2 && f == g then ⟨xs.zip ys ++ rest, kept, bs⟩ else defer
    | _, _ => defer

def advance (a b : FTerm) (rest kept : List FEq) (bs : List (Variable × FTerm)) : FFrame :=
  match a, b with
  | .app k f o ins xs, .app k' g o' ins' ys =>
    if k == 2 && k' == 2 then
      if f == g then ⟨xs.zip ys ++ rest, kept, bs⟩
      else ⟨rest, (.app k f o ins xs, .app k' g o' ins' ys) :: kept, bs⟩
    else settle (.app k f o ins xs) (.app k' g o' ins' ys) rest kept bs
  | a, b => settle a b rest kept bs

def go : Nat → FFrame → FFrame
  | 0, st => st
  | n + 1, st =>
    match st with
    | ⟨[], _, _⟩ => st
    | ⟨(a, b) :: rest, kept, bs⟩ => go n (advance a b rest kept bs)

def split (a b : FTerm) (rest kept : List FEq) (bs : List (Variable × FTerm)) : FFrame :=
  match a, b with
  | .app k f o ins xs, .app k' g o' ins' ys =>
    if k == 2 && k' == 2 then
      if f == g then ⟨xs.zip ys ++ rest, kept, bs⟩
      else ⟨rest, (.app k f o ins xs, .app k' g o' ins' ys) :: kept, bs⟩
    else if beq (.app k f o ins xs) (.app k' g o' ins' ys) then ⟨rest, kept, bs⟩
    else ⟨rest, (.app k f o ins xs, .app k' g o' ins' ys) :: kept, bs⟩
  | a, b => if beq a b then ⟨rest, kept, bs⟩ else ⟨rest, (a, b) :: kept, bs⟩

def spread : Nat → FFrame → FFrame
  | 0, st => st
  | n + 1, st =>
    match st with
    | ⟨[], _, _⟩ => st
    | ⟨(a, b) :: rest, kept, bs⟩ => spread n (split a b rest kept bs)

def fuel (eqs : List FEq) : Nat :=
  let size := (eqs.map fun e => e.1.weight + e.2.weight).sum + eqs.length + 2
  size * size

def factor (eqs : List FEq) : FFrame :=
  let n := fuel eqs
  let st := spread n ⟨eqs, [], []⟩
  go n ⟨st.todo ++ st.kept, [], st.binds⟩

/-- The substitution of the bindings: the earliest is applied first. -/
def chain : List (Variable × FTerm) → Variable → FTerm
  | [], v => .var v
  | (w, t) :: bs, v => FTerm.subst (fun u => if u = w then t else .var u) (chain bs v)


section Simulation
variable {d : Dictionary}

def lowerEq (e : Equation d.sig) : FEq := (lower e.lhs, lower e.rhs)

/-- A frame of free factoring and a frame on lowered terms in step. -/
structure Sim {p : Problem d.sig} (st : FreeFactoring.Frame p) (fs : FFrame) : Prop where
  todo : fs.todo = st.todo.map lowerEq
  kept : fs.kept = st.kept.map lowerEq
  image : ∀ v, lower (st.θ.image v) = chain fs.binds v

theorem lower_children (f : d.sig.FreeSym) (xs ys : Fin (d.sig.arity f) → Term d.sig) :
    (Matching.children f xs ys).map lowerEq =
      (List.ofFn fun i => lower (xs i)).zip (List.ofFn fun i => lower (ys i)) := by
  apply List.ext_getElem <;> simp [Matching.children, lowerEq]

theorem lower_replace (v : Variable) (t u : Term d.sig) :
    lower (FreeFactoring.replace v t u) = FTerm.replace v (lower t) (lower u) := by
  rw [replace_eq]
  induction u with
  | var w => by_cases h : w = v <;> simp [FreeFactoring.replace, lower, subst, h]
  | atom a => rfl
  | free f xs ih =>
    simp only [FreeFactoring.replace]
    rw [lower_free, lower_free]
    simp only [subst, substAll_eq, List.map_ofFn, Function.comp_def]
    congr 1
    congr 1
    funext i
    rw [← ih i]
    simp
  | comm f a b ia ib | ac f a b ia ib =>
    simp [FreeFactoring.replace, lower, subst, substAll, ia, ib]

theorem lower_swap (v : Variable) (t u : Term d.sig) :
    lower (FreeFactoring.swap v t u) = swap v (lower t) (lower u) := by
  unfold FreeFactoring.swap swap
  by_cases h : u.Occurs v
  · simp only [h, ↓reduceIte, (lower_occurs v u).mpr h, lower_replace]
  · have no : (lower u).occurs v = false := by
      cases e : (lower u).occurs v
      · rfl
      · exact absurd ((lower_occurs v u).mp e) h
    simp only [h, ↓reduceIte, no, Bool.false_eq_true]

theorem lower_rewrite (v : Variable) (t : Term d.sig) (eqs : Problem d.sig) :
    (FreeFactoring.rewrite v t eqs).map lowerEq = rewrite v (lower t) (eqs.map lowerEq) := by
  simp [FreeFactoring.rewrite, rewrite, lowerEq, lower_swap]

theorem lower_bindable (v : Variable) (t : Term d.sig) :
    (FreeFactoring.bindable v t).isSome = bindable v (lower t) := by
  unfold FreeFactoring.bindable bindable
  by_cases ho : t.Occurs v
  · simp only [ho, ↓reduceDIte, (lower_occurs v t).mpr ho, Option.isSome_none, Bool.not_true,
      Bool.false_and]
  · have no : (lower t).occurs v = false := by
      cases e : (lower t).occurs v
      · rfl
      · exact absurd ((lower_occurs v t).mp e) ho
    simp only [ho, ↓reduceDIte, no, lower_check, Bool.not_false, Bool.true_and]
    split <;> simp_all

theorem chain_bind {θ : Substitution d.sig} {bs : List (Variable × FTerm)}
    (hθ : ∀ u, lower (θ.image u) = chain bs u) (v : Variable) (t : Term d.sig) (h : HasSort t v.sort)
    (u : Variable) :
    lower (((Substitution.binding v t h).compose θ).image u) = chain ((v, lower t) :: bs) u := by
  simp only [Substitution.compose, Substitution.apply, chain]
  rw [lower_subst, hθ]
  congr 1
  funext w
  simp only [Substitution.binding]
  split <;> rfl

theorem bind_sim {p : Problem d.sig} (v : Variable) (t : Term d.sig) (rest kept : Problem d.sig)
    (θ : Substitution d.sig) (ok : HasSort t v.sort ∧ ¬ t.Occurs v)
    (tr : FactoredUnification.Trace p .identity (⟨.var v,t⟩ :: (rest ++ kept)) θ)
    (bs : List (Variable × FTerm)) (hθ : ∀ u, lower (θ.image u) = chain bs u) :
    Sim (FreeFactoring.bind p v t rest kept θ ok tr)
      (bind v (lower t) (rest.map lowerEq) (kept.map lowerEq) bs) where
  todo := by simp [FreeFactoring.bind, bind, ← List.map_append, lower_rewrite]
  kept := rfl
  image := chain_bind hθ v t ok.1

theorem frame_sim {p : Problem d.sig} (todo kept : Problem d.sig) (θ : Substitution d.sig)
    (tr : FactoredUnification.Trace p .identity (todo ++ kept) θ) (bs : List (Variable × FTerm))
    (hθ : ∀ u, lower (θ.image u) = chain bs u) :
    Sim (⟨todo, kept, θ, tr⟩ : FreeFactoring.Frame p) ⟨todo.map lowerEq, kept.map lowerEq, bs⟩ :=
  ⟨rfl, rfl, hθ⟩

theorem lower_beq_false {a b : Term d.sig} (h : ¬ a = b) : beq (lower a) (lower b) = false := by
  rw [lower_beq]; simp [h]

theorem lower_bindable_none {v : Variable} {t : Term d.sig} (h : FreeFactoring.bindable v t = none) :
    bindable v (lower t) = false := by
  rw [← lower_bindable, h]; rfl

theorem lower_bindable_some {v : Variable} {t : Term d.sig} {ok} (h : FreeFactoring.bindable v t = some ok) :
    bindable v (lower t) = true := by
  rw [← lower_bindable, h]; rfl

theorem settle_sim {p : Problem d.sig} (a b : Term d.sig) (rest kept : Problem d.sig)
    (θ : Substitution d.sig) (tr : FactoredUnification.Trace p .identity (⟨a,b⟩ :: (rest ++ kept)) θ)
    (bs : List (Variable × FTerm)) (hθ : ∀ u, lower (θ.image u) = chain bs u) :
    Sim (FreeFactoring.settle p a b rest kept θ tr)
      (settle (lower a) (lower b) (rest.map lowerEq) (kept.map lowerEq) bs) := by
  unfold FreeFactoring.settle settle
  by_cases same : a = b
  · subst same
    simp only [dite_true, (beq_iff _ _).mpr rfl, ↓reduceIte]
    exact ⟨rfl, rfl, hθ⟩
  · simp only [same, dite_false, lower_beq_false same, Bool.false_eq_true, ↓reduceIte]
    cases a with
    | var v =>
      simp only [lower]
      split
      next ok hv =>
        simp only [lower_bindable_some hv, ↓reduceIte]
        exact bind_sim v b rest kept θ ok.down tr bs hθ
      next hv =>
        simp only [lower_bindable_none hv, Bool.false_eq_true, ↓reduceIte]
        cases b with
        | var w =>
          simp only [lower]
          split
          next ok hw =>
            have := lower_bindable_some hw
            simp only [lower] at this
            simp only [this, ↓reduceIte]
            exact bind_sim w (.var v) rest kept θ ok.down _ bs hθ
          next hw =>
            have := lower_bindable_none hw
            simp only [lower] at this
            simp only [this, Bool.false_eq_true, ↓reduceIte]
            exact ⟨rfl, rfl, hθ⟩
        | _ => exact ⟨rfl, rfl, hθ⟩
    | atom x =>
      cases b with
      | var v =>
        simp only [lower]
        split
        next ok hv =>
          have := lower_bindable_some hv
          simp only [lower] at this
          simp only [this, ↓reduceIte]
          exact bind_sim v _ rest kept θ ok.down _ bs hθ
        next hv =>
          have := lower_bindable_none hv
          simp only [lower] at this
          simp only [this, Bool.false_eq_true, ↓reduceIte]
          exact ⟨rfl, rfl, hθ⟩
      | _ => exact ⟨rfl, rfl, hθ⟩
    | free f xs =>
      cases b with
      | var v =>
        simp only [lower]
        split
        next ok hv =>
          have := lower_bindable_some hv
          simp only [lower] at this
          simp only [this, ↓reduceIte]
          exact bind_sim v _ rest kept θ ok.down _ bs hθ
        next hv =>
          have := lower_bindable_none hv
          simp only [lower] at this
          simp only [this, Bool.false_eq_true, ↓reduceIte]
          exact ⟨rfl, rfl, hθ⟩
      | free g ys =>
        rw [lower_free, lower_free]
        by_cases eq : f = g
        · subst eq
          simp only [dite_true, beq_self_eq_true, Bool.and_self, ↓reduceIte]
          exact ⟨by simp [lower_children], rfl, hθ⟩
        · have ne : (f.val == g.val) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]
            exact fun h => eq (Subtype.ext h)
          simp only [eq, dite_false, ne, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          exact ⟨rfl, by simp [lowerEq, lower_free], hθ⟩
      | _ => exact ⟨rfl, rfl, hθ⟩
    | comm f x y =>
      cases b with
      | var v =>
        simp only [lower]
        split
        next ok hv =>
          have := lower_bindable_some hv
          simp only [lower] at this
          simp only [this, ↓reduceIte]
          exact bind_sim v _ rest kept θ ok.down _ bs hθ
        next hv =>
          have := lower_bindable_none hv
          simp only [lower] at this
          simp only [this, Bool.false_eq_true, ↓reduceIte]
          exact ⟨rfl, rfl, hθ⟩
      | _ => exact ⟨rfl, rfl, hθ⟩
    | ac f x y =>
      cases b with
      | var v =>
        simp only [lower]
        split
        next ok hv =>
          have := lower_bindable_some hv
          simp only [lower] at this
          simp only [this, ↓reduceIte]
          exact bind_sim v _ rest kept θ ok.down _ bs hθ
        next hv =>
          have := lower_bindable_none hv
          simp only [lower] at this
          simp only [this, Bool.false_eq_true, ↓reduceIte]
          exact ⟨rfl, rfl, hθ⟩
      | _ => exact ⟨rfl, rfl, hθ⟩

theorem advance_sim {p : Problem d.sig} (a b : Term d.sig) (rest kept : Problem d.sig)
    (θ : Substitution d.sig) (tr : FactoredUnification.Trace p .identity (⟨a,b⟩ :: (rest ++ kept)) θ)
    (bs : List (Variable × FTerm)) (hθ : ∀ u, lower (θ.image u) = chain bs u) :
    Sim (FreeFactoring.advance p a b rest kept θ tr)
      (advance (lower a) (lower b) (rest.map lowerEq) (kept.map lowerEq) bs) := by
  cases a <;> cases b <;> first
    | exact settle_sim _ _ rest kept θ tr bs hθ
    | skip
  next f xs g ys =>
    unfold FreeFactoring.advance advance
    rw [lower_free, lower_free]
    by_cases eq : f = g
    · subst eq
      simp only [dite_true, beq_self_eq_true, Bool.and_self, ↓reduceIte]
      exact ⟨by simp [lower_children], rfl, hθ⟩
    · have ne : (f.val == g.val) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun h => eq (Subtype.ext h)
      simp only [eq, dite_false, ne, Bool.and_self, Bool.false_eq_true, ↓reduceIte]
      exact ⟨rfl, by simp [lowerEq, lower_free], hθ⟩

theorem split_sim {p : Problem d.sig} (a b : Term d.sig) (rest kept : Problem d.sig)
    (θ : Substitution d.sig) (tr : FactoredUnification.Trace p .identity (⟨a,b⟩ :: (rest ++ kept)) θ)
    (bs : List (Variable × FTerm)) (hθ : ∀ u, lower (θ.image u) = chain bs u) :
    Sim (FreeFactoring.split p a b rest kept θ tr)
      (split (lower a) (lower b) (rest.map lowerEq) (kept.map lowerEq) bs) := by
  by_cases bothFree : ∃ f xs g ys, a = .free f xs ∧ b = .free g ys
  · obtain ⟨f, xs, g, ys, rfl, rfl⟩ := bothFree
    unfold FreeFactoring.split split
    rw [lower_free, lower_free]
    by_cases eq : f = g
    · subst eq
      simp only [dite_true, beq_self_eq_true, Bool.and_self, ↓reduceIte]
      exact ⟨by simp [lower_children], rfl, hθ⟩
    · have ne : (f.val == g.val) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun h => eq (Subtype.ext h)
      simp only [eq, dite_false, ne, Bool.and_self, Bool.false_eq_true, ↓reduceIte]
      exact ⟨rfl, by simp [lowerEq, lower_free], hθ⟩
  · have left : FreeFactoring.split p a b rest kept θ tr =
        if same : a = b then ⟨rest, kept, θ, tr.trans (.discard (same ▸ .refl _) _ _)⟩
        else ⟨rest, ⟨a,b⟩ :: kept, θ, tr.trans (.perm List.perm_middle.symm _)⟩ := by
      cases a <;> cases b <;> first | rfl | exact absurd ⟨_, _, _, _, rfl, rfl⟩ bothFree
    have right : split (lower a) (lower b) (rest.map lowerEq) (kept.map lowerEq) bs =
        if beq (lower a) (lower b) then ⟨rest.map lowerEq, kept.map lowerEq, bs⟩
        else ⟨rest.map lowerEq, (lower a, lower b) :: kept.map lowerEq, bs⟩ := by
      cases a <;> cases b <;> first | rfl | exact absurd ⟨_, _, _, _, rfl, rfl⟩ bothFree
    rw [left, right, lower_beq]
    by_cases same : a = b
    · subst same
      simp only [dite_true, decide_true, ↓reduceIte]
      exact ⟨rfl, rfl, hθ⟩
    · simp only [same, dite_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ⟨rfl, rfl, hθ⟩

theorem go_sim {p : Problem d.sig} (n : Nat) : ∀ (st : FreeFactoring.Frame p) (fs : FFrame),
    Sim st fs → Sim (FreeFactoring.go p n st) (go n fs) := by
  induction n with
  | zero => intro st fs h; exact h
  | succ n ih =>
    rintro ⟨todo, kept, θ, tr⟩ ⟨ftodo, fkept, bs⟩ ⟨h1, h2, h3⟩
    simp only at h1 h2 h3
    subst h1 h2
    cases todo with
    | nil => exact ⟨rfl, rfl, h3⟩
    | cons e rest =>
      obtain ⟨a, b⟩ := e
      exact ih _ _ (advance_sim a b rest kept θ tr bs h3)

theorem spread_sim {p : Problem d.sig} (n : Nat) : ∀ (st : FreeFactoring.Frame p) (fs : FFrame),
    Sim st fs → Sim (FreeFactoring.spread p n st) (spread n fs) := by
  induction n with
  | zero => intro st fs h; exact h
  | succ n ih =>
    rintro ⟨todo, kept, θ, tr⟩ ⟨ftodo, fkept, bs⟩ ⟨h1, h2, h3⟩
    simp only at h1 h2 h3
    subst h1 h2
    cases todo with
    | nil => exact ⟨rfl, rfl, h3⟩
    | cons e rest =>
      obtain ⟨a, b⟩ := e
      exact ih _ _ (split_sim a b rest kept θ tr bs h3)

theorem fuel_lower (p : Problem d.sig) : fuel (p.map lowerEq) = FreeFactoring.fuel p := by
  simp [fuel, FreeFactoring.fuel, lowerEq, lower_weight, Function.comp_def]

theorem factor_sim (p : Problem d.sig) : Sim (FreeFactoring.factor p) (factor (p.map lowerEq)) := by
  unfold FreeFactoring.factor factor
  simp only [fuel_lower]
  have start : Sim (⟨p, [], .identity, by rw [List.append_nil]; exact .done _ _⟩ : FreeFactoring.Frame p)
      ⟨p.map lowerEq, [], []⟩ := ⟨rfl, rfl, fun _ => rfl⟩
  have spreaded := spread_sim (FreeFactoring.fuel p) _ _ start
  apply go_sim
  exact ⟨by simp [FreeFactoring.restart, spreaded.todo, spreaded.kept], rfl, spreaded.image⟩

end Simulation


/-! ### Images and the reply -/

/-- The image of a variable in a table of bindings. -/
def lookupD : List (Variable × FTerm) → Variable → FTerm
  | [], v => .var v
  | (w, t) :: rest, v => if varEq v w then t else lookupD rest v

/-- One pass over the bindings, the latest first: every entry gets the image
of its term under the entries of the later bindings. -/
def resolveBinds (bs : List (Variable × FTerm)) : List (Variable × FTerm) :=
  bs.foldl (fun table b => (b.1, FTerm.subst (lookupD table) b.2) :: table) []

theorem lookupD_foldl (L : List (Variable × FTerm)) (tab : List (Variable × FTerm)) (u : Variable) :
    lookupD (L.foldl (fun table b => (b.1, FTerm.subst (lookupD table) b.2) :: table) tab) u =
      FTerm.subst (lookupD tab) (chain L u) := by
  induction L generalizing tab with
  | nil => rfl
  | cons b L ih =>
    obtain ⟨w, t⟩ := b
    simp only [List.foldl_cons, chain]
    rw [ih, FTerm.subst_subst]
    congr 1
    funext x
    by_cases h : x = w <;> simp [lookupD, h, FTerm.subst]

theorem lookupD_resolve (bs : List (Variable × FTerm)) (u : Variable) :
    lookupD (resolveBinds bs) u = chain bs u := by
  rw [resolveBinds, lookupD_foldl]
  have : lookupD [] = FTerm.var := rfl
  rw [this, FTerm.subst_var]

/-- The binding row of a variable, read from the table. -/
def row (table : List (Variable × FTerm)) (v : Variable) : Option (Array UInt64) := do
  let id ← WordEncoding.pack v.id
  (lookupD table v).emit #[id, sortCode v.sort]

section Reply
variable {d : Dictionary}

theorem row_binding (σ : Substitution d.sig) (table : List (Variable × FTerm))
    (same : ∀ v, lower (σ.image v) = lookupD table v) (v : Variable) :
    row table v = binding σ v := by
  unfold row binding
  simp only [← same, lower_emit]
  cases WordEncoding.pack v.id with
  | none => rfl
  | some id =>
    cases write (σ.image v) with
    | none => rfl
    | some c => simp [tokenWords]

/-- The variables of a lowered problem, in the order of `Problem.variables`. -/
def problemVars (eqs : List FEq) : List Variable :=
  eqs.flatMap fun e => e.1.vars ++ e.2.vars

theorem problemVars_lower (p : Problem d.sig) : problemVars (p.map lowerEq) = p.variables := by
  unfold problemVars Problem.variables
  rw [List.flatMap_map]
  congr 1
  funext e
  simp [lowerEq, lower_vars]

mutual
/-- The variables of a term in front of an accumulator. -/
def varsInto : FTerm → List Variable → List Variable
  | .var v, acc => v :: acc
  | .atom .., acc => acc
  | .app _ _ _ _ args, acc => varsAllInto args acc
def varsAllInto : List FTerm → List Variable → List Variable
  | [], acc => acc
  | t :: ts, acc => varsInto t (varsAllInto ts acc)
end

mutual
theorem varsInto_eq : ∀ (t : FTerm) (acc : List Variable), varsInto t acc = t.vars ++ acc
  | .var _, _ => rfl
  | .atom .., _ => rfl
  | .app _ _ _ _ args, acc => by simp only [varsInto, FTerm.vars, varsAllInto_eq args acc]
theorem varsAllInto_eq : ∀ (ts : List FTerm) (acc : List Variable), varsAllInto ts acc = FTerm.varsAll ts ++ acc
  | [], _ => rfl
  | t :: ts, acc => by simp only [varsAllInto, FTerm.varsAll, varsInto_eq t, varsAllInto_eq ts, List.append_assoc]
end

/-- `List.eraseDups` comparing variables field by field. -/
def dedupVars : List Variable → List Variable → List Variable
  | [], seen => seen.reverse
  | v :: vs, seen => if seen.any (varEq v) then dedupVars vs seen else dedupVars vs (v :: seen)

theorem dedupVars_eq (l seen : List Variable) :
    dedupVars l seen = List.eraseDupsBy.loop (· == ·) l seen := by
  induction l generalizing seen with
  | nil => rfl
  | cons v vs ih =>
    have : seen.any (varEq v) = seen.any (fun b => v == b) := by
      congr 1; funext b; exact varEq_eq v b
    cases h : seen.any (fun b => v == b) <;> simp [dedupVars, List.eraseDupsBy.loop, this, h, ih]

/-- The variables of the lowered query without repeats, in order. -/
def keysOf (eqs : List FEq) : List Variable :=
  dedupVars (eqs.foldr (fun e acc => varsInto e.1 (varsInto e.2 acc)) []) []

theorem keysOf_eq (eqs : List FEq) : keysOf eqs = (problemVars eqs).eraseDups := by
  have vars : eqs.foldr (fun e acc => varsInto e.1 (varsInto e.2 acc)) [] = problemVars eqs := by
    induction eqs with
    | nil => rfl
    | cons e es ih =>
      rw [List.foldr_cons, ih, varsInto_eq, varsInto_eq]
      simp [problemVars]
  rw [keysOf, vars, dedupVars_eq]
  rfl

/-- The decline test at the head of `TotalUnifyWire.family`. -/
def declines (p : Problem d.sig) : Bool :=
  (p.all fun e => sumLike e.lhs && sumLike e.rhs) &&
      (p.any fun e => wideProduct ≤ spine wideProduct e.lhs || wideProduct ≤ spine wideProduct e.rhs) &&
      32 ≤ p.variables.length &&
      UnifyExists.fast UnifyExists.depth p == some false

variable [Interrupt]

theorem family_solved (p : Problem d.sig) (kept : declines p = false)
    (quick : p.any NarrowingClash.quick = false)
    (todo : (FreeFactoring.factor p).todo = []) (left : (FreeFactoring.factor p).kept = []) :
    ∃ σ : Substitution d.sig, family p = [σ.compose (FreeFactoring.factor p).θ] ∧
      ∀ v, σ.image v = .var v := by
  obtain ⟨σ, hσ, img⟩ := MixedUnification.forcing_empty (s := d.sig) (p.variables ++ [])
  refine ⟨σ, ?_, img⟩
  unfold declines at kept
  unfold family
  simp only [kept, Bool.false_eq_true, ↓reduceIte]
  rw [MixedUnification.verified_solve (s := d.sig)]
  simp only [quick, Bool.false_eq_true, ↓reduceIte]
  rw [FreeFactoring.solve_eq (s := d.sig), todo, left, List.append_nil, hσ]
  rfl

/-- `NarrowingClash.impossible`. -/
def impossible (e : FEq) : Bool :=
  !(FTerm.heads e.1 e.2) || (e.1.check e.1.rootSort && !(e.2.possible e.1.rootSort)) ||
    (e.2.check e.2.rootSort && !(e.1.possible e.2.rootSort))

omit [Interrupt] in
theorem possibleAll_ofFn {n : Nat} (g : Fin n → FTerm) (h : Fin n → SortId) :
    possibleAll (List.ofFn g) (List.ofFn h) = (List.finRange n).all fun i => possible (g i) (h i) := by
  induction n with
  | zero => simp [possibleAll]
  | succ n ih =>
    simp only [List.ofFn_succ, possibleAll, List.finRange_succ, List.all_cons, List.all_map,
      Function.comp_def]
    rw [ih]

omit [Interrupt] in
theorem lower_possible (t : Term d.sig) (k : SortId) :
    (lower t).possible k = NarrowingClash.possible t k := by
  induction t generalizing k with
  | var w => simp [lower, possible, NarrowingClash.possible]
  | atom a => simp [lower, possible, NarrowingClash.possible]
  | free f xs ih =>
    rw [lower_free]
    simp only [possible, NarrowingClash.possible, possibleAll_ofFn, ih]
  | comm f a b ia ib | ac f a b ia ib =>
    simp [lower, possible, possibleAll, NarrowingClash.possible, ia, ib, Bool.and_assoc]

omit [Interrupt] in
theorem lower_rootSort (t : Term d.sig) : (lower t).rootSort = t.rootSort := by
  cases t <;> rfl

omit [Interrupt] in
private theorem beq_decide {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (a b : α) :
    (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

omit [Interrupt] in
theorem lower_heads (a b : Term d.sig) : FTerm.heads (lower a) (lower b) = NarrowingClash.heads a b := by
  cases a <;> cases b <;>
    simp [lower, FTerm.heads, NarrowingClash.heads, Subtype.ext_iff, Prod.ext_iff, beq_decide]

omit [Interrupt] in
theorem lower_impossible (e : Equation d.sig) : impossible (lowerEq e) = NarrowingClash.impossible e := by
  simp [impossible, lowerEq, NarrowingClash.impossible, NarrowingClash.sortClash, lower_heads,
    lower_check, lower_rootSort, lower_possible]

omit [Interrupt] in
theorem lower_product (t : Term d.sig) : (lower t).product = (ForcedOperands.headOf t).isSome := by
  cases t <;> rfl

omit [Interrupt] in
theorem lower_leaves (t : Term d.sig) : (lower t).leaves = ForcedOperands.leaves t := by
  induction t with
  | ac f a b ia ib => simp [lower, FTerm.leaves, ForcedOperands.leaves, ia, ib]
  | comm f a b => simp [lower, FTerm.leaves, ForcedOperands.leaves]
  | free f xs =>
    rw [lower_free]
    simp only [ForcedOperands.leaves]
    unfold FTerm.leaves
    split
    · next h => simp only [FTerm.app.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
    · rfl
  | var | atom => rfl

omit [Interrupt] in
theorem added_none (r : Problem d.sig)
    (flat : r.all (fun e => !(lower e.lhs).product && !(lower e.rhs).product)) :
    (ForcedOperands.added r).val = [] := by
  have empty : ForcedOperands.heads r = [] := by
    unfold ForcedOperands.heads
    have nil : (r.flatMap fun e => (ForcedOperands.headOf e.lhs).toList ++
        (ForcedOperands.headOf e.rhs).toList) = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro e he
      have := List.all_eq_true.mp flat e he
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, lower_product] at this
      cases h1 : ForcedOperands.headOf e.lhs <;> cases h2 : ForcedOperands.headOf e.rhs <;> simp_all
    rw [nil]
    rfl
  unfold ForcedOperands.added
  split
  · rfl
  · simp [empty]

theorem family_clash (p : Problem d.sig) (kept : declines p = false)
    (quick : p.any NarrowingClash.quick = false)
    (clash : ((FreeFactoring.factor p).todo ++ (FreeFactoring.factor p).kept).any
      NarrowingClash.impossible)
    (flat : (ForcedOperands.added ((FreeFactoring.factor p).todo ++ (FreeFactoring.factor p).kept)).val = []) :
    family p = [] := by
  unfold declines at kept
  unfold family
  simp only [kept, Bool.false_eq_true, ↓reduceIte]
  rw [MixedUnification.verified_solve (s := d.sig)]
  simp only [quick, Bool.false_eq_true, ↓reduceIte]
  rw [FreeFactoring.solve_eq (s := d.sig)]
  simp only [MixedUnification.rounds, MixedUnification.forcing, ForcedOperands.unifier,
    flat, List.isEmpty_nil, ↓reduceIte, MixedUnification.residual,
    NarrowingClash.unifier, clash, List.map_nil]
  rfl

/-- The reply for a query on which neither the decline test nor the root test
fires, from free factoring on its lowered equations: the images of the query
variables when no equation is left, the empty family when the residual has an
impossible equation and too few product operands to force any, and `slow ()`
otherwise. -/
def solved (eqs : List FEq) (slow : Unit → Array (Array UInt64)) : Array (Array UInt64) :=
  let st := factor eqs
  if st.todo.isEmpty && st.kept.isEmpty then
    let table := resolveBinds st.binds
    match (keysOf eqs).mapM (row table) with
    | some rows => (#[1] :: #[] :: rows).toArray
    | none => slow ()
  else if (st.todo ++ st.kept).any impossible &&
      ((st.todo ++ st.kept).all (fun e => !e.1.product && !e.2.product) ||
        ((st.todo ++ st.kept).map fun e => e.1.leaves + e.2.leaves).sum < ForcedOperands.floor) then
    #[#[1]]
  else slow ()

omit [Interrupt] in
theorem pack_single (p : Problem d.sig) (σ : Substitution d.sig) :
    pack p [σ] = (p.variables.eraseDups.mapM (binding σ)).map fun rows => (#[1] :: #[] :: rows).toArray := by
  unfold pack arm
  cases h : p.variables.eraseDups.mapM (binding σ) <;> simp [h]

theorem solved_eq (p : Problem d.sig) (hd : declines p = false)
    (hq : p.any NarrowingClash.quick = false) (slow : Unit → Array (Array UInt64))
    (hs : slow () = (pack p (family p)).getD #[#[0]]) :
    solved (p.map lowerEq) slow = (pack p (family p)).getD #[#[0]] := by
  unfold solved
  · have sim := factor_sim p
    dsimp only
    split
    · next done =>
      have todo : (FreeFactoring.factor p).todo = [] := by
        have := sim.todo
        simp only [Bool.and_eq_true, List.isEmpty_iff] at done
        rw [done.1] at this
        exact List.map_eq_nil_iff.mp this.symm
      have left : (FreeFactoring.factor p).kept = [] := by
        have := sim.kept
        simp only [Bool.and_eq_true, List.isEmpty_iff] at done
        rw [done.2] at this
        exact List.map_eq_nil_iff.mp this.symm
      obtain ⟨σ, hfam, img⟩ := family_solved p hd hq todo left
      have id : σ.image = Term.var := funext img
      have same : ∀ v, lower ((σ.compose (FreeFactoring.factor p).θ).image v) =
          lookupD (resolveBinds (factor (p.map lowerEq)).binds) v := by
        intro v
        rw [lookupD_resolve, ← sim.image]
        simp [Substitution.compose, Substitution.apply, id]
      have rows : (keysOf (p.map lowerEq)).mapM
          (row (resolveBinds (factor (p.map lowerEq)).binds)) =
          p.variables.eraseDups.mapM (binding (σ.compose (FreeFactoring.factor p).θ)) := by
        rw [keysOf_eq, problemVars_lower]
        congr 1
        funext v
        exact row_binding _ _ same v
      rw [hs, hfam, pack_single, rows]
      split <;> simp_all
    · split
      · next clash =>
        have residual : (factor (p.map lowerEq)).todo ++ (factor (p.map lowerEq)).kept =
            ((FreeFactoring.factor p).todo ++ (FreeFactoring.factor p).kept).map lowerEq := by
          rw [sim.todo, sim.kept, List.map_append]
        rw [residual, Bool.and_eq_true, List.any_map, List.all_map] at clash
        have imp : ((FreeFactoring.factor p).todo ++ (FreeFactoring.factor p).kept).any
            NarrowingClash.impossible := by
          have := clash.1
          simp only [Function.comp_def, lower_impossible] at this
          exact this
        have flat : (ForcedOperands.added ((FreeFactoring.factor p).todo ++
            (FreeFactoring.factor p).kept)).val = [] := by
          rcases Bool.or_eq_true_iff.mp clash.2 with none | small
          · apply added_none
            simp only [Function.comp_def, lowerEq] at none
            exact none
          · apply ForcedOperands.added_small
            simp only [List.map_map, Function.comp_def, lowerEq, lower_leaves, decide_eq_true_eq] at small
            exact small
        rw [family_clash p hd hq imp flat]
        rfl
      · exact hs

end Reply

/-! ### Decoding straight to lowered terms -/

/-- `ACRepresentation.fold` on lowered terms. -/
def foldAC (id : UInt64) (o : SortId) (a : FTerm) : List FTerm → FTerm
  | [] => a
  | b :: bs => .app 4 id o [o, o] [a, foldAC id o b bs]

/-- `TotalUnifyWire.app` on lowered children. -/
def decodeApp (ds : List Whole.Decl) (k id : UInt64) (children : List FTerm) : Option FTerm :=
  match decl ds k id with
  | none => none
  | some dl =>
    if k == 2 then
      if children.length = dl.inputs.length then
        some (.app 2 id (sortOf dl.output) (dl.inputs.map sortOf) children)
      else none
    else if k == 3 then
      match children with
      | [l, r] => let o := sortOf dl.output; some (.app 3 id o [o, o] [l, r])
      | _ => none
    else if k == 4 then
      match children with
      | l :: r :: rs => let o := sortOf dl.output; some (.app 4 id o [o, o] [l, foldAC id o r rs])
      | _ => none
    else none

/-- `TotalUnifyWire.leaf`, an atom being declared by its own row. -/
def decodeLeaf (k id arg : UInt64) : Option FTerm :=
  if arg ≤ 4 then
    if k == 0 then some (.var ⟨id.toNat, sortOf arg⟩)
    else if k == 1 then some (.atom id (sortOf arg))
    else none
  else none

/-- `TotalUnifyWire.node` on lowered terms. -/
def decodeNode (ds : List Whole.Decl) (prior : Array FTerm) (row : Array UInt64) : Option FTerm :=
  match row.toList with
  | k :: id :: tail =>
    if k ≤ 1 then
      match tail with
      | [arg] => decodeLeaf k id arg
      | _ => none
    else do decodeApp ds k id (← tail.mapM fun (i : UInt64) => prior[i.toNat]?)
  | _ => none

/-- `TotalUnifyWire.equations` on lowered terms. -/
def decodeEquations (ts : Array FTerm) : List UInt64 → Option (List FEq)
  | [] => some []
  | i :: j :: rest => do return (← ts[i.toNat]?, ← ts[j.toNat]?) :: (← decodeEquations ts rest)
  | [_] => none

/-- `TotalUnifyWire.input`, lowered. -/
def decode (decls : Array UInt64) (nodes : Array (Array UInt64)) (roots : Array UInt64) :
    Option (List FEq) := do
  let ds ← Whole.declarations decls.toList
  let ts ← nodes.foldlM (fun acc r => do return acc.push (← decodeNode ds acc r)) #[]
  decodeEquations ts roots.toList

section DecodeProof
variable {d : Dictionary}

theorem lower_fold (f : d.sig.ACSym) (a : Term d.sig) (bs : List (Term d.sig)) :
    lower (ACRepresentation.fold f a bs) = foldAC f.val (sortOf (info f).output) (lower a) (bs.map lower) := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih => simp [ACRepresentation.fold, foldAC, lower, ih]

theorem resolve_some {k id : UInt64} (h : (decl d.decls k id).isSome) :
    resolve d.decls k id = some ⟨id, h⟩ := by
  simp [resolve, h]

theorem info_eq {k id : UInt64} {dl : Whole.Decl} (found : decl d.decls k id = some dl)
    (h : (decl d.decls k id).isSome) : info (⟨id, h⟩ : Symbol d.decls k) = dl := by
  simp [info, found]

theorem decodeApp_sound (k id : UInt64) (cs : List (Term d.sig)) (ft : FTerm)
    (h : decodeApp d.decls k id (cs.map lower) = some ft) :
    ∃ t, TotalUnifyWire.app d k id cs = some t ∧ lower t = ft := by
  unfold decodeApp at h
  split at h
  · cases h
  · next dl found =>
    have hs : (decl d.decls k id).isSome := by simp [found]
    have hi := info_eq found hs
    unfold TotalUnifyWire.app
    by_cases k2 : (k == 2) = true
    · have kk : k = 2 := by simpa using k2
      subst kk
      simp only [k2, ↓reduceIte, List.length_map] at h ⊢
      split at h
      · next len =>
        cases h
        rw [resolve_some hs]
        let f : d.sig.FreeSym := ⟨id, hs⟩
        have arity : d.sig.arity f = dl.inputs.length := by
          show (info f).inputs.length = _
          rw [hi]
        have fits : cs.length = d.sig.arity f := by rw [arity, len]
        refine ⟨.free f fun i => cs.get (Fin.cast fits.symm i), ?_, ?_⟩
        · simp only [Option.bind_eq_bind, Option.bind_some]
          split
          · rfl
          · next no => exact absurd fits no
        · rw [lower_free]
          have out : d.sig.outputSort f = sortOf dl.output := by
            show sortOf (info f).output = _
            rw [hi]
          have ofFnGet (l : List UInt64) :
              (List.ofFn fun i : Fin l.length => sortOf (l.get i)) = l.map sortOf := by
            apply List.ext_getElem <;> simp
          have ins : List.ofFn (d.sig.inputSort f) = dl.inputs.map sortOf := by
            show (List.ofFn fun i : Fin (info f).inputs.length => sortOf ((info f).inputs.get i)) = _
            rw [ofFnGet, hi]
          have args : (List.ofFn fun i => lower (cs.get (Fin.cast fits.symm i))) = cs.map lower := by
            apply List.ext_getElem <;> simp [fits]
          rw [out, ins, args]
      · cases h
    · by_cases k3 : (k == 3) = true
      · have kk : k = 3 := by simpa using k3
        subst kk
        simp only [k3, ↓reduceIte] at h ⊢
        rw [resolve_some hs]
        match cs, h with
        | [a, b], h =>
          cases h
          refine ⟨.comm ⟨id, hs⟩ a b, rfl, ?_⟩
          simp [lower, hi]
      · by_cases k4 : (k == 4) = true
        · have kk : k = 4 := by simpa using k4
          subst kk
          simp only [k4, ↓reduceIte] at h ⊢
          rw [resolve_some hs]
          match cs, h with
          | a :: b :: rest, h =>
            cases h
            refine ⟨.ac ⟨id, hs⟩ a (ACRepresentation.fold ⟨id, hs⟩ b rest), rfl, ?_⟩
            simp [lower, hi, lower_fold]
        · simp [k2, k3, k4] at h

theorem decodeLeaf_sound (k id arg : UInt64) (ft : FTerm)
    (member : k = 1 → (id, sortOf arg) ∈ d.atoms)
    (h : decodeLeaf k id arg = some ft) : ∃ t, leaf d k id arg = some t ∧ lower t = ft := by
  unfold decodeLeaf at h
  unfold leaf
  by_cases small : arg ≤ 4
  · simp only [small, ↓reduceIte] at h
    by_cases k0 : (k == 0) = true
    · simp only [k0, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨.var ⟨id.toNat, sortOf arg⟩, by simp [small, k0, guard], rfl⟩
    · by_cases k1 : (k == 1) = true
      · simp only [k0, k1, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h
        have mem := member (by simpa using k1)
        refine ⟨.atom ⟨(id, sortOf arg), mem⟩, ?_, rfl⟩
        simp [small, k0, k1, guard, TotalUnifyWire.atom, mem]
      · simp [k0, k1] at h
  · simp [small] at h

theorem mapM_lower (prior : Array (Term d.sig)) (is : List UInt64) :
    is.mapM (fun (i : UInt64) => (prior.map lower)[i.toNat]?) =
      (is.mapM fun (i : UInt64) => prior[i.toNat]?).map (List.map lower) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    rw [List.mapM_cons, List.mapM_cons, ih]
    simp only [Array.getElem?_map]
    cases prior[i.toNat]? <;> cases is.mapM (fun (i : UInt64) => prior[i.toNat]?) <;> rfl

theorem decodeNode_sound (prior : Array (Term d.sig)) (row : Array UInt64) (ft : FTerm)
    (member : ∀ id arg, row.toList = [1, id, arg] → (id, sortOf arg) ∈ d.atoms)
    (h : decodeNode d.decls (prior.map lower) row = some ft) :
    ∃ t, node d prior row = some t ∧ lower t = ft := by
  unfold decodeNode at h
  unfold node
  split at h
  · next k id tail list =>
    simp only [list]
    by_cases leafy : k ≤ 1
    · simp only [leafy, ↓reduceIte] at h ⊢
      split at h
      · next arg =>
        apply decodeLeaf_sound k id arg ft _ h
        intro k1
        subst k1
        exact member id arg list
      · cases h
    · simp only [leafy, ↓reduceIte, Option.bind_eq_bind] at h ⊢
      rw [mapM_lower] at h
      cases hcs : tail.mapM (fun (i : UInt64) => prior[i.toNat]?) with
      | none => simp [hcs] at h
      | some cs =>
        simp only [hcs, Option.map_some, Option.bind_some] at h
        obtain ⟨t, ht, lt⟩ := decodeApp_sound k id cs ft h
        exact ⟨t, by simp [ht], lt⟩
  · cases h

theorem decodeEquations_sound (ts : Array (Term d.sig)) : ∀ (roots : List UInt64) (eqs : List FEq),
    decodeEquations (ts.map lower) roots = some eqs → ∃ p, equations ts roots = some p ∧ p.map lowerEq = eqs
  | [], eqs, h => by simp [decodeEquations] at h; subst h; exact ⟨[], rfl, rfl⟩
  | [_], eqs, h => by simp [decodeEquations] at h
  | i :: j :: rest, eqs, h => by
    simp only [decodeEquations, Array.getElem?_map, bind_pure_comp, Option.bind_eq_bind] at h
    cases hi : ts[i.toNat]? with
    | none => simp [hi] at h
    | some a =>
      cases hj : ts[j.toNat]? with
      | none => simp [hi, hj] at h
      | some b =>
        cases hr : decodeEquations (ts.map lower) rest with
        | none => simp [hi, hj, hr] at h
        | some more =>
          simp [hi, hj, hr] at h
          subst h
          obtain ⟨p, hp, eq⟩ := decodeEquations_sound ts rest more hr
          exact ⟨⟨a, b⟩ :: p, by simp [equations, hi, hj, hp], by simp [eq, lowerEq]⟩

theorem fold_sound (L : List (Array UInt64))
    (member : ∀ row ∈ L, ∀ id arg, row.toList = [1, id, arg] → (id, sortOf arg) ∈ d.atoms) :
    ∀ (acc : Array (Term d.sig)) (fts : Array FTerm),
      L.foldlM (fun acc r => do return acc.push (← decodeNode d.decls acc r)) (acc.map lower) = some fts →
      ∃ ts, L.foldlM (fun acc r => do return acc.push (← node d acc r)) acc = some ts ∧ ts.map lower = fts := by
  induction L with
  | nil => intro acc fts h; simp at h; subst h; exact ⟨acc, rfl, rfl⟩
  | cons r rest ih =>
    intro acc fts h
    cases hn : decodeNode d.decls (acc.map lower) r with
    | none => simp [hn] at h
    | some ft =>
      obtain ⟨t, ht, lt⟩ := decodeNode_sound acc r ft (member r List.mem_cons_self) hn
      have push : (acc.map lower).push ft = (acc.push t).map lower := by simp [lt]
      have h' : rest.foldlM (fun acc r => do return acc.push (← decodeNode d.decls acc r))
          ((acc.push t).map lower) = some fts := by
        rw [← push]
        simpa [hn] using h
      obtain ⟨ts, hts, eq⟩ := ih (fun row hr => member row (List.mem_cons_of_mem _ hr)) (acc.push t) fts h'
      exact ⟨ts, by simpa [ht] using hts, eq⟩

theorem decode_sound (decls : Array UInt64) (nodes : Array (Array UInt64)) (roots : Array UInt64)
    (eqs : List FEq) (h : decode decls nodes roots = some eqs) :
    ∃ d p, input decls nodes roots = some ⟨d, p⟩ ∧ p.map lowerEq = eqs := by
  unfold decode at h
  cases hds : Whole.declarations decls.toList with
  | none => simp [hds] at h
  | some ds =>
    simp only [hds, Option.bind_some, Option.bind_eq_bind] at h
    let d : Dictionary := ⟨ds, (nodes.toList.filterMap fun row => match row.toList with
      | [1,id,s] => some (id,sortOf s)
      | _ => none).eraseDups⟩
    have member : ∀ row ∈ nodes.toList, ∀ id arg, row.toList = [1, id, arg] → (id, sortOf arg) ∈ d.atoms := by
      intro row hrow id arg hlist
      apply List.mem_eraseDups.mpr
      apply List.mem_filterMap.mpr
      exact ⟨row, hrow, by simp [hlist]⟩
    cases hf : nodes.foldlM (fun acc r => do return acc.push (← decodeNode ds acc r)) #[] with
    | none =>
      simp only [Option.bind_eq_bind] at hf
      rw [hf] at h
      cases h
    | some fts =>
      have hf' := hf
      simp only [Option.bind_eq_bind] at hf'
      rw [hf'] at h
      simp only [Option.bind_some] at h
      rw [← Array.foldlM_toList] at hf
      have hf2 : List.foldlM (fun acc r => do return acc.push (← decodeNode d.decls acc r))
          ((#[] : Array (Term d.sig)).map lower) nodes.toList = some fts := by
        rw [Array.map_empty]
        exact hf
      obtain ⟨ts, hts, eq⟩ := fold_sound (d := d) nodes.toList member #[] fts hf2
      rw [Array.foldlM_toList] at hts
      subst eq
      obtain ⟨p, hp, peq⟩ := decodeEquations_sound ts roots.toList eqs h
      refine ⟨d, p, ?_, peq⟩
      have hg : graph decls nodes = some ⟨d, ts⟩ := by
        have h2 : (Array.foldlM (fun acc r => do return acc.push (← node d acc r)) #[] nodes).bind
            (fun ts => (some ⟨d, ts⟩ : Option ((d : Dictionary) × Array (Term d.sig)))) = some ⟨d, ts⟩ := by
          rw [hts]; rfl
        unfold graph
        rw [hds]
        exact h2
      simp only [input, Option.bind_eq_bind, hg, Option.bind_some, hp]
      rfl

end DecodeProof

/-- `TotalUnifyWire.run` with its own body, for the fallback of `runFast`. -/
def runSlow [Interrupt] (decls : Array UInt64) (nodes : Array (Array UInt64)) (roots : Array UInt64) :
    Array (Array UInt64) :=
  (do
    let ⟨_,p⟩ ← input decls nodes roots
    pack p (family p)).getD #[#[0]]


/-! ### The tests at the head of `family`, on lowered terms -/

/-- `TotalUnifyWire.sumLike`. -/
def sumLikeF : FTerm → Bool
  | .var _ => true
  | .app k .. => k == 4
  | _ => false

/-- `TotalUnifyWire.spine`. -/
def spineF : Nat → FTerm → Nat
  | 0, _ => 0
  | n + 1, .app k _ _ _ [_, r] => if k == 4 then 1 + spineF n r else 1
  | _ + 1, _ => 1

/-- The first three conjuncts of `declines`, which decide it when false. -/
def declinesPre (eqs : List FEq) : Bool :=
  (eqs.all fun e => sumLikeF e.1 && sumLikeF e.2) &&
    (eqs.any fun e => wideProduct ≤ spineF wideProduct e.1 || wideProduct ≤ spineF wideProduct e.2) &&
    32 ≤ (problemVars eqs).length

/-- `NarrowingClash.rootPossible`. -/
def rootPossibleF : FTerm → SortId → Bool
  | .var v, k => Subsort.check v.sort k || Subsort.check k v.sort
  | .atom _ s, k => Subsort.check s k
  | .app _ _ o _ _, k => Subsort.check o k

/-- `NarrowingClash.shallow`. -/
def shallowF : FTerm → FTerm → Bool
  | .var v, b => !(rootPossibleF b v.sort)
  | _, _ => false

/-- `NarrowingClash.quick`. -/
def quickF (e : FEq) : Bool := !(FTerm.heads e.1 e.2) || shallowF e.1 e.2 || shallowF e.2 e.1

section Tests
variable {d : Dictionary}

theorem lower_sumLike (t : Term d.sig) : sumLikeF (lower t) = sumLike t := by
  cases t <;> rfl

theorem spineF_free (n : Nat) (id : UInt64) (o : SortId) (ins : List SortId) (args : List FTerm) :
    spineF (n + 1) (.app 2 id o ins args) = 1 := by
  match args with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: _ => rfl

theorem lower_spine (n : Nat) (t : Term d.sig) : spineF n (lower t) = spine n t := by
  induction n generalizing t with
  | zero => cases t <;> rfl
  | succ n ih =>
    cases t with
    | ac f a b => simp [lower, spineF, spine, ih]
    | comm f a b => simp [lower, spineF, spine]
    | free f xs =>
      rw [lower_free, spineF_free]
      rfl
    | var | atom => rfl

theorem lower_rootPossible (t : Term d.sig) (k : SortId) :
    rootPossibleF (lower t) k = NarrowingClash.rootPossible t k := by
  cases t <;> rfl

theorem lower_shallow (a b : Term d.sig) : shallowF (lower a) (lower b) = NarrowingClash.shallow a b := by
  cases a <;> simp [lower, shallowF, NarrowingClash.shallow, lower_rootPossible]

theorem lower_quick (e : Equation d.sig) : quickF (lowerEq e) = NarrowingClash.quick e := by
  simp [quickF, lowerEq, NarrowingClash.quick, lower_heads, lower_shallow]

theorem declinesPre_false {p : Problem d.sig} (h : declinesPre (p.map lowerEq) = false) :
    declines p = false := by
  unfold declinesPre at h
  unfold declines
  simp only [List.all_map, List.any_map, Function.comp_def, lowerEq, lower_sumLike, lower_spine,
    problemVars_lower] at h
  simp [h]

variable [Interrupt]

theorem family_quick (p : Problem d.sig) (kept : declines p = false)
    (quick : p.any NarrowingClash.quick = true) : family p = [] := by
  unfold declines at kept
  unfold family
  simp only [kept, Bool.false_eq_true, ↓reduceIte]
  rw [MixedUnification.verified_solve (s := d.sig)]
  simp [quick]

end Tests

/-- The reply to a query decoded straight to lowered terms; `slow ()` is the
reply of `TotalUnifyWire.run`, for the queries that are left to it. -/
def replyF (eqs : List FEq) (slow : Unit → Array (Array UInt64)) : Array (Array UInt64) :=
  if declinesPre eqs then slow ()
  else if eqs.any quickF then #[#[1]]
  else solved eqs slow

theorem replyF_eq [Interrupt] {d : Dictionary} (p : Problem d.sig) (slow : Unit → Array (Array UInt64))
    (hs : slow () = (pack p (family p)).getD #[#[0]]) :
    replyF (p.map lowerEq) slow = (pack p (family p)).getD #[#[0]] := by
  unfold replyF
  split
  · exact hs
  · next pre =>
    have hd := declinesPre_false (Bool.eq_false_iff.mpr pre)
    split
    · next q =>
      have hq : p.any NarrowingClash.quick = true := by
        rw [List.any_map] at q
        simpa [Function.comp_def, lower_quick] using q
      rw [family_quick p hd hq]
      rfl
    · next q =>
      have hq : p.any NarrowingClash.quick = false := by
        rw [List.any_map] at q
        simpa [Function.comp_def, lower_quick] using q
      exact solved_eq p hd hq slow hs

/-- `TotalUnifyWire.run`, decoding straight to lowered terms. -/
def runFast [Interrupt] (decls : Array UInt64) (nodes : Array (Array UInt64)) (roots : Array UInt64) :
    Array (Array UInt64) :=
  match decode decls nodes roots with
  | none => runSlow decls nodes roots
  | some eqs => replyF eqs fun _ => runSlow decls nodes roots

@[csimp] theorem run_eq_fast : @run = @runFast := by
  funext i decls nodes roots
  unfold runFast
  split
  · rfl
  · next eqs found =>
    obtain ⟨d, p, hin, rfl⟩ := decode_sound decls nodes roots eqs found
    have slow : runSlow decls nodes roots = (pack p (family p)).getD #[#[0]] := by
      simp [runSlow, hin]
    rw [replyF_eq p _ slow]
    simp [run, hin]

end Tamarin.TotalUnifyFast
