import Tamarin.FactoredUnification
import Tamarin.TermEquality
import Tamarin.SortCheck
import Tamarin.VariablesFast
import Tamarin.Buckets

/-! Free factoring before the component search. The worklist eliminates
variable bindings, decomposes equal free heads and drops identical sides.
Every step is one constructor of `FactoredUnification.Trace`, so stopping at
any point leaves a residual whose complete answers lift to the input. The
fuel bounds work only; it never decides an answer. -/
namespace Tamarin.FreeFactoring
open FactoredUnification
variable {s : Signature} [DecidableEq s.Atom] [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym]

/-- A reachable factoring state. Deferred equations wait in `kept`. -/
structure Frame (p : Problem s) where
  todo : Problem s
  kept : Problem s
  θ : Substitution s
  trace : Trace p .identity (todo ++ kept) θ

/-- A variable may be bound to a term of its sort that does not contain it. -/
private def bindable (v : Variable) (t : Term s) : Option (PLift (HasSort t v.sort ∧ ¬ t.Occurs v)) :=
  letI := Term.occursDecidable v t
  if ho : t.Occurs v then none
  else if hs : t.checkSort v.sort = true then some ⟨Term.checkSort_sound _ _ hs, ho⟩ else none

/-- Replace one variable, storing the arguments of every rebuilt free
application. `Term.subst` leaves them as closures that substitute again on
every access, one layer per binding. -/
private def replace (v : Variable) (t : Term s) : Term s → Term s
  | .var w => if w = v then t else .var w
  | .atom a => .atom a
  | .free f xs =>
    let stored := Vector.ofFn fun i => replace v t (xs i)
    .free f fun i => stored[i]
  | .comm f a b => .comm f (replace v t a) (replace v t b)
  | .ac f a b => .ac f (replace v t a) (replace v t b)

omit [DecidableEq s.Atom] [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] in
private theorem replace_eq (v : Variable) (t : Term s) (ht : HasSort t v.sort) (u : Term s) :
    replace v t u = (Substitution.binding v t ht).apply u := by
  induction u with
  | var w => simp [replace, Substitution.apply, Term.subst, Substitution.binding]
  | atom => rfl
  | free f xs ih =>
    simp only [replace, Substitution.apply, Term.subst]
    exact congrArg (Term.free f) (funext fun i => by simpa [Substitution.apply] using ih i)
  | comm f a b ia ib | ac f a b ia ib =>
    simp only [replace, Substitution.apply, Term.subst] at ia ib ⊢
    rw [ia, ib]

/-- Terms without the variable are shared, not rebuilt. -/
private def swap (v : Variable) (t u : Term s) : Term s :=
  letI := Term.occursDecidable v u
  if u.Occurs v then replace v t u else u

omit [DecidableEq s.Atom] [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] in
private theorem swap_eq (v : Variable) (t : Term s) (ht : HasSort t v.sort) (u : Term s) :
    swap v t u = (Substitution.binding v t ht).apply u := by
  unfold swap
  split
  · exact replace_eq v t ht u
  · next no => exact (Substitution.binding_apply_of_not_occurs v t u ht no).symm

private def rewrite (v : Variable) (t : Term s) (p : Problem s) : Problem s :=
  p.map fun e => ⟨swap v t e.lhs, swap v t e.rhs⟩

omit [DecidableEq s.Atom] [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] in
private theorem rewrite_eq (v : Variable) (t : Term s) (ht : HasSort t v.sort) (p : Problem s) :
    rewrite v t p = p.substitute (.binding v t ht) := by
  simp only [rewrite, Problem.substitute, swap_eq v t ht]

/-- Deferred equations return to the worklist: the binding may expose a free head. -/
private def bind (p : Problem s) (v : Variable) (t : Term s) (rest kept : Problem s)
    (θ : Substitution s) (ok : HasSort t v.sort ∧ ¬ t.Occurs v)
    (tr : Trace p .identity (⟨.var v,t⟩ :: (rest ++ kept)) θ) : Frame p :=
  ⟨rewrite v t (rest ++ kept), [], (Substitution.binding v t ok.1).compose θ,
    by rw [List.append_nil, rewrite_eq v t ok.1]; exact tr.trans (.bind v t ok.1 ok.2 _ _)⟩

private def settle (p : Problem s) (a b : Term s) (rest kept : Problem s) (θ : Substitution s)
    (tr : Trace p .identity (⟨a,b⟩ :: (rest ++ kept)) θ) : Frame p :=
  if same : a = b then ⟨rest, kept, θ, tr.trans (.discard (same ▸ .refl _) _ _)⟩
  else
    let defer : Frame p := ⟨rest, ⟨a,b⟩ :: kept, θ, tr.trans (.perm List.perm_middle.symm _)⟩
    match a, b, tr with
    | .var v, t, tr =>
      match bindable v t with
      | some ok => bind p v t rest kept θ ok.down tr
      | none =>
        match t, tr with
        | .var w, tr =>
          match bindable w (.var v : Term s) with
          | some ok => bind p w (.var v) rest kept θ ok.down (tr.trans (.swap _ _ _ _))
          | none => defer
        | _, _ => defer
    | t, .var v, tr =>
      match bindable v t with
      | some ok => bind p v t rest kept θ ok.down (tr.trans (.swap _ _ _ _))
      | none => defer
    | .free f xs, .free g ys, tr =>
      if eq : f = g then by
        subst eq
        exact ⟨Matching.children f xs ys ++ rest, kept, θ,
          by rw [List.append_assoc]; exact tr.trans (.positional f xs ys _ _)⟩
      else defer
    | _, _, _ => defer

/-- Equal free heads decompose at once. Comparing the two sides first would
walk them again at every level; their leaves are compared when reached. -/
private def advance (p : Problem s) (a b : Term s) (rest kept : Problem s) (θ : Substitution s)
    (tr : Trace p .identity (⟨a,b⟩ :: (rest ++ kept)) θ) : Frame p :=
  match a, b, tr with
  | .free f xs, .free g ys, tr =>
    if eq : f = g then by
      subst eq
      exact ⟨Matching.children f xs ys ++ rest, kept, θ,
        by rw [List.append_assoc]; exact tr.trans (.positional f xs ys _ _)⟩
    else ⟨rest, ⟨.free f xs,.free g ys⟩ :: kept, θ, tr.trans (.perm List.perm_middle.symm _)⟩
  | a, b, tr => settle p a b rest kept θ tr

private def go (p : Problem s) : Nat → Frame p → Frame p
  | 0, st => st
  | n+1, st =>
    match st with
    | ⟨[], _, _, _⟩ => st
    | ⟨⟨a,b⟩ :: rest, kept, θ, tr⟩ => go p n (advance p a b rest kept θ tr)

/-- Decompose free heads and drop identical sides without binding anything. -/
private def split (p : Problem s) (a b : Term s) (rest kept : Problem s) (θ : Substitution s)
    (tr : Trace p .identity (⟨a,b⟩ :: (rest ++ kept)) θ) : Frame p :=
  match a, b, tr with
  | .free f xs, .free g ys, tr =>
    if eq : f = g then by
      subst eq
      exact ⟨Matching.children f xs ys ++ rest, kept, θ,
        by rw [List.append_assoc]; exact tr.trans (.positional f xs ys _ _)⟩
    else ⟨rest, ⟨.free f xs,.free g ys⟩ :: kept, θ, tr.trans (.perm List.perm_middle.symm _)⟩
  | a, b, tr =>
    if same : a = b then ⟨rest, kept, θ, tr.trans (.discard (same ▸ .refl _) _ _)⟩
    else ⟨rest, ⟨a,b⟩ :: kept, θ, tr.trans (.perm List.perm_middle.symm _)⟩

/-- A first pass that only decomposes. Each later binding then rewrites the
small equations between leaves, not the undecomposed input terms. -/
private def spread (p : Problem s) : Nat → Frame p → Frame p
  | 0, st => st
  | n+1, st =>
    match st with
    | ⟨[], _, _, _⟩ => st
    | ⟨⟨a,b⟩ :: rest, kept, θ, tr⟩ => spread p n (split p a b rest kept θ tr)

private def restart (p : Problem s) (st : Frame p) : Frame p :=
  ⟨st.todo ++ st.kept, [], st.θ, by rw [List.append_nil]; exact st.trace⟩

private def weight : Term s → Nat
  | .var _ | .atom _ => 1
  | .free _ xs => 1 + (List.ofFn fun i => weight (xs i)).sum
  | .comm _ a b | .ac _ a b => 1 + weight a + weight b

private def weightFrom : Term s → Nat → Nat
  | .var _, acc | .atom _, acc => acc + 1
  | .free _ xs, acc => Fin.foldr _ (fun i acc => weightFrom (xs i) acc) (acc + 1)
  | .comm _ a b, acc | .ac _ a b, acc => weightFrom a (weightFrom b (acc + 1))

omit [DecidableEq s.Atom] [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] in
private theorem foldr_sum {n} (g : Fin n → Nat) (acc : Nat) :
    Fin.foldr n (fun i acc => g i + acc) acc = (List.ofFn g).sum + acc := by
  induction n with
  | zero => simp
  | succ n ih => simp [Fin.foldr_succ, List.ofFn_succ, ih, Nat.add_assoc]

omit [DecidableEq s.Atom] [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] in
private theorem weightFrom_eq (t : Term s) (acc : Nat) : weightFrom t acc = weight t + acc := by
  induction t generalizing acc with
  | var | atom => simp [weightFrom, weight, Nat.add_comm]
  | free f xs ih =>
    simp only [weightFrom, weight, ih]
    rw [foldr_sum]
    omega
  | comm f a b ia ib | ac f a b ia ib =>
    simp only [weightFrom, weight, ia, ib]
    omega

/-- `weight` without a list of argument weights at every application. -/
private def weightDirect (t : Term s) : Nat := weightFrom t 0

@[csimp] private theorem weight_eq_direct : @weight = @weightDirect := by
  funext s t
  simp [weightDirect, weightFrom_eq]

/-- Enough for every input whose bindings do not duplicate large subterms. -/
private def fuel (p : Problem s) : Nat :=
  let size := (p.map fun e => weight e.lhs + weight e.rhs).sum + p.length + 2
  size * size

def factor (p : Problem s) : Frame p :=
  let fuel := fuel p
  go p fuel (restart p (spread p fuel ⟨p, [], .identity, by rw [List.append_nil]; exact .done _ _⟩))

/-- The same term with the arguments of every free application stored. -/
private def force : Term s → Term s
  | .var v => .var v
  | .atom a => .atom a
  | .free f xs =>
    let stored := Vector.ofFn fun i => force (xs i)
    .free f fun i => stored[i]
  | .comm f a b => .comm f (force a) (force b)
  | .ac f a b => .ac f (force a) (force b)

omit [DecidableEq s.Atom] [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] in
private theorem force_eq (t : Term s) : force t = t := by
  induction t with
  | var | atom => rfl
  | free f xs ih =>
    simp only [force]
    exact congrArg (Term.free f) (funext fun i => by simpa using ih i)
  | comm f a b ia ib | ac f a b ia ib => simp only [force, ia, ib]

private def lookup : List (Variable × Term s) → Variable → Option (Term s)
  | [], _ => none
  | (w,t) :: rest, v => if v = w then some t else lookup rest v

omit [DecidableEq s.Atom] [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] in
private theorem lookup_map (f : Variable → Term s) (keys : List Variable) (v : Variable) :
    (lookup (keys.map fun w => (w, f w)) v).getD (f v) = f v := by
  induction keys with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, lookup]
    split
    · next h => rw [h]; rfl
    · exact ih

private def tabledWith (θ : Substitution s) (table : List (Variable × Term s))
    (same : ∀ v, (lookup table v).getD (θ.image v) = θ.image v) : Substitution s where
  image := fun v => (lookup table v).getD (θ.image v)
  support := θ.support
  outside := fun v hv => (same v).trans (θ.outside v hv)
  sorted := fun v => by rw [same v]; exact θ.sorted v

/-- The accumulated bindings are a chain of compositions. Evaluate the image
of every listed variable once and read the rest through the chain. -/
private def tabled (θ : Substitution s) (keys : List Variable) : Substitution s :=
  tabledWith θ (keys.map fun w => (w, force (θ.image w)))
    (fun v => by simp only [force_eq]; exact lookup_map θ.image keys v)

omit [DecidableEq s.Atom] [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] in
private theorem tabled_eq (θ : Substitution s) (keys : List Variable) : tabled θ keys = θ := by
  have build : ∀ (f : Variable → Term s) (h₁ h₂), f = θ.image →
      (⟨f, θ.support, h₁, h₂⟩ : Substitution s) = θ := by
    intro f h₁ h₂ e
    subst e
    rfl
  exact build _ _ _ (funext fun v => by simp only [force_eq]; exact lookup_map θ.image keys v)

/-- Solve the residual with witnesses apart from every input variable, then
compose each residual answer with the accumulated bindings. -/
def solve (u : VerifiedUnifier s (fun _ => True)) (p : Problem s) (avoid : List Variable) :
    List (Substitution s) :=
  let st := factor p
  let θ := tabled st.θ (Buckets.dedup Variable.id p.variables)
  (u.solve (st.todo ++ st.kept) trivial (p.variables ++ avoid)).map fun σ => σ.compose θ

/-- The answers are the residual answers composed with the accumulated bindings. -/
theorem solve_eq (u : VerifiedUnifier s (fun _ => True)) (p : Problem s) (avoid : List Variable) :
    solve u p avoid = (u.solve ((factor p).todo ++ (factor p).kept) trivial (p.variables ++ avoid)).map
      fun σ => σ.compose (factor p).θ := by
  simp only [solve, tabled_eq]

theorem correct (u : VerifiedUnifier s (fun _ => True)) (p : Problem s) (avoid : List Variable) :
    (Outcome.complete (solve u p avoid)).CorrectIn p avoid := by
  simp only [solve, tabled_eq]
  exact (factor p).trace.correctIn (fun v hv => (p.mem_variables v).mpr hv)
    ⟨u.correct _ _ _, u.domain _ _ _, u.fresh _ _ _⟩

/-- Any complete unifier for the residual gives one for the input. -/
def unifier (u : VerifiedUnifier s (fun _ => True)) : VerifiedUnifier s (fun _ => True) where
  solve p _ avoid := solve u p avoid
  correct p _ avoid := (correct u p avoid).mathematical
  domain p _ avoid := (correct u p avoid).domain
  fresh p _ avoid := (correct u p avoid).fresh

end Tamarin.FreeFactoring
