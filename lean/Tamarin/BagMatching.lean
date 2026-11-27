import Tamarin.MatchRows
import Tamarin.TermEquality
import Tamarin.DHProduct

/-! Whole-term matching on operand bags. An AC subject is read once as the bag
of its operands. Rigid pattern operands each remove one subject operand, and
the bindable variables of the same AC application then share what is left.
Subject operands that are syntactically identical are interchangeable, so a
choice among them is listed once. The number of rows therefore follows the
number of distinct assignments, not the number of ways to split a list. -/
namespace Tamarin.BagMatching
open ReferenceMatching ACRepresentation Matching
open Cancellation (classOf)

section Bags
variable {α : Type} (same : α → α → Bool)

/-- Sub-bags with at most `k` elements, each with its complement. Skipping an
element bans every later element identified with it, so the taken copies of
one element are always its first occurrences. -/
def sub : Nat → List α → List α → List (List α × List α)
  | 0, _, xs => [([], xs)]
  | _ + 1, _, [] => [([], [])]
  | k + 1, banned, x :: xs =>
    let skip := (sub (k + 1) (x :: banned) xs).map fun (l, r) => (l, x :: r)
    if banned.any (same · x) then skip
    else (sub k banned xs).map (fun (l, r) => (x :: l, r)) ++ skip

theorem sub_sound (k : Nat) (banned xs : List α) {l r}
    (h : (l, r) ∈ sub same k banned xs) : xs.Perm (l ++ r) := by
  induction xs generalizing k banned l r with
  | nil =>
    cases k <;> simp only [sub, List.mem_singleton, Prod.mk.injEq] at h <;>
      (obtain ⟨rfl, rfl⟩ := h; exact .refl _)
  | cons x xs ih =>
    cases k with
    | zero =>
      simp only [sub, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .refl _
    | succ k =>
      have skipped {l r} (m : (l, r) ∈ (sub same (k + 1) (x :: banned) xs).map
          fun (l, r) => (l, x :: r)) : (x :: xs).Perm (l ++ r) := by
        obtain ⟨⟨a, b⟩, hm, eq⟩ := List.mem_map.mp m
        cases eq
        exact ((ih _ _ hm).cons x).trans List.perm_middle.symm
      simp only [sub] at h
      split at h
      · exact skipped h
      · rcases List.mem_append.mp h with taken | m
        · obtain ⟨⟨a, b⟩, hm, eq⟩ := List.mem_map.mp taken
          cases eq
          exact (ih _ _ hm).cons x
        · exact skipped m

/-- Every sub-bag of keys is listed, provided identified elements share a key
and no key of a banned element is requested. -/
theorem sub_complete {β : Type} (key : α → β) (hs : ∀ a b, same a b = true → key a = key b)
    (k : Nat) (banned xs : List α) {A B : List β} (h : (xs.map key).Perm (A ++ B))
    (free : ∀ b ∈ banned, key b ∉ A) (len : A.length ≤ k) :
    ∃ l r, (l, r) ∈ sub same k banned xs ∧ (l.map key).Perm A ∧ (r.map key).Perm B := by
  classical
  induction xs generalizing k banned A B with
  | nil =>
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h.symm.eq_nil
    exact ⟨[], [], by cases k <;> simp [sub], .nil, .nil⟩
  | cons x xs ih =>
    cases k with
    | zero =>
      obtain rfl := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp len)
      exact ⟨[], x :: xs, by simp [sub], .nil, h⟩
    | succ k =>
      by_cases hx : key x ∈ A
      · have open_ : banned.any (same · x) = false := by
          apply Bool.eq_false_iff.mpr
          intro hit
          obtain ⟨b, hb, sb⟩ := List.any_eq_true.mp hit
          exact free b hb (hs b x sb ▸ hx)
        have put := List.perm_cons_erase hx
        have rest : (xs.map key).Perm (A.erase (key x) ++ B) :=
          (h.trans (put.append_right B)).cons_inv
        have short : (A.erase (key x)).length ≤ k := by
          have := put.length_eq
          simp only [List.length_cons] at this
          omega
        obtain ⟨l, r, hm, hl, hr⟩ := ih k banned rest
          (fun b hb hit => free b hb (List.mem_of_mem_erase hit)) short
        refine ⟨x :: l, r, ?_, (hl.cons _).trans put.symm, hr⟩
        simp only [sub, open_]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨(l, r), hm, rfl⟩)
      · have inB : key x ∈ B :=
          (List.mem_append.mp (h.mem_iff.mp List.mem_cons_self)).resolve_left hx
        have put := List.perm_cons_erase inB
        have rest : (xs.map key).Perm (A ++ B.erase (key x)) :=
          (h.trans ((put.append_left A).trans List.perm_middle)).cons_inv
        obtain ⟨l, r, hm, hl, hr⟩ := ih (k + 1) (x :: banned) rest
          (fun b hb => (List.mem_cons.mp hb).elim (fun e => e ▸ hx) (free b)) len
        refine ⟨l, x :: r, ?_, hl, (hr.cons _).trans put.symm⟩
        have skipped : (l, x :: r) ∈ (sub same (k + 1) (x :: banned) xs).map
            fun (l, r) => (l, x :: r) := List.mem_map.mpr ⟨(l, r), hm, rfl⟩
        simp only [sub]
        split
        · exact skipped
        · exact List.mem_append_right _ skipped

/-- One element with the rest of the bag, once per identified element. -/
def picks (xs : List α) : List (α × List α) :=
  (sub same 1 [] xs).filterMap fun
    | ([x], r) => some (x, r)
    | _ => none

theorem picks_sound (xs : List α) {x r} (h : (x, r) ∈ picks same xs) : xs.Perm (x :: r) := by
  obtain ⟨⟨l, r'⟩, hm, eq⟩ := List.mem_filterMap.mp h
  match l, hm, eq with
  | [y], hm, eq =>
    cases eq
    exact sub_sound same _ _ _ hm

theorem picks_complete {β : Type} (key : α → β) (hs : ∀ a b, same a b = true → key a = key b)
    (xs : List α) {k : β} {W : List β} (h : (xs.map key).Perm (k :: W)) :
    ∃ x r, (x, r) ∈ picks same xs ∧ key x = k ∧ (r.map key).Perm W := by
  obtain ⟨l, r, hm, hl, hr⟩ := sub_complete same key hs 1 [] xs (A := [k]) (B := W) h
    (fun _ hb => nomatch hb) (Nat.le_refl 1)
  cases l with
  | nil => exact absurd hl.length_eq (by simp)
  | cons x l =>
    cases l with
    | nil =>
      have eq : key x = k := by simpa using hl.mem_iff.mp List.mem_cons_self
      exact ⟨x, r, List.mem_filterMap.mpr ⟨([x], r), hm, rfl⟩, eq, hr⟩
    | cons y l => exact absurd hl.length_eq (by simp)

end Bags

variable {s : Signature}

/-- A branch in progress: the requirements so far, the operands not yet
consumed, and the bindable variables of the enclosing AC application that
still await their share. -/
abbrev Partial (s : Signature) := Requirements s × List (Term s) × List Variable

def finish : Partial s → Option (Requirements s)
  | (row, [], []) => some row
  | _ => none

/-- Two requirements on one variable must agree. -/
def consistent (eq : Term s → Term s → Bool) : Requirements s → Bool
  | [] => true
  | (v, t) :: rest => rest.all (fun (w, u) => v != w || eq t u) && consistent eq rest

theorem consistent_of_holds {eq : Term s → Term s → Bool} (heq : ∀ a b, EquivB a b → eq a b = true)
    {σ : Substitution s} {row : Requirements s} (h : holds σ row) : consistent eq row = true := by
  induction row with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨v, t⟩ := e
    simp only [consistent, Bool.and_eq_true, List.all_eq_true]
    refine ⟨fun ⟨w, u⟩ hm => ?_, ih (fun v t m => h v t (List.mem_cons_of_mem _ m))⟩
    by_cases same : v = w
    · subst w
      have a := h v t List.mem_cons_self
      have b := h v u (List.mem_cons_of_mem _ hm)
      simp [heq t u (a.symm.trans b)]
    · simp [same]

theorem holds_append {σ : Substitution s} {a b : Requirements s} :
    holds σ (a ++ b) ↔ holds σ a ∧ holds σ b :=
  ⟨fun h => ⟨fun v t m => h v t (List.mem_append_left _ m), fun v t m => h v t (List.mem_append_right _ m)⟩,
    fun ⟨ha, hb⟩ v t m => (List.mem_append.mp m).elim (ha v t) (hb v t)⟩

/-- Remove one operand equal to `u` modulo B. -/
def takeOne (eq : Term s → Term s → Bool) (u : Term s) : List (Term s) → Option (List (Term s))
  | [] => none
  | z :: zs => if eq u z then some zs else (takeOne eq u zs).map (z :: ·)

def takeAll (eq : Term s → Term s → Bool) : List (Term s) → List (Term s) → Option (List (Term s))
  | [], zs => some zs
  | u :: us, zs => (takeOne eq u zs).bind (takeAll eq us)

/-- Pairs are combined only when the first component has a branch. -/
def andThen (xs : List (Requirements s)) (ys : Unit → List (Requirements s)) : List (Requirements s) :=
  if xs.isEmpty then [] else combine xs (ys ())

theorem andThen_eq (xs : List (Requirements s)) (ys : Unit → List (Requirements s)) :
    andThen xs ys = combine xs (ys ()) := by
  unfold andThen
  split
  · next h => simp [List.isEmpty_iff.mp h, combine]
  · rfl

/-- Combine the branches of several subproblems. A partial combination is
dropped as soon as two of its requirements disagree, so shared variables
prune the product instead of filtering it at the end. -/
def joined (eq : Term s → Term s → Bool) : List (List (Requirements s)) → List (Requirements s)
  | [] => [[]]
  | xs :: rest => (andThen xs fun _ => joined eq rest).filter (consistent eq)

/-- Known before the search: `k` occurrences of `v` are direct operands of an
application of `g` that must equal a subject with the operands `bag`. -/
structure Bound (s : Signature) where
  g : s.ACSym
  v : Variable
  k : Nat
  bag : List (Term s)

/-- Scan a bag, keeping an operand while fewer than `limit` operands equal to
it are kept. The second component holds the operands passed over. -/
def keep (eq : Term s → Term s → Bool) (limit : Term s → Nat) :
    List (Term s) → List (Term s) → List (Term s) × List (Term s)
  | kept, [] => (kept, [])
  | kept, x :: xs =>
    if kept.countP (eq x) < limit x then keep eq limit (x :: kept) xs
    else
      let later := keep eq limit kept xs
      (later.1, x :: later.2)

/-- Lower `n` to what every recorded bound allows for copies of `x`. -/
def capped (eq : Term s → Term s → Bool) (bounds : List (Bound s)) (x : Term s) (n : Nat) : Nat :=
  bounds.foldl (fun n b => min n (b.bag.countP (eq x) / b.k)) n

/-- The operands one of `k` occurrences of a variable can take, and the rest.
An image taken `k` times uses at most `⌊m / k⌋` of `m` equal operands, and no
more than the recorded bounds of the variable allow. -/
def pool (eq : Term s → Term s → Bool) (bounds : List (Bound s)) (k : Nat) (zs : List (Term s)) :
    List (Term s) × List (Term s) :=
  if k ≤ 1 && bounds.isEmpty then (zs, [])
  else keep eq (fun x => capped eq bounds x (zs.countP (eq x) / k)) [] zs

/-- The copies of `x`, out of `m`, that the other waiting occurrences can take at
most. An
occurrence of a variable waiting `n` times takes at most `⌊m / n⌋` of `m`
equal operands, and no more than the recorded bounds of its variable allow. -/
def absorbed (eq : Term s → Term s → Bool) (others : List (Nat × List (Bound s)))
    (m : Nat) (x : Term s) : Nat :=
  (others.map fun w => capped eq w.2 x (m / w.1)).sum

/-- Split the pool of a variable waiting `k` times into the operands its image
must contain and the operands it may contain. When nothing is left over, the
image takes every copy that the other waiting occurrences cannot. -/
def forced (eq : Term s → Term s → Bool) (spare : Bool) (k : Nat)
    (others : List (Nat × List (Bound s))) (zs pool : List (Term s)) :
    List (Term s) × List (Term s) :=
  if spare || others.any (fun w => w.1 == 1 && w.2.isEmpty) then ([], pool)
  else keep eq (fun x =>
    let m := zs.countP (eq x)
    (m - absorbed eq others m x + (k - 1)) / k) [] pool

section
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

def same (a b : Term s) : Bool := decide (a = b)

/-- The recorded bounds of one variable under one symbol. -/
def mine (tab : List (Bound s)) (g : s.ACSym) (v : Variable) : List (Bound s) :=
  tab.filter fun b => b.g = g && b.v == v && b.k != 0

/-- The largest image of a variable waiting `k` times in a bag of `size`
operands, of which `waiting` go to other occurrences. Every occurrence takes
at least one operand, and so does a spare remainder. A variable whose sort
lies below the operand sort takes one operand only. -/
def room (g : s.ACSym) (v : Variable) (spare : Bool) (k waiting size : Nat) : Nat :=
  if Subsort.check (s.acSort g) v.sort then (size - waiting - (if spare then 1 else 0)) / k else 1

/-- Share operands among the waiting variables. A variable that already has an
image must receive that image again. A new variable chooses its image inside
its pool, always including the forced operands and never exceeding its room.
With `spare` a nonempty remainder is left over and returned; without it
everything is consumed and the last new variable takes all that is left. -/
def share (eq : Term s → Term s → Bool) (tab : List (Bound s)) (g : s.ACSym) (spare : Bool) :
    Requirements s → List Variable → List (Term s) → List (Requirements s × List (Term s))
  | _, [], zs => if zs.isEmpty == spare then [] else [([], zs)]
  | acc, v :: vs, zs =>
    match acc.lookup v with
    | some u =>
      match takeAll eq (flatten g u) zs with
      | some r => share eq tab g spare acc vs r
      | none => []
    | none =>
      if !spare && vs.isEmpty then
        match decode g zs with
        | some t => if t.checkSort v.sort then [([(v, t)], [])] else []
        | none => []
      else
        let k := vs.count v + 1
        let others := vs.filter (· != v)
        let pool := pool eq (mine tab g v) k zs
        let must := forced eq spare k (others.map fun w => (others.count w, mine tab g w)) zs pool.1
        let size := room g v spare k others.length zs.length
        if size < must.1.length then []
        else (sub same (size - must.1.length) [] must.2).flatMap fun (l, r) =>
          match decode g (must.1 ++ l) with
          | some t =>
            if t.checkSort v.sort then
              (share eq tab g spare ((v, t) :: acc) vs (r ++ pool.2)).map fun out => ((v, t) :: out.1, out.2)
            else []
          | none => []

/-- Variables that already have an image come first, then the variables that
take a single operand. -/
def order (g : s.ACSym) (acc : Requirements s) (vs : List Variable) : List Variable :=
  let known := fun v => (acc.lookup v).isSome
  let narrow := fun v => !Subsort.check (s.acSort g) v.sort
  let open_ := vs.filter (fun v => !known v)
  vs.filter known ++ (open_.filter narrow ++ open_.filter (fun v => !narrow v))

/-- Share all remaining operands among the waiting variables. -/
def dist (eq : Term s → Term s → Bool) (tab : List (Bound s)) (g : s.ACSym) (acc : Requirements s)
    (vs : List Variable) (zs : List (Term s)) : List (Requirements s) :=
  (share eq tab g false acc (order g acc vs) zs).map (·.1)

/-- Match one pattern operand against each distinct operand of the bag. -/
def operand (xs : List (Term s)) (single : Term s → List (Requirements s)) : List (Partial s) :=
  (picks same xs).flatMap fun (x, r) => (single x).map (·, r, [])

/-- Remove the operands of a pattern from a bag. Inside an application of the
context symbol the pattern contributes several operands and its bindable
variables wait. Elsewhere the pattern is one operand. -/
def go (tab : List (Bound s)) (bind : Variable → Bool) (eq : Term s → Term s → Bool) :
    Term s → Option s.ACSym → List (Term s) → List (Partial s)
  | .var v, ctx, xs =>
    if bind v then
      match ctx with
      | some _ => [([], xs, [v])]
      | none => operand xs fun x => if x.checkSort v.sort then [[(v, x)]] else []
    else operand xs fun x => if isVariable v x then [[]] else []
  | .atom a, _, xs => operand xs fun x =>
      match x with
      | .atom b => if a = b then [[]] else []
      | _ => []
  | .free f ps, _, xs => operand xs fun x =>
      match x with
      | .free g ys =>
        if h : f = g then
          joined eq (List.ofFn fun i => (go tab bind eq (ps i) none [ys (h ▸ i)]).filterMap finish)
        else []
      | _ => []
  | .comm f a b, _, xs => operand xs fun x =>
      match x with
      | .comm g l m =>
        if f = g then
          (andThen ((go tab bind eq a none [l]).filterMap finish)
              (fun _ => (go tab bind eq b none [m]).filterMap finish) ++
            andThen ((go tab bind eq a none [m]).filterMap finish)
              (fun _ => (go tab bind eq b none [l]).filterMap finish)).filter (consistent eq)
        else []
      | _ => []
  | .ac g a b, ctx, xs =>
    if ctx = some g then
      (go tab bind eq a ctx xs).flatMap fun (r1, ys, v1) =>
        (go tab bind eq b ctx ys).filterMap fun (r2, zs, v2) =>
          if consistent eq (r1 ++ r2) then some (r1 ++ r2, zs, v1 ++ v2) else none
    else operand xs fun x =>
      ((go tab bind eq a (some g) (flatten g x)).flatMap fun (r1, ys, v1) =>
        (go tab bind eq b (some g) ys).flatMap fun (r2, zs, v2) =>
          (dist eq tab g (r1 ++ r2) (v1 ++ v2) zs).map fun r3 => r1 ++ r2 ++ r3).filter (consistent eq)

/-- Branches of a whole pattern against a whole subject. -/
def rows (tab : List (Bound s)) (bind : Variable → Bool) (eq : Term s → Term s → Bool) (p t : Term s) :
    List (Requirements s) :=
  (go tab bind eq p none [t]).filterMap finish

/-- Branches of a pattern against a proper sub-product of an application of
`g`, each with the operands it leaves untouched. -/
def around (bind : Variable → Bool) (eq : Term s → Term s → Bool) (g : s.ACSym) (p t : Term s) :
    List (Requirements s × List (Term s)) :=
  ((go [] bind eq p (some g) (flatten g t)).flatMap fun (row, ys, vs) =>
    (share eq [] g true row (order g row vs) ys).map fun out => (row ++ out.1, out.2)).filter
      fun out => consistent eq out.1

end

/-! ### Specification

Operand bags are compared as lists of B-classes. Inside an application of
`g` a term contributes the classes of its `g`-operands; elsewhere it is one
class. -/

abbrev cls (xs : List (Term s)) : List (Cancellation.Class s) := xs.map classOf

noncomputable def opsC : Option s.ACSym → Term s → List (Cancellation.Class s)
  | some g, t => Cancellation.flatten g t
  | none, t => [classOf t]

/-- The classes owed to waiting variables. -/
noncomputable def pend (ctx : Option s.ACSym) (σ : Substitution s) (vs : List Variable) :
    List (Cancellation.Class s) :=
  vs.flatMap fun v => opsC ctx (σ.image v)

/-- Every listed term is a single operand of the context. -/
def Flat (ctx : Option s.ACSym) (xs : List (Term s)) : Prop := ∀ x ∈ xs, opsC ctx x = [classOf x]

theorem Flat.of_subset {ctx : Option s.ACSym} {xs ys : List (Term s)} (h : Flat ctx xs)
    (sub : ∀ y ∈ ys, y ∈ xs) : Flat ctx ys := fun y hy => h y (sub y hy)

theorem perm_split {β : Type} {x k : β} {xs W : List β} (h : (x :: xs).Perm (k :: W)) (ne : x ≠ k) :
    ∃ W', W.Perm (x :: W') ∧ xs.Perm (k :: W') := by
  classical
  have inW : x ∈ W := (List.mem_cons.mp (h.mem_iff.mp List.mem_cons_self)).resolve_left ne
  have put := List.perm_cons_erase inW
  exact ⟨W.erase x, put, (h.trans ((put.cons k).trans (.swap x k _))).cons_inv⟩

theorem flatC_fold (g : s.ACSym) (a : Term s) (as : List (Term s))
    (flat : ∀ t ∈ a :: as, Cancellation.flatten g t = [classOf t]) :
    Cancellation.flatten g (fold g a as) = cls (a :: as) := by
  induction as generalizing a with
  | nil => exact flat a List.mem_cons_self
  | cons b bs ih =>
    simp only [fold, Cancellation.flatten_ac, flat a List.mem_cons_self,
      ih b (fun t ht => flat t (List.mem_cons_of_mem _ ht)), List.singleton_append, List.map_cons]

theorem fold_cls (g : s.ACSym) (xs : List (Term s)) :
    Cancellation.fold g (cls xs) = (decode g xs).map classOf := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons, Cancellation.fold, ih]
    cases xs <;> rfl

/-- A bag with the operand classes of a term decodes to that term modulo B. -/
theorem decode_of_perm (g : s.ACSym) {zs : List (Term s)} {v : Term s}
    (perm : (cls zs).Perm (Cancellation.flatten g v)) : ∃ t, decode g zs = some t ∧ EquivB v t := by
  have e := Cancellation.fold_perm g perm
  rw [fold_cls, Cancellation.fold_flatten] at e
  cases h : decode g zs with
  | none => simp [h] at e
  | some u =>
    have same : classOf u = classOf v := by simpa [h] using e
    exact ⟨u, rfl, Quotient.exact same.symm⟩

theorem ac_of_operands (g : s.ACSym) (t : Term s) (h : 1 < (Cancellation.flatten g t).length) :
    ∃ a b, t = .ac g a b := by
  classical
  cases t with
  | ac f a b =>
    by_cases same : g = f
    · exact ⟨a, b, same ▸ rfl⟩
    · simp [Cancellation.flatten, same] at h
  | _ => simp [Cancellation.flatten] at h

theorem takeOne_subset {eq : Term s → Term s → Bool} {u : Term s} {zs r : List (Term s)}
    (h : takeOne eq u zs = some r) : ∀ x ∈ r, x ∈ zs := by
  induction zs generalizing r with
  | nil => simp [takeOne] at h
  | cons z zs ih =>
    simp only [takeOne] at h
    split at h
    · cases h
      exact fun x hx => List.mem_cons_of_mem _ hx
    · obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.mp h
      exact fun x hx => (List.mem_cons.mp hx).elim (fun e => e ▸ List.mem_cons_self)
        (fun m => List.mem_cons_of_mem _ (ih hr x m))

theorem takeAll_subset {eq : Term s → Term s → Bool} {us zs r : List (Term s)}
    (h : takeAll eq us zs = some r) : ∀ x ∈ r, x ∈ zs := by
  induction us generalizing zs with
  | nil => cases h; exact fun _ hx => hx
  | cons u us ih =>
    obtain ⟨m, hm, rest⟩ := Option.bind_eq_some_iff.mp h
    exact fun x hx => takeOne_subset hm x (ih rest x hx)

theorem takeOne_sound {eq : Term s → Term s → Bool} (heq : ∀ a b, eq a b = true → EquivB a b)
    {u : Term s} {zs r : List (Term s)} (h : takeOne eq u zs = some r) :
    (cls zs).Perm (classOf u :: cls r) := by
  induction zs generalizing r with
  | nil => simp [takeOne] at h
  | cons z zs ih =>
    simp only [takeOne] at h
    split at h
    · next hit =>
      cases h
      have e : classOf z = classOf u := Quotient.sound (heq u z hit).symm
      simp only [List.map_cons, e]
      exact .refl _
    · obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ((ih hr).cons _).trans (.swap ..)

theorem takeOne_complete {eq : Term s → Term s → Bool} (heq : ∀ a b, eq a b = true ↔ EquivB a b)
    {u : Term s} {zs : List (Term s)} {B : List (Cancellation.Class s)}
    (h : (cls zs).Perm (classOf u :: B)) : ∃ r, takeOne eq u zs = some r ∧ (cls r).Perm B := by
  induction zs generalizing B with
  | nil => exact absurd h.length_eq (by simp)
  | cons z zs ih =>
    by_cases hit : eq u z = true
    · have e : classOf z = classOf u := Quotient.sound ((heq u z).mp hit).symm
      refine ⟨zs, by simp [takeOne, hit], ?_⟩
      simp only [List.map_cons, e] at h
      exact h.cons_inv
    · have ne : classOf z ≠ classOf u := fun e => hit ((heq u z).mpr (Quotient.exact e.symm))
      obtain ⟨B', hB, rest⟩ := perm_split h ne
      obtain ⟨r, hr, pr⟩ := ih rest
      exact ⟨z :: r, by simp [takeOne, hit, hr], (pr.cons _).trans hB.symm⟩

theorem takeAll_sound {eq : Term s → Term s → Bool} (heq : ∀ a b, eq a b = true → EquivB a b)
    {us zs r : List (Term s)} (h : takeAll eq us zs = some r) :
    (cls zs).Perm (cls us ++ cls r) := by
  induction us generalizing zs with
  | nil => cases h; exact .refl _
  | cons u us ih =>
    obtain ⟨m, hm, rest⟩ := Option.bind_eq_some_iff.mp h
    exact (takeOne_sound heq hm).trans ((ih rest).cons _)

theorem takeAll_complete {eq : Term s → Term s → Bool} (heq : ∀ a b, eq a b = true ↔ EquivB a b)
    {us zs : List (Term s)} {B : List (Cancellation.Class s)}
    (h : (cls zs).Perm (cls us ++ B)) : ∃ r, takeAll eq us zs = some r ∧ (cls r).Perm B := by
  induction us generalizing zs with
  | nil => exact ⟨zs, rfl, h⟩
  | cons u us ih =>
    obtain ⟨m, hm, pm⟩ := takeOne_complete heq (u := u) (B := cls us ++ B) h
    obtain ⟨r, hr, pr⟩ := ih pm
    exact ⟨r, by simp [takeAll, hm, hr], pr⟩

theorem accepts_filter {eq : Term s → Term s → Bool} (heq : ∀ a b, EquivB a b → eq a b = true)
    (σ : Substitution s) (rows : List (Requirements s)) :
    accepts σ (rows.filter (consistent eq)) ↔ accepts σ rows :=
  ⟨fun ⟨row, m, h⟩ => ⟨row, (List.mem_filter.mp m).1, h⟩,
    fun ⟨row, m, h⟩ => ⟨row, List.mem_filter.mpr ⟨m, consistent_of_holds heq h⟩, h⟩⟩

theorem joined_iff {eq : Term s → Term s → Bool} (heq : ∀ a b, EquivB a b → eq a b = true)
    (σ : Substitution s) (xss : List (List (Requirements s))) :
    accepts σ (joined eq xss) ↔ ∀ rows ∈ xss, accepts σ rows := by
  induction xss with
  | nil => simp [accepts, joined, holds]
  | cons x xs ih => simp [joined, accepts_filter heq, andThen_eq, combine_iff, ih]

theorem part_of_joined {eq : Term s → Term s → Bool} (xss : List (List (Requirements s))) {row}
    (member : row ∈ joined eq xss) {ys} (hy : ys ∈ xss) : ∃ part ∈ ys, part ⊆ row := by
  induction xss generalizing row with
  | nil => contradiction
  | cons y xss ih =>
    have inside := (List.mem_filter.mp member).1
    rw [andThen_eq] at inside
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_combine.mp inside
    rcases List.mem_cons.mp hy with rfl | hm
    · exact ⟨a, ha, List.subset_append_left ..⟩
    · obtain ⟨v, hv, sub⟩ := ih hb hm
      exact ⟨v, hv, sub.trans (List.subset_append_right ..)⟩

theorem joined_consistent {eq : Term s → Term s → Bool} (xss : List (List (Requirements s))) {row}
    (member : row ∈ joined eq xss) : consistent eq row = true := by
  cases xss with
  | nil =>
    obtain rfl := List.mem_singleton.mp member
    rfl
  | cons y xss => exact (List.mem_filter.mp member).2

theorem entry_of_joined {eq : Term s → Term s → Bool} (xss : List (List (Requirements s))) {row}
    (member : row ∈ joined eq xss) {e} (he : e ∈ row) : ∃ ys ∈ xss, ∃ part ∈ ys, e ∈ part := by
  induction xss generalizing row with
  | nil =>
    obtain rfl := List.mem_singleton.mp member
    contradiction
  | cons y xss ih =>
    have inside := (List.mem_filter.mp member).1
    rw [andThen_eq] at inside
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_combine.mp inside
    rcases List.mem_append.mp he with left | right
    · exact ⟨y, List.mem_cons_self, a, ha, left⟩
    · obtain ⟨ys, hy, part, hp, hit⟩ := ih hb right
      exact ⟨ys, List.mem_cons_of_mem _ hy, part, hp, hit⟩

/-- In a consistent row all requirements on one variable agree. -/
theorem consistent_pairs {eq : Term s → Term s → Bool} (heq : ∀ a b, eq a b = true → EquivB a b)
    {row : Requirements s} (ok : consistent eq row = true) {v : Variable} {t u : Term s}
    (ht : (v, t) ∈ row) (hu : (v, u) ∈ row) : EquivB t u := by
  induction row with
  | nil => contradiction
  | cons e rest ih =>
    obtain ⟨w, r⟩ := e
    simp only [consistent, Bool.and_eq_true, List.all_eq_true] at ok
    have later {a b : Term s} (head : (v, a) = (w, r)) (tail : (v, b) ∈ rest) : EquivB a b := by
      cases head
      have := ok.1 (v, b) tail
      simp only [bne_self_eq_false, Bool.false_or] at this
      exact heq _ _ this
    rcases List.mem_cons.mp ht with e1 | m1 <;> rcases List.mem_cons.mp hu with e2 | m2
    · cases e1; cases e2; exact .refl _
    · exact later e1 m2
    · exact (later e2 m1).symm
    · exact ih ok.2 m1 m2

theorem finish_eq {part : Partial s} {row : Requirements s} :
    finish part = some row ↔ part = (row, [], []) := by
  obtain ⟨r, ys, vs⟩ := part
  cases ys <;> cases vs <;> simp [finish]

theorem flat_flatten [DecidableEq s.ACSym] (g : s.ACSym) (x : Term s) :
    Flat (some g) (flatten g x) := by
  induction x with
  | ac f a b ia ib =>
    by_cases same : g = f
    · subst f
      intro u hu
      simp only [flatten, ite_true, List.mem_append] at hu
      exact hu.elim (ia u) (ib u)
    · intro u hu
      simp only [flatten, same, ite_false, List.mem_singleton] at hu
      subst u
      simp [opsC, Cancellation.flatten, same]
  | _ =>
    intro u hu
    simp only [flatten, List.mem_singleton] at hu
    subst u
    rfl

theorem pend_cons (ctx : Option s.ACSym) (σ : Substitution s) (v : Variable) (vs : List Variable) :
    pend ctx σ (v :: vs) = opsC ctx (σ.image v) ++ pend ctx σ vs := by
  simp [pend]

theorem pend_one (ctx : Option s.ACSym) (σ : Substitution s) (v : Variable) :
    pend ctx σ [v] = opsC ctx (σ.image v) := by
  simp [pend]

theorem pend_append (ctx : Option s.ACSym) (σ : Substitution s) (us vs : List Variable) :
    pend ctx σ (us ++ vs) = pend ctx σ us ++ pend ctx σ vs := by
  simp [pend]

theorem lookup_mem {acc : Requirements s} {v : Variable} {u : Term s}
    (h : acc.lookup v = some u) : (v, u) ∈ acc := by
  obtain ⟨l₁, l₂, eq, _⟩ := List.lookup_eq_some_iff.mp h
  simp [eq]

theorem cls_flatten [DecidableEq s.ACSym] (g : s.ACSym) (u : Term s) :
    cls (flatten g u) = Cancellation.flatten g u :=
  (Rewriting.DHProduct.classes g u).symm

theorem keep_perm (eq : Term s → Term s → Bool) (limit : Term s → Nat) (kept xs : List (Term s)) :
    (kept ++ xs).Perm ((keep eq limit kept xs).1 ++ (keep eq limit kept xs).2) := by
  induction xs generalizing kept with
  | nil => simp [keep]
  | cons x xs ih =>
    simp only [keep]
    split
    · exact List.perm_middle.trans (ih (x :: kept))
    · exact List.perm_middle.trans (((ih kept).cons x).trans List.perm_middle.symm)

open Classical in
theorem countP_class {eq : Term s → Term s → Bool} (heq : ∀ a b, eq a b = true ↔ EquivB a b)
    (x : Term s) (zs : List (Term s)) : zs.countP (eq x) = (cls zs).count (classOf x) := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    simp only [List.countP_cons, List.map_cons, List.count_cons, ih]
    congr 1
    by_cases hit : eq x z = true
    · have e : classOf z = classOf x := Quotient.sound ((heq x z).mp hit).symm
      simp [hit, e]
    · have ne : classOf z ≠ classOf x := fun e => hit ((heq x z).mpr (Quotient.exact e.symm))
      simp [hit, ne]

open Classical in
theorem count_cons_cls (x : Term s) (ys : List (Term s)) (c : Cancellation.Class s) :
    (cls (x :: ys)).count c = (cls ys).count c + if classOf x = c then 1 else 0 := by
  simp only [List.map_cons, List.count_cons, beq_iff_eq]

open Classical in
/-- A class keeps `n` operands when the limit allows `n` and the bag has them. -/
theorem keep_ge {eq : Term s → Term s → Bool} (heq : ∀ a b, eq a b = true ↔ EquivB a b)
    (limit : Term s → Nat) (c : Cancellation.Class s) (n : Nat)
    (low : ∀ x, classOf x = c → n ≤ limit x) (kept xs : List (Term s))
    (present : n ≤ (cls kept).count c + (cls xs).count c) :
    n ≤ (cls (keep eq limit kept xs).1).count c := by
  induction xs generalizing kept with
  | nil => simpa [keep] using present
  | cons x xs ih =>
    rw [count_cons_cls] at present
    simp only [keep, countP_class heq]
    split
    · apply ih
      rw [count_cons_cls]
      omega
    · next full =>
      apply ih
      by_cases here : classOf x = c
      · have := low x here
        rw [here] at full
        omega
      · rw [ite_eq_right here] at present
        omega

open Classical in
/-- A class keeps at most `n` operands when the limit stays within `n`. -/
theorem keep_le {eq : Term s → Term s → Bool} (heq : ∀ a b, eq a b = true ↔ EquivB a b)
    (limit : Term s → Nat) (c : Cancellation.Class s) (n : Nat)
    (high : ∀ x, classOf x = c → limit x ≤ n) (kept xs : List (Term s))
    (start : (cls kept).count c ≤ n) : (cls (keep eq limit kept xs).1).count c ≤ n := by
  induction xs generalizing kept with
  | nil => simpa [keep] using start
  | cons x xs ih =>
    simp only [keep, countP_class heq]
    split
    · next fits =>
      apply ih
      rw [count_cons_cls]
      by_cases here : classOf x = c
      · have := high x here
        rw [here] at fits
        rw [ite_eq_left here]
        omega
      · rw [ite_eq_right here]
        exact start
    · exact ih kept start

open Classical in
/-- A count within every recorded bound is not lowered. -/
theorem capped_ge {eq : Term s → Term s → Bool} (heq : ∀ a b, eq a b = true ↔ EquivB a b)
    (bounds : List (Bound s)) (x : Term s) (i n : Nat)
    (fit : ∀ b ∈ bounds, b.k ≠ 0 ∧ b.k * i ≤ (cls b.bag).count (classOf x)) (h : i ≤ n) :
    i ≤ capped eq bounds x n := by
  unfold capped
  induction bounds generalizing n with
  | nil => exact h
  | cons b bounds ih =>
    rw [List.foldl_cons]
    refine ih _ (fun b hb => fit b (List.mem_cons_of_mem _ hb)) ?_
    obtain ⟨pos, within⟩ := fit b List.mem_cons_self
    refine Nat.le_min.mpr ⟨h, (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero pos)).mpr ?_⟩
    rw [countP_class heq, Nat.mul_comm]
    exact within

theorem pool_perm (eq : Term s → Term s → Bool) (bounds : List (Bound s)) (k : Nat)
    (zs : List (Term s)) : zs.Perm ((pool eq bounds k zs).1 ++ (pool eq bounds k zs).2) := by
  unfold pool
  split
  · simp
  · exact keep_perm eq _ [] zs

open Classical in
/-- An image that the bag supplies `k` times within the recorded bounds lies
inside the pool. -/
theorem pool_cover {eq : Term s → Term s → Bool} (heq : ∀ a b, eq a b = true ↔ EquivB a b)
    (bounds : List (Bound s)) (k : Nat) (hk : 0 < k) (zs : List (Term s))
    (image : List (Cancellation.Class s))
    (fit : ∀ b ∈ bounds, ∀ c, b.k ≠ 0 ∧ b.k * image.count c ≤ (cls b.bag).count c)
    (enough : ∀ c, image.count c * k ≤ (cls zs).count c) (c : Cancellation.Class s) :
    image.count c ≤ (cls (pool eq bounds k zs).1).count c := by
  have once : image.count c ≤ (cls zs).count c :=
    Nat.le_trans (Nat.le_mul_of_pos_right _ hk) (enough c)
  unfold pool
  split
  · exact once
  · apply keep_ge heq _ c
    · intro x here
      apply capped_ge heq _ _ _ _ (fun b hb => here ▸ fit b hb c)
      rw [countP_class heq, here]
      exact (Nat.le_div_iff_mul_le hk).mpr (enough c)
    · simpa using once

theorem forced_perm (eq : Term s → Term s → Bool) (spare : Bool) (k : Nat)
    (others : List (Nat × List (Bound s))) (zs pool : List (Term s)) :
    pool.Perm ((forced eq spare k others zs pool).1 ++ (forced eq spare k others zs pool).2) := by
  unfold forced
  split
  · simp
  · exact keep_perm eq _ [] pool

open Classical in
/-- The forced operands lie inside an image that takes, `k` times, every copy
the other occurrences cannot. -/
theorem forced_le {eq : Term s → Term s → Bool} (heq : ∀ a b, eq a b = true ↔ EquivB a b)
    (spare : Bool) (k : Nat) (hk : 0 < k) (others : List (Nat × List (Bound s)))
    (zs pool : List (Term s)) (image : List (Cancellation.Class s))
    (need : spare = false → ∀ x, zs.countP (eq x) - absorbed eq others (zs.countP (eq x)) x ≤
      k * image.count (classOf x)) (c : Cancellation.Class s) :
    (cls (forced eq spare k others zs pool).1).count c ≤ image.count c := by
  unfold forced
  split
  · simp
  · next closed =>
    have off : spare = false := by
      cases spare
      · rfl
      · simp at closed
    apply keep_le heq _ c _ _ _ _ (by simp)
    intro x here
    have := need off x
    rw [here] at this
    exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by
      rw [Nat.mul_succ]
      omega))

theorem exists_perm_of_count_le {β : Type} [DecidableEq β] (A L : List β)
    (h : ∀ c, A.count c ≤ L.count c) : ∃ B, L.Perm (A ++ B) := by
  induction A generalizing L with
  | nil => exact ⟨L, .refl _⟩
  | cons a A ih =>
    have inL : a ∈ L := List.count_pos_iff.mp (by
      have := h a
      rw [List.count_cons_self] at this
      omega)
    obtain ⟨B, hB⟩ := ih (L.erase a) (fun c => by
      have := h c
      rw [List.count_cons] at this
      rw [List.count_erase]
      by_cases same : (a == c) = true
      · rw [ite_eq_left same] at this ⊢
        omega
      · rw [ite_eq_right same] at this ⊢
        omega)
    exact ⟨B, (List.perm_cons_erase inL).trans (hB.cons a)⟩

open Classical in
theorem pend_count (ctx : Option s.ACSym) (σ : Substitution s) (v : Variable) (vs : List Variable)
    (c : Cancellation.Class s) :
    vs.count v * (opsC ctx (σ.image v)).count c ≤ (pend ctx σ vs).count c := by
  induction vs with
  | nil => simp
  | cons w vs ih =>
    rw [pend_cons, List.count_append]
    by_cases same : w = v
    · subst same
      rw [List.count_cons_self, Nat.add_mul, Nat.one_mul]
      omega
    · rw [List.count_cons_of_ne same]
      omega

open Classical in
/-- The classes owed to the occurrences of one variable, and to the others. -/
theorem pend_split (ctx : Option s.ACSym) (σ : Substitution s) (v : Variable) (vs : List Variable)
    (c : Cancellation.Class s) :
    (pend ctx σ vs).count c =
      vs.count v * (opsC ctx (σ.image v)).count c + (pend ctx σ (vs.filter (· != v))).count c := by
  induction vs with
  | nil => simp [pend]
  | cons w vs ih =>
    rw [pend_cons, List.count_append, ih]
    by_cases same : w = v
    · subst same
      rw [List.count_cons_self, Nat.add_mul, Nat.one_mul, List.filter_cons_of_neg (by simp)]
      omega
    · rw [List.count_cons_of_ne same, List.filter_cons_of_pos (by simpa using same), pend_cons,
        List.count_append]
      omega

theorem pend_length (ctx : Option s.ACSym) (σ : Substitution s) (v : Variable) (vs : List Variable) :
    (pend ctx σ vs).length =
      vs.count v * (opsC ctx (σ.image v)).length + (pend ctx σ (vs.filter (· != v))).length := by
  induction vs with
  | nil => simp [pend]
  | cons w vs ih =>
    rw [pend_cons, List.length_append, ih]
    by_cases same : w = v
    · subst same
      rw [List.count_cons_self, Nat.add_mul, Nat.one_mul, List.filter_cons_of_neg (by simp)]
      omega
    · rw [List.count_cons_of_ne same, List.filter_cons_of_pos (by simpa using same), pend_cons,
        List.length_append]
      omega

/-- Every waiting occurrence is owed at least one operand. -/
theorem pend_long (g : s.ACSym) (σ : Substitution s) (vs : List Variable) :
    vs.length ≤ (pend (some g) σ vs).length := by
  induction vs with
  | nil => simp
  | cons w vs ih =>
    rw [pend_cons, List.length_append, List.length_cons]
    have some_ : 0 < (opsC (some g) (σ.image w)).length := by
      apply List.length_pos_iff.mpr
      intro e
      have folded := Cancellation.fold_flatten g (σ.image w)
      change Cancellation.flatten g (σ.image w) = [] at e
      rw [e] at folded
      cases folded
    omega

open Classical in
theorem pend_le_sum (ctx : Option s.ACSym) (σ : Substitution s) (c : Cancellation.Class s)
    (ws : List Variable) (bound : Variable → Nat)
    (h : ∀ w ∈ ws, (opsC ctx (σ.image w)).count c ≤ bound w) :
    (pend ctx σ ws).count c ≤ (ws.map bound).sum := by
  induction ws with
  | nil => simp [pend]
  | cons w ws ih =>
    rw [pend_cons, List.count_append, List.map_cons, List.sum_cons]
    have := h w List.mem_cons_self
    have := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
    omega

theorem decode_classes (g : s.ACSym) {zs : List (Term s)} {t : Term s} (dec : decode g zs = some t)
    (flat : Flat (some g) zs) : Cancellation.flatten g t = cls zs := by
  cases zs with
  | nil => simp [decode] at dec
  | cons a as =>
    simp only [decode, Option.some.injEq] at dec
    subst t
    exact flatC_fold g a as flat

open Classical in
/-- Every recorded bound holds for the images of a substitution. -/
def Fits (tab : List (Bound s)) (σ : Substitution s) : Prop :=
  ∀ b ∈ tab, ∀ c, b.k * (Cancellation.flatten b.g (σ.image b.v)).count c ≤ (cls b.bag).count c

theorem fits_nil (σ : Substitution s) : Fits [] σ := fun _ hb => nomatch hb

section
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

theorem same_class (a b : Term s) (h : same a b = true) : classOf a = classOf b := by
  rw [of_decide_eq_true h]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] in
theorem mem_mine {tab : List (Bound s)} {g : s.ACSym} {v : Variable} {b : Bound s}
    (h : b ∈ mine tab g v) : b ∈ tab ∧ b.g = g ∧ b.v = v ∧ b.k ≠ 0 := by
  obtain ⟨hb, ok⟩ := List.mem_filter.mp h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne] at ok
  exact ⟨hb, ok.1.1, ok.1.2, ok.2⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] in
open Classical in
theorem fits_mine {tab : List (Bound s)} {σ : Substitution s} (fits : Fits tab σ) (g : s.ACSym)
    (v : Variable) : ∀ b ∈ mine tab g v, ∀ c,
      b.k ≠ 0 ∧ b.k * (Cancellation.flatten g (σ.image v)).count c ≤ (cls b.bag).count c := by
  intro b hb c
  obtain ⟨inside, rfl, rfl, pos⟩ := mem_mine hb
  exact ⟨pos, fits b inside c⟩

theorem share_sound {eq : Term s → Term s → Bool} (heq : ∀ a b, eq a b = true → EquivB a b)
    (σ : Substitution s) (tab : List (Bound s)) (g : s.ACSym) (spare : Bool) (acc : Requirements s)
    (vs : List Variable) (zs : List (Term s)) {out : Requirements s × List (Term s)}
    (m : out ∈ share eq tab g spare acc vs zs) (ha : holds σ acc) (hr : holds σ out.1)
    (flat : Flat (some g) zs) :
    (cls zs).Perm (pend (some g) σ vs ++ cls out.2) ∧ (out.2 = [] ↔ spare = false) := by
  induction vs generalizing acc zs out with
  | nil =>
    simp only [share] at m
    split at m
    · contradiction
    · next open_ =>
      obtain rfl := List.mem_singleton.mp m
      refine ⟨by simp [pend], ?_⟩
      cases spare <;> cases zs <;> simp_all
  | cons v vs ih =>
    rw [pend_cons, List.append_assoc]
    simp only [share] at m
    split at m
    · next u look =>
      split at m
      · next r taken =>
        have known : (Cancellation.flatten g (σ.image v)).Perm (cls (flatten g u)) := by
          rw [cls_flatten]
          exact Cancellation.flatten_equiv g (ha v u (lookup_mem look))
        obtain ⟨rest, done⟩ := ih acc r m ha hr (flat.of_subset (takeAll_subset taken))
        exact ⟨(takeAll_sound heq taken).trans (known.symm.append rest), done⟩
      · contradiction
    · split at m
      · next last =>
        obtain ⟨closed, final⟩ : spare = false ∧ vs = [] := by simpa using last
        subst closed final
        split at m
        · next t dec =>
          split at m
          · obtain rfl := List.mem_singleton.mp m
            have img := hr v t List.mem_cons_self
            have shape := decode_classes g dec flat
            simp only [pend, List.flatMap_nil, List.map_nil, List.append_nil]
            exact ⟨shape ▸ (Cancellation.flatten_equiv g img).symm, by simp⟩
          · contradiction
        · contradiction
      · split at m
        · contradiction
        · obtain ⟨⟨l, r⟩, part, inner⟩ := List.mem_flatMap.mp m
          have split := sub_sound same _ _ _ part
          have pooled := pool_perm eq (mine tab g v) (vs.count v + 1) zs
          have must := forced_perm eq spare (vs.count v + 1)
            ((vs.filter (· != v)).map fun w => ((vs.filter (· != v)).count w, mine tab g w)) zs
            (pool eq (mine tab g v) (vs.count v + 1) zs).1
          dsimp only at inner
          split at inner
          · next t dec =>
            split at inner
            · obtain ⟨later, hlater, rfl⟩ := List.mem_map.mp inner
              have img := hr v t List.mem_cons_self
              have tail : holds σ later.1 := fun w u hm => hr w u (List.mem_cons_of_mem _ hm)
              have all := pooled.trans ((must.trans (split.append_left _)).append_right _)
              rw [← List.append_assoc, List.append_assoc] at all
              have fl := flat.of_subset fun y hy => all.mem_iff.mpr (List.mem_append_left _ hy)
              have fr := flat.of_subset fun y hy => all.mem_iff.mpr (List.mem_append_right _ hy)
              have grown : holds σ ((v, t) :: acc) := fun w u hm =>
                (List.mem_cons.mp hm).elim (fun e => by cases e; exact img) (ha w u)
              have left := decode_classes g dec fl ▸ (Cancellation.flatten_equiv g img).symm
              have whole := all.map classOf
              simp only [List.map_append] at whole
              obtain ⟨rest, done⟩ := ih _ _ hlater grown tail fr
              simp only [cls, List.map_append] at left rest ⊢
              exact ⟨whole.trans (left.append rest), done⟩
            · contradiction
          · contradiction

theorem share_complete {eq : Term s → Term s → Bool} (heq : ∀ a b, eq a b = true ↔ EquivB a b)
    (σ : Substitution s) (tab : List (Bound s)) (fits : Fits tab σ) (g : s.ACSym) (spare : Bool)
    (acc : Requirements s) (vs : List Variable)
    (zs : List (Term s)) (ha : holds σ acc) {W : List (Cancellation.Class s)}
    (h : (cls zs).Perm (pend (some g) σ vs ++ W)) (hw : W = [] ↔ spare = false) :
    ∃ out ∈ share eq tab g spare acc vs zs, holds σ out.1 ∧ (cls out.2).Perm W := by
  classical
  induction vs generalizing acc zs with
  | nil =>
    have h' : (cls zs).Perm W := by simpa [pend] using h
    have empty : zs = [] ↔ W = [] :=
      ⟨fun z => by subst z; exact (List.nil_perm.mp h'), fun w => by subst w; simpa using h'⟩
    refine ⟨([], zs), ?_, ?_, h'⟩
    · simp only [share]
      cases spare <;> cases zs <;> simp_all
    · intro _ _ hm
      cases hm
  | cons v vs ih =>
    rw [pend_cons, List.append_assoc] at h
    change (cls zs).Perm (Cancellation.flatten g (σ.image v) ++ _) at h
    simp only [share]
    split
    · next u look =>
      have known : (Cancellation.flatten g (σ.image v)).Perm (cls (flatten g u)) := by
        rw [cls_flatten]
        exact Cancellation.flatten_equiv g (ha v u (lookup_mem look))
      obtain ⟨r, taken, pr⟩ := takeAll_complete heq (h.trans (known.append_right _))
      simp only [taken]
      exact ih acc r ha pr
    · have sorted := Term.checkSort_complete (σ.sorted v)
      split
      · next last =>
        obtain ⟨closed, final⟩ : spare = false ∧ vs = [] := by simpa using last
        subst closed final
        obtain rfl := hw.mpr rfl
        simp only [pend, List.flatMap_nil, List.append_nil] at h
        obtain ⟨t, dec, img⟩ := decode_of_perm g h
        have ok : t.checkSort v.sort = true := SortClash.check_equiv img v.sort ▸ sorted
        refine ⟨([(v, t)], []), by simp [dec, ok], ?_, .nil⟩
        intro w u hm
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp hm)
        exact img
      · generalize hI : Cancellation.flatten g (σ.image v) = image at h
        generalize hos : vs.filter (· != v) = others
        have hk : 0 < vs.count v + 1 := Nat.succ_pos _
        -- What the bag holds of each class.
        have total (c : Cancellation.Class s) : (cls zs).count c =
            (vs.count v + 1) * image.count c + (pend (some g) σ others).count c + W.count c := by
          have := h.count_eq c
          rw [List.count_append, List.count_append, pend_split (some g) σ v vs c, hos] at this
          change _ = _ + (_ * (Cancellation.flatten g (σ.image v)).count c + _ + _) at this
          rw [hI] at this
          rw [this, Nat.add_mul, Nat.one_mul]
          omega
        have size : zs.length =
            (vs.count v + 1) * image.length + (pend (some g) σ others).length + W.length := by
          have := h.length_eq
          rw [List.length_append, List.length_append, pend_length (some g) σ v vs, hos] at this
          change _ = _ + (_ * (Cancellation.flatten g (σ.image v)).length + _ + _) at this
          rw [hI, List.length_map] at this
          rw [this, Nat.add_mul, Nat.one_mul]
          omega
        have enough (c : Cancellation.Class s) :
            image.count c * (vs.count v + 1) ≤ (cls zs).count c := by
          rw [total c, Nat.mul_comm]
          omega
        have inside := pool_cover heq (mine tab g v) _ hk zs image
          (fun b hb c => hI ▸ fits_mine fits g v b hb c) enough
        have pooled := pool_perm eq (mine tab g v) (vs.count v + 1) zs
        generalize pool eq (mine tab g v) (vs.count v + 1) zs = pool at inside pooled
        have must := forced_perm eq spare (vs.count v + 1)
          (others.map fun w => (others.count w, mine tab g w)) zs pool.1
        have least := forced_le heq spare (vs.count v + 1) hk
          (others.map fun w => (others.count w, mine tab g w)) zs pool.1 image (by
            intro closed x
            obtain rfl := hw.mpr closed
            have all := total (classOf x)
            rw [countP_class heq]
            have taken : (pend (some g) σ others).count (classOf x) ≤
                absorbed eq (others.map fun w => (others.count w, mine tab g w))
                  ((cls zs).count (classOf x)) x := by
              unfold absorbed
              rw [List.map_map]
              apply pend_le_sum
              intro w hw
              apply capped_ge heq _ _ _ _ (fun b hb => fits_mine fits g w b hb _)
              have many : 0 < others.count w := List.count_pos_iff.mpr hw
              apply (Nat.le_div_iff_mul_le many).mpr
              have := pend_count (some g) σ w others (classOf x)
              change others.count w * (Cancellation.flatten g (σ.image w)).count (classOf x) ≤ _ at this
              rw [Nat.mul_comm]
              omega
            simp only [List.count_nil, Nat.add_zero] at all
            omega)
        generalize forced eq spare (vs.count v + 1)
          (others.map fun w => (others.count w, mine tab g w)) zs pool.1 = must_ at must least
        obtain ⟨A, hA⟩ := exists_perm_of_count_le (cls must_.1) image least
        have may (c : Cancellation.Class s) : A.count c ≤ (cls must_.2).count c := by
          have a := hA.count_eq c
          have b := (must.map classOf).count_eq c
          have := inside c
          simp only [cls, List.map_append, List.count_append] at a b this ⊢
          omega
        obtain ⟨B, hB⟩ := exists_perm_of_count_le A (cls must_.2) may
        have long : image.length = must_.1.length + A.length := by
          simpa using hA.length_eq
        have fitsRoom : image.length ≤
            room g v spare (vs.count v + 1) others.length zs.length := by
          unfold room
          split
          · apply (Nat.le_div_iff_mul_le hk).mpr
            have := pend_long g σ others
            have left : (if spare = true then 1 else 0) ≤ W.length := by
              cases spare
              · simp
              · have : W ≠ [] := fun e => by simpa using hw.mp e
                simp only [ite_true]
                exact List.length_pos_iff.mpr this
            rw [size, Nat.mul_comm]
            omega
          · next narrow =>
            apply Nat.le_of_not_lt
            intro many
            obtain ⟨a, b, shape⟩ := ac_of_operands g _ (hI ▸ many)
            rw [shape] at sorted
            simp only [Term.checkSort, Bool.and_eq_true] at sorted
            exact narrow sorted.1.1
        rw [ite_eq_right (by omega)]
        obtain ⟨l, r, part, pl, pr⟩ := sub_complete same classOf same_class
          (room g v spare (vs.count v + 1) others.length zs.length - must_.1.length) [] must_.2
          hB (fun _ hb => nomatch hb) (by omega)
        have whole : (cls (must_.1 ++ l)).Perm (Cancellation.flatten g (σ.image v)) := by
          rw [hI]
          simp only [cls, List.map_append]
          exact (pl.append_left _).trans hA.symm
        obtain ⟨t, dec, img⟩ := decode_of_perm g whole
        have ok : t.checkSort v.sort = true := SortClash.check_equiv img v.sort ▸ sorted
        have grown : holds σ ((v, t) :: acc) := fun w u hm =>
          (List.mem_cons.mp hm).elim (fun e => by cases e; exact img) (ha w u)
        have remainder : (cls (r ++ pool.2)).Perm (pend (some g) σ vs ++ W) := by
          have all := (pooled.trans (must.append_right _)).map classOf
          simp only [List.map_append] at all
          have regroup : (cls must_.1 ++ cls must_.2 ++ cls pool.2).Perm
              (image ++ (B ++ cls pool.2)) := by
            have x := (hB.append_left (cls must_.1)).append_right (cls pool.2)
            have y := (hA.symm.append_right B).append_right (cls pool.2)
            simp only [List.append_assoc] at x y ⊢
            exact x.trans y
          have both := h.symm.trans (all.trans regroup)
          have rest := (List.perm_append_left_iff _).mp both
          simp only [cls, List.map_append]
          exact (pr.append_right _).trans rest.symm
        obtain ⟨later, hlater, sat, pw⟩ := ih _ _ grown remainder
        refine ⟨((v, t) :: later.1, later.2), List.mem_flatMap.mpr ⟨(l, r), part, ?_⟩, ?_, pw⟩
        · simp only [dec, ok, ite_true]
          exact List.mem_map.mpr ⟨later, hlater, rfl⟩
        · intro w u hm
          exact (List.mem_cons.mp hm).elim (fun e => by cases e; exact img) (sat w u)

theorem share_mentions {eq : Term s → Term s → Bool} (tab : List (Bound s)) (g : s.ACSym)
    (spare : Bool) (acc : Requirements s) (vs : List Variable) (zs : List (Term s))
    {out : Requirements s × List (Term s)} (m : out ∈ share eq tab g spare acc vs zs) {w : Variable}
    (hw : w ∈ vs) : (∃ t, (w, t) ∈ out.1) ∨ ∃ u, (w, u) ∈ acc := by
  induction vs generalizing acc zs out with
  | nil => contradiction
  | cons v vs ih =>
    simp only [share] at m
    split at m
    · next u look =>
      split at m
      · rcases List.mem_cons.mp hw with rfl | later
        · exact .inr ⟨u, lookup_mem look⟩
        · exact ih acc _ m later
      · contradiction
    · split at m
      · next last =>
        obtain ⟨_, final⟩ : spare = false ∧ vs = [] := by simpa using last
        subst final
        obtain rfl : w = v := by simpa using hw
        split at m
        · split at m
          · obtain rfl := List.mem_singleton.mp m
            exact .inl ⟨_, List.mem_cons_self⟩
          · contradiction
        · contradiction
      · split at m
        · contradiction
        · obtain ⟨⟨l, r⟩, _, inner⟩ := List.mem_flatMap.mp m
          dsimp only at inner
          split at inner
          · next t _ =>
            split at inner
            · obtain ⟨later, hlater, rfl⟩ := List.mem_map.mp inner
              rcases List.mem_cons.mp hw with rfl | further
              · exact .inl ⟨t, List.mem_cons_self⟩
              · rcases ih _ _ hlater further with ⟨u, hu⟩ | ⟨u, hu⟩
                · exact .inl ⟨u, List.mem_cons_of_mem _ hu⟩
                · rcases List.mem_cons.mp hu with e | old
                  · cases e
                    exact .inl ⟨_, List.mem_cons_self⟩
                  · exact .inr ⟨u, old⟩
            · contradiction
          · contradiction

/-- A requirement is recorded only for a waiting variable and fits its sort. -/
theorem share_entries {eq : Term s → Term s → Bool} (tab : List (Bound s)) (g : s.ACSym)
    (spare : Bool) (acc : Requirements s) (vs : List Variable) (zs : List (Term s))
    {out : Requirements s × List (Term s)} (m : out ∈ share eq tab g spare acc vs zs) {v : Variable}
    {t : Term s} (h : (v, t) ∈ out.1) : v ∈ vs ∧ t.checkSort v.sort = true := by
  induction vs generalizing acc zs out with
  | nil =>
    simp only [share] at m
    split at m
    · contradiction
    · obtain rfl := List.mem_singleton.mp m
      contradiction
  | cons w vs ih =>
    simp only [share] at m
    split at m
    · split at m
      · exact ⟨List.mem_cons_of_mem _ (ih acc _ m h).1, (ih acc _ m h).2⟩
      · contradiction
    · split at m
      · split at m
        · split at m
          · next ok =>
            obtain rfl := List.mem_singleton.mp m
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp h)
            exact ⟨List.mem_cons_self, ok⟩
          · contradiction
        · contradiction
      · split at m
        · contradiction
        · obtain ⟨⟨l, r⟩, _, inner⟩ := List.mem_flatMap.mp m
          dsimp only at inner
          split at inner
          · split at inner
            · next ok =>
              obtain ⟨later, hlater, rfl⟩ := List.mem_map.mp inner
              rcases List.mem_cons.mp h with e | further
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
                exact ⟨List.mem_cons_self, ok⟩
              · exact ⟨List.mem_cons_of_mem _ (ih _ _ hlater further).1, (ih _ _ hlater further).2⟩
            · contradiction
          · contradiction

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem order_perm (g : s.ACSym) (acc : Requirements s) (vs : List Variable) :
    (order g acc vs).Perm vs := by
  unfold order
  exact ((List.filter_append_perm _ _).append_left _).trans (List.filter_append_perm _ _)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem pend_perm (ctx : Option s.ACSym) (σ : Substitution s) {us vs : List Variable}
    (h : us.Perm vs) : (pend ctx σ us).Perm (pend ctx σ vs) :=
  h.flatMap_right _

theorem dist_sound {eq : Term s → Term s → Bool} (heq : ∀ a b, eq a b = true → EquivB a b)
    (σ : Substitution s) (tab : List (Bound s)) (g : s.ACSym) (acc : Requirements s)
    (vs : List Variable)
    (zs : List (Term s)) {row : Requirements s} (m : row ∈ dist eq tab g acc vs zs)
    (ha : holds σ acc) (hr : holds σ row) (flat : Flat (some g) zs) :
    (cls zs).Perm (pend (some g) σ vs) := by
  obtain ⟨out, hout, rfl⟩ := List.mem_map.mp m
  obtain ⟨all, none_⟩ := share_sound heq σ tab g false acc _ zs hout ha hr flat
  exact (by simpa [none_.mpr rfl] using all : (cls zs).Perm _).trans
    (pend_perm _ σ (order_perm g acc vs))

theorem dist_complete {eq : Term s → Term s → Bool} (heq : ∀ a b, eq a b = true ↔ EquivB a b)
    (σ : Substitution s) (tab : List (Bound s)) (fits : Fits tab σ) (g : s.ACSym)
    (acc : Requirements s) (vs : List Variable)
    (zs : List (Term s)) (ha : holds σ acc) (h : (cls zs).Perm (pend (some g) σ vs)) :
    ∃ row ∈ dist eq tab g acc vs zs, holds σ row := by
  obtain ⟨out, hout, sat, _⟩ := share_complete heq σ tab fits g false acc (order g acc vs) zs ha
    (W := []) (by simpa using h.trans (pend_perm _ σ (order_perm g acc vs)).symm) (by simp)
  exact ⟨out.1, List.mem_map.mpr ⟨out, hout, rfl⟩, sat⟩

theorem dist_mentions {eq : Term s → Term s → Bool} (tab : List (Bound s)) (g : s.ACSym)
    (acc : Requirements s)
    (vs : List Variable) (zs : List (Term s)) {row : Requirements s}
    (m : row ∈ dist eq tab g acc vs zs) {w : Variable} (hw : w ∈ vs) :
    (∃ t, (w, t) ∈ row) ∨ ∃ u, (w, u) ∈ acc := by
  obtain ⟨out, hout, rfl⟩ := List.mem_map.mp m
  exact share_mentions tab g false acc _ zs hout ((order_perm g acc vs).mem_iff.mpr hw)

theorem dist_entries {eq : Term s → Term s → Bool} (tab : List (Bound s)) (g : s.ACSym)
    (acc : Requirements s)
    (vs : List Variable) (zs : List (Term s)) {row : Requirements s}
    (m : row ∈ dist eq tab g acc vs zs) {v : Variable} {t : Term s} (h : (v, t) ∈ row) :
    v ∈ vs ∧ t.checkSort v.sort = true := by
  obtain ⟨out, hout, rfl⟩ := List.mem_map.mp m
  obtain ⟨waits, ok⟩ := share_entries tab g false acc _ zs hout h
  exact ⟨(order_perm g acc vs).mem_iff.mp waits, ok⟩

theorem mem_operand {xs : List (Term s)} {single : Term s → List (Requirements s)} {part : Partial s} :
    part ∈ operand xs single ↔
      ∃ x r, (x, r) ∈ picks same xs ∧ ∃ row ∈ single x, part = (row, r, []) := by
  simp only [operand, List.mem_flatMap, List.mem_map, Prod.exists]
  constructor
  · rintro ⟨x, r, hp, row, hr, rfl⟩
    exact ⟨x, r, hp, row, hr, rfl⟩
  · rintro ⟨x, r, hp, row, hr, rfl⟩
    exact ⟨x, r, hp, row, hr, rfl⟩

/-- A pattern that is one operand of its context removes one subject operand
of its own class. Completeness may rest on a side condition. -/
theorem operand_spec (side : Prop) (σ : Substitution s) (q : Term s) (ctx : Option s.ACSym)
    (xs : List (Term s)) (single : Term s → List (Requirements s)) (one : opsC ctx q = [classOf q])
    (sound : ∀ x, accepts σ (single x) → EquivB q x)
    (complete : side → ∀ x, EquivB q x → accepts σ (single x)) :
    (∀ part ∈ operand xs single, holds σ part.1 →
      (Flat ctx xs → Flat ctx part.2.1) ∧
        (cls xs ++ pend ctx σ part.2.2).Perm (opsC ctx q ++ cls part.2.1)) ∧
    (side → ∀ W, (cls xs).Perm (opsC ctx q ++ W) →
      ∃ part ∈ operand xs single, holds σ part.1 ∧
        (cls part.2.1).Perm (pend ctx σ part.2.2 ++ W)) := by
  rw [one]
  constructor
  · intro part m sat
    obtain ⟨x, r, hp, row, hr, rfl⟩ := mem_operand.mp m
    have split := picks_sound same xs hp
    have e : classOf x = classOf q := Quotient.sound (sound x ⟨row, hr, sat⟩).symm
    refine ⟨fun fl => fl.of_subset fun y hy => split.mem_iff.mpr (List.mem_cons_of_mem _ hy), ?_⟩
    have whole : (cls xs).Perm (classOf x :: cls r) := by simpa [cls] using split.map classOf
    simpa [pend, e] using whole
  · intro ok W h
    obtain ⟨x, r, hp, e, rest⟩ := picks_complete same classOf same_class xs h
    obtain ⟨row, hr, sat⟩ := complete ok x (Quotient.exact e.symm)
    exact ⟨(row, r, []), mem_operand.mpr ⟨x, r, hp, row, hr, rfl⟩, sat, by simpa [pend] using rest⟩

theorem operand_iff (side : Prop) (σ : Substitution s) (q : Term s) (ctx : Option s.ACSym)
    (xs : List (Term s)) (single : Term s → List (Requirements s)) (one : opsC ctx q = [classOf q])
    (iff : ∀ x, accepts σ (single x) ↔ EquivB q x) :
    (∀ part ∈ operand xs single, holds σ part.1 →
      (Flat ctx xs → Flat ctx part.2.1) ∧
        (cls xs ++ pend ctx σ part.2.2).Perm (opsC ctx q ++ cls part.2.1)) ∧
    (side → ∀ W, (cls xs).Perm (opsC ctx q ++ W) →
      ∃ part ∈ operand xs single, holds σ part.1 ∧
        (cls part.2.1).Perm (pend ctx σ part.2.2 ++ W)) :=
  operand_spec side σ q ctx xs single one (fun x => (iff x).mp) (fun _ x => (iff x).mpr)

/-- What `go` removes is exactly the pattern instance, up to the operands
still owed to waiting variables. Every branch that a substitution satisfies
removes its instance. A substitution within the recorded bounds finds a
branch for each way of removing its instance. -/
def Spec (tab : List (Bound s)) (bind : Variable → Bool) (eq : Term s → Term s → Bool)
    (σ : Substitution s) (p : Term s) : Prop :=
  ∀ ctx xs,
    (∀ part ∈ go tab bind eq p ctx xs, holds σ part.1 →
      (Flat ctx xs → Flat ctx part.2.1) ∧
        (cls xs ++ pend ctx σ part.2.2).Perm (opsC ctx (σ.apply p) ++ cls part.2.1)) ∧
    (Fits tab σ → ∀ W, (cls xs).Perm (opsC ctx (σ.apply p) ++ W) →
      ∃ part ∈ go tab bind eq p ctx xs, holds σ part.1 ∧
        (cls part.2.1).Perm (pend ctx σ part.2.2 ++ W))

theorem pending_none (tab : List (Bound s)) (bind : Variable → Bool) (eq : Term s → Term s → Bool)
    (p : Term s) (xs : List (Term s)) : ∀ part ∈ go tab bind eq p none xs, part.2.2 = [] := by
  intro part m
  have op {single} (m : part ∈ operand xs single) : part.2.2 = [] := by
    obtain ⟨x, r, _, row, _, rfl⟩ := mem_operand.mp m
    rfl
  cases p with
  | var v =>
    simp only [go] at m
    split at m <;> exact op m
  | atom a => exact op (by simpa only [go] using m)
  | free f ps => exact op (by simpa only [go] using m)
  | comm f a b => exact op (by simpa only [go] using m)
  | ac g a b =>
    simp only [go, reduceCtorEq, ite_false] at m
    exact op m

theorem single_sound {tab : List (Bound s)} {bind : Variable → Bool} {eq : Term s → Term s → Bool}
    {σ : Substitution s} {p : Term s} (h : Spec tab bind eq σ p) (x : Term s)
    (found : accepts σ ((go tab bind eq p none [x]).filterMap finish)) : EquivB (σ.apply p) x := by
  obtain ⟨row, m, sat⟩ := found
  obtain ⟨part, hp, fin⟩ := List.mem_filterMap.mp m
  obtain rfl := finish_eq.mp fin
  have removed := ((h none [x]).1 _ hp sat).2
  have one : [classOf x].Perm [classOf (σ.apply p)] := by simpa [pend, opsC] using removed
  exact Quotient.exact (List.cons.inj (List.singleton_perm.mp one)).1.symm

theorem single_complete {tab : List (Bound s)} {bind : Variable → Bool}
    {eq : Term s → Term s → Bool} {σ : Substitution s} {p : Term s} (h : Spec tab bind eq σ p)
    (fits : Fits tab σ) (x : Term s) (e : EquivB (σ.apply p) x) :
    accepts σ ((go tab bind eq p none [x]).filterMap finish) := by
  have start : (cls [x]).Perm (opsC none (σ.apply p) ++ []) := by
    have same : classOf x = classOf (σ.apply p) := Quotient.sound e.symm
    simp [opsC, same]
  obtain ⟨⟨row, ys, vs⟩, hp, sat, rest⟩ := (h none [x]).2 fits [] start
  have none_ : vs = [] := pending_none tab bind eq p [x] _ hp
  subst none_
  have done : ys = [] := by simpa [pend] using rest
  subst done
  exact ⟨row, List.mem_filterMap.mpr ⟨_, hp, rfl⟩, sat⟩

theorem spec {tab : List (Bound s)} {bind : Variable → Bool} {eq : Term s → Term s → Bool}
    (heq : ∀ a b, eq a b = true ↔ EquivB a b) (σ : Substitution s) (p : Term s)
    (fixed : ∀ v, p.Occurs v → bind v = false → σ.image v = .var v) : Spec tab bind eq σ p := by
  have hq : ∀ a b, EquivB a b → eq a b = true := fun a b => (heq a b).mpr
  induction p with
  | var v =>
    intro ctx xs
    by_cases hb : bind v = true
    · cases ctx with
      | none =>
        simp only [go, hb, ite_true]
        refine operand_iff _ σ _ none xs _ rfl (fun x => ?_)
        change _ ↔ EquivB (σ.image v) x
        constructor
        · rintro ⟨row, m, sat⟩
          split at m
          · obtain rfl := List.mem_singleton.mp m
            exact sat v x List.mem_cons_self
          · contradiction
        · intro e
          have ok : x.checkSort v.sort = true :=
            SortClash.check_equiv e v.sort ▸ Term.checkSort_complete (σ.sorted v)
          exact ⟨[(v, x)], by simp [ok], fun w u hm => by
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp hm); exact e⟩
      | some g =>
        simp only [go, hb, ite_true]
        constructor
        · intro part m _
          obtain rfl := List.mem_singleton.mp m
          refine ⟨id, ?_⟩
          change (cls xs ++ pend (some g) σ [v]).Perm (opsC (some g) (σ.image v) ++ cls xs)
          rw [pend_one]
          exact List.perm_append_comm
        · intro _ W h
          refine ⟨([], xs, [v]), List.mem_singleton_self _, ?_, ?_⟩
          · intro _ _ hm
            cases hm
          · change (cls xs).Perm (pend (some g) σ [v] ++ W)
            rw [pend_one]
            exact h
    · have hb' : bind v = false := by simpa using hb
      have img : σ.apply (.var v) = .var v := fixed v rfl hb'
      simp only [go, hb', Bool.false_eq_true, ite_false, img]
      refine operand_iff _ σ _ ctx xs _ (by cases ctx <;> rfl) (fun x => ?_)
      rw [← isVariable_iff]
      split
      · next h => simp [accepts, holds, h]
      · next h => simp [accepts, h]
  | atom a =>
    intro ctx xs
    simp only [go]
    refine operand_iff _ σ (σ.apply (.atom a)) ctx xs _ (by cases ctx <;> rfl) (fun x => ?_)
    change _ ↔ EquivB (.atom a) x
    cases x with
    | atom b =>
      by_cases same : a = b
      · subst b; simp [accepts, holds, EquivB.refl]
      · simp [same, accepts]
        exact mismatch (fun h => same (Head.atom.inj h))
    | _ => simp [accepts]; exact mismatch (fun h => nomatch h)
  | free f ps ih =>
    intro ctx xs
    simp only [go]
    have child (i) := ih i (fun v occ => fixed v ⟨i, occ⟩)
    refine operand_spec _ σ (σ.apply (.free f ps)) ctx xs _ (by cases ctx <;> rfl)
      (fun x found => ?_) (fun fits x e => ?_)
    · cases x with
      | free g ys =>
        by_cases same : f = g
        · subst g
          simp only [↓reduceDIte] at found
          have all := (joined_iff hq σ _).mp found
          change EquivB (.free f (fun i => σ.apply (ps i))) (.free f ys)
          exact (free_equiv_iff ..).mpr fun i =>
            single_sound (child i) (ys i) (all _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
        · simp [same, accepts] at found
      | _ => simp [accepts] at found
    · cases x with
      | free g ys =>
        by_cases same : f = g
        · subst g
          simp only [↓reduceDIte]
          change EquivB (.free f (fun i => σ.apply (ps i))) (.free f ys) at e
          apply (joined_iff hq σ _).mpr
          rintro _ hm
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
          exact single_complete (child i) fits (ys i) ((free_equiv_iff ..).mp e i)
        · exact absurd e (mismatch (fun h => same (Head.free.inj h)))
      | _ => exact absurd e (mismatch (fun h => nomatch h))
  | comm f a b ia ib =>
    intro ctx xs
    simp only [go]
    have sa := ia (fun v occ => fixed v (.inl occ))
    have sb := ib (fun v occ => fixed v (.inr occ))
    have append (xs ys : List (Requirements s)) :
        accepts σ (xs ++ ys) ↔ accepts σ xs ∨ accepts σ ys := by
      simp [accepts, List.mem_append, or_and_right, exists_or]
    refine operand_spec _ σ (σ.apply (.comm f a b)) ctx xs _ (by cases ctx <;> rfl)
      (fun x found => ?_) (fun fits x e => ?_)
    · cases x with
      | comm g l r =>
        by_cases same : f = g
        · subst g
          simp only [ite_true, accepts_filter hq, append, andThen_eq, combine_iff] at found
          exact (Commutative.equiv_iff ..).mpr (found.imp
            (fun h => ⟨single_sound sa l h.1, single_sound sb r h.2⟩)
            (fun h => ⟨single_sound sa r h.1, single_sound sb l h.2⟩))
        · simp [same, accepts] at found
      | _ => simp [accepts] at found
    · cases x with
      | comm g l r =>
        by_cases same : f = g
        · subst g
          simp only [ite_true, accepts_filter hq, append, andThen_eq, combine_iff]
          exact ((Commutative.equiv_iff ..).mp e).imp
            (fun h => ⟨single_complete sa fits l h.1, single_complete sb fits r h.2⟩)
            (fun h => ⟨single_complete sa fits r h.1, single_complete sb fits l h.2⟩)
        · exact absurd e (mismatch (fun h => same (Head.comm.inj h)))
      | _ => exact absurd e (mismatch (fun h => nomatch h))
  | ac g a b ia ib =>
    intro ctx xs
    have sa := ia (fun v occ => fixed v (.inl occ))
    have sb := ib (fun v occ => fixed v (.inr occ))
    have shape : σ.apply (.ac g a b) = .ac g (σ.apply a) (σ.apply b) := rfl
    by_cases hc : ctx = some g
    · subst hc
      have ops : opsC (some g) (σ.apply (.ac g a b)) =
          opsC (some g) (σ.apply a) ++ opsC (some g) (σ.apply b) := Cancellation.flatten_ac g _ _
      simp only [go, ite_true]
      rw [ops]
      constructor
      · intro part m sat
        obtain ⟨⟨r1, ys, v1⟩, m1, m2⟩ := List.mem_flatMap.mp m
        obtain ⟨⟨r2, zs, v2⟩, m3, fin⟩ := List.mem_filterMap.mp m2
        dsimp only at fin
        split at fin
        · cases fin
          obtain ⟨s1, s2⟩ := holds_append.mp sat
          obtain ⟨f1, p1⟩ := (sa (some g) xs).1 _ m1 s1
          obtain ⟨f2, p2⟩ := (sb (some g) ys).1 _ m3 s2
          refine ⟨fun fl => f2 (f1 fl), ?_⟩
          dsimp only at p1 p2 ⊢
          rw [pend_append, ← List.append_assoc]
          refine (p1.append_right _).trans ?_
          rw [List.append_assoc, List.append_assoc]
          exact p2.append_left _
        · contradiction
      · intro fits W h
        rw [List.append_assoc] at h
        obtain ⟨⟨r1, ys, v1⟩, m1, s1, q1⟩ := (sa (some g) xs).2 fits _ h
        obtain ⟨⟨r2, zs, v2⟩, m3, s2, q2⟩ :=
          (sb (some g) ys).2 fits _ (q1.trans (List.perm_append_comm_assoc ..))
        have sat : holds σ (r1 ++ r2) := holds_append.mpr ⟨s1, s2⟩
        refine ⟨(r1 ++ r2, zs, v1 ++ v2),
          List.mem_flatMap.mpr ⟨_, m1, List.mem_filterMap.mpr ⟨_, m3, ?_⟩⟩, sat, ?_⟩
        · simp [consistent_of_holds hq sat]
        · dsimp only at q2 ⊢
          rw [pend_append, List.append_assoc]
          exact q2.trans (List.perm_append_comm_assoc ..)
    · have one : opsC ctx (σ.apply (.ac g a b)) = [classOf (σ.apply (.ac g a b))] := by
        cases ctx with
        | none => rfl
        | some f =>
          have ne : f ≠ g := fun e => hc (e ▸ rfl)
          simp [opsC, shape, Cancellation.flatten, ne]
      simp only [go, hc, ite_false]
      refine operand_spec _ σ _ ctx xs _ one (fun x found => ?_) (fun fits x e => ?_)
      · rw [accepts_filter hq] at found
        obtain ⟨row, m, sat⟩ := found
        obtain ⟨⟨r1, ys, v1⟩, m1, m2⟩ := List.mem_flatMap.mp m
        obtain ⟨⟨r2, zs, v2⟩, m3, m4⟩ := List.mem_flatMap.mp m2
        obtain ⟨r3, m5, rfl⟩ := List.mem_map.mp m4
        obtain ⟨s12, s3⟩ := holds_append.mp sat
        obtain ⟨s1, s2⟩ := holds_append.mp s12
        obtain ⟨f1, p1⟩ := (sa (some g) (flatten g x)).1 _ m1 s1
        obtain ⟨f2, p2⟩ := (sb (some g) ys).1 _ m3 s2
        have p3 := dist_sound (fun a b => (heq a b).mp) σ tab g _ _ _ m5 s12 s3
          (f2 (f1 (flat_flatten g x)))
        dsimp only at p1 p2
        rw [pend_append] at p3
        have total : (cls (flatten g x) ++ (pend (some g) σ v1 ++ pend (some g) σ v2)).Perm
            ((opsC (some g) (σ.apply a) ++ opsC (some g) (σ.apply b)) ++
              (pend (some g) σ v1 ++ pend (some g) σ v2)) := by
          rw [← List.append_assoc]
          refine (p1.append_right _).trans ?_
          rw [List.append_assoc, List.append_assoc]
          exact (p2.trans (p3.append_left _)).append_left _
        have core : (Cancellation.flatten g x).Perm
            (Cancellation.flatten g (σ.apply a) ++ Cancellation.flatten g (σ.apply b)) := by
          rw [← cls_flatten]
          exact (List.perm_append_right_iff _).mp total
        have e := Cancellation.fold_perm g core
        rw [Cancellation.fold_flatten, ← Cancellation.flatten_ac, Cancellation.fold_flatten] at e
        exact Quotient.exact (Option.some.inj e).symm
      · rw [accepts_filter hq]
        have bags : (cls (flatten g x)).Perm
            (opsC (some g) (σ.apply a) ++ opsC (some g) (σ.apply b)) := by
          rw [cls_flatten]
          exact (Cancellation.flatten_equiv g e.symm).trans
            (by rw [shape, Cancellation.flatten_ac]; exact .refl _)
        obtain ⟨⟨r1, ys, v1⟩, m1, s1, q1⟩ := (sa (some g) (flatten g x)).2 fits _ bags
        obtain ⟨⟨r2, zs, v2⟩, m3, s2, q2⟩ :=
          (sb (some g) ys).2 fits _ (q1.trans List.perm_append_comm)
        have s12 := holds_append.mpr ⟨s1, s2⟩
        obtain ⟨r3, m5, s3⟩ := dist_complete heq σ tab fits g (r1 ++ r2) (v1 ++ v2) zs s12
          (by rw [pend_append]; exact q2.trans List.perm_append_comm)
        exact ⟨r1 ++ r2 ++ r3, List.mem_flatMap.mpr ⟨_, m1, List.mem_flatMap.mpr
          ⟨_, m3, List.mem_map.mpr ⟨r3, m5, rfl⟩⟩⟩, holds_append.mpr ⟨s12, s3⟩⟩

/-- Every bindable variable of the pattern has a requirement or still waits. -/
theorem go_mentions {tab : List (Bound s)} {bind : Variable → Bool} {eq : Term s → Term s → Bool} (p : Term s)
    {ctx : Option s.ACSym} {xs : List (Term s)} {part : Partial s}
    (m : part ∈ go tab bind eq p ctx xs) {v : Variable} (occ : p.Occurs v) (hb : bind v = true) :
    (∃ t, (v, t) ∈ part.1) ∨ v ∈ part.2.2 := by
  induction p generalizing ctx xs part with
  | var w =>
    obtain rfl : v = w := occ
    simp only [go, hb, ite_true] at m
    cases ctx with
    | none =>
      obtain ⟨x, r, _, row, hr, rfl⟩ := mem_operand.mp m
      split at hr
      · obtain rfl := List.mem_singleton.mp hr
        exact .inl ⟨x, List.mem_cons_self⟩
      · contradiction
    | some g =>
      obtain rfl := List.mem_singleton.mp m
      exact .inr List.mem_cons_self
  | atom => contradiction
  | free f ps ih =>
    obtain ⟨i, hi⟩ := occ
    simp only [go] at m
    obtain ⟨x, r, _, row, hr, rfl⟩ := mem_operand.mp m
    cases x with
    | free g ys =>
      dsimp only at hr
      split at hr
      · next same =>
        subst g
        obtain ⟨piece, hp, sub⟩ := part_of_joined _ hr (List.mem_ofFn.mpr ⟨i, rfl⟩)
        obtain ⟨inner, hin, fin⟩ := List.mem_filterMap.mp hp
        obtain rfl := finish_eq.mp fin
        rcases ih i hin hi with ⟨t, ht⟩ | waits
        · exact .inl ⟨t, sub ht⟩
        · cases waits
      · contradiction
    | _ => contradiction
  | comm f a b ia ib =>
    simp only [go] at m
    obtain ⟨x, r, _, row, hr, rfl⟩ := mem_operand.mp m
    cases x with
    | comm g l k =>
      dsimp only at hr
      split at hr
      · have side {p q : Term s} {u w : Term s}
            (ip : ∀ {ctx xs part}, part ∈ go tab bind eq p ctx xs → p.Occurs v → (∃ t, (v, t) ∈ part.1) ∨ v ∈ part.2.2)
            (iq : ∀ {ctx xs part}, part ∈ go tab bind eq q ctx xs → q.Occurs v → (∃ t, (v, t) ∈ part.1) ∨ v ∈ part.2.2)
            (hit : p.Occurs v ∨ q.Occurs v)
            (member : row ∈ andThen ((go tab bind eq p none [u]).filterMap finish)
              (fun _ => (go tab bind eq q none [w]).filterMap finish)) : ∃ t, (v, t) ∈ row := by
          rw [andThen_eq] at member
          refine mentions_combine member (hit.imp (fun pv piece hp => ?_) (fun qv piece hp => ?_))
          · obtain ⟨inner, hin, fin⟩ := List.mem_filterMap.mp hp
            obtain rfl := finish_eq.mp fin
            exact (ip hin pv).resolve_right (fun waits => nomatch waits)
          · obtain ⟨inner, hin, fin⟩ := List.mem_filterMap.mp hp
            obtain rfl := finish_eq.mp fin
            exact (iq hin qv).resolve_right (fun waits => nomatch waits)
        rcases List.mem_append.mp (List.mem_filter.mp hr).1 with member | member
        · exact .inl (side (fun h o => ia h o) (fun h o => ib h o) occ member)
        · exact .inl (side (fun h o => ia h o) (fun h o => ib h o) occ member)
      · contradiction
    | _ => contradiction
  | ac g a b ia ib =>
    by_cases hc : ctx = some g
    · subst hc
      simp only [go, ite_true] at m
      obtain ⟨⟨r1, ys, v1⟩, m1, m2⟩ := List.mem_flatMap.mp m
      obtain ⟨⟨r2, zs, v2⟩, m3, fin⟩ := List.mem_filterMap.mp m2
      dsimp only at fin
      split at fin
      · cases fin
        rcases occ with av | bv
        · rcases ia m1 av with ⟨t, ht⟩ | waits
          · exact .inl ⟨t, List.mem_append_left _ ht⟩
          · exact .inr (List.mem_append_left _ waits)
        · rcases ib m3 bv with ⟨t, ht⟩ | waits
          · exact .inl ⟨t, List.mem_append_right _ ht⟩
          · exact .inr (List.mem_append_right _ waits)
      · contradiction
    · simp only [go, hc, ite_false] at m
      obtain ⟨x, r, _, row, hr, rfl⟩ := mem_operand.mp m
      obtain ⟨⟨r1, ys, v1⟩, m1, m2⟩ := List.mem_flatMap.mp (List.mem_filter.mp hr).1
      obtain ⟨⟨r2, zs, v2⟩, m3, m4⟩ := List.mem_flatMap.mp m2
      obtain ⟨r3, m5, rfl⟩ := List.mem_map.mp m4
      have waiting (hw : v ∈ v1 ++ v2) : ∃ t, (v, t) ∈ r1 ++ r2 ++ r3 :=
        (dist_mentions tab g _ _ _ m5 hw).elim (fun ⟨t, ht⟩ => ⟨t, List.mem_append_right _ ht⟩)
          (fun ⟨t, ht⟩ => ⟨t, List.mem_append_left _ ht⟩)
      rcases occ with av | bv
      · rcases ia m1 av with ⟨t, ht⟩ | waits
        · exact .inl ⟨t, List.mem_append_left _ (List.mem_append_left _ ht)⟩
        · exact .inl (waiting (List.mem_append_left _ waits))
      · rcases ib m3 bv with ⟨t, ht⟩ | waits
        · exact .inl ⟨t, List.mem_append_left _ (List.mem_append_right _ ht)⟩
        · exact .inl (waiting (List.mem_append_right _ waits))

/-- A substitution satisfying a branch of a whole pattern makes the pattern
equal to the subject. -/
theorem rows_sound {tab : List (Bound s)} {bind : Variable → Bool} {eq : Term s → Term s → Bool}
    (heq : ∀ a b, eq a b = true ↔ EquivB a b) (σ : Substitution s) (p t : Term s)
    (fixed : ∀ v, p.Occurs v → bind v = false → σ.image v = .var v)
    (found : accepts σ (rows tab bind eq p t)) : EquivB (σ.apply p) t :=
  single_sound (spec heq σ p fixed) t found

/-- The branches of a whole pattern describe exactly its instances equal to
the subject, for every substitution that leaves rigid variables alone and
stays within the recorded bounds. -/
theorem rows_iff {tab : List (Bound s)} {bind : Variable → Bool} {eq : Term s → Term s → Bool}
    (heq : ∀ a b, eq a b = true ↔ EquivB a b) (σ : Substitution s) (p t : Term s)
    (fixed : ∀ v, p.Occurs v → bind v = false → σ.image v = .var v) (fits : Fits tab σ) :
    accepts σ (rows tab bind eq p t) ↔ EquivB (σ.apply p) t :=
  ⟨single_sound (spec heq σ p fixed) t, single_complete (spec heq σ p fixed) fits t⟩

theorem rows_mentions {tab : List (Bound s)} {bind : Variable → Bool} {eq : Term s → Term s → Bool} {p t : Term s}
    {row : Requirements s} (m : row ∈ rows tab bind eq p t) {v : Variable} (occ : p.Occurs v)
    (hb : bind v = true) : ∃ u, (v, u) ∈ row := by
  obtain ⟨part, hp, fin⟩ := List.mem_filterMap.mp m
  obtain rfl := finish_eq.mp fin
  exact (go_mentions p hp occ hb).resolve_right (fun waits => nomatch waits)

/-- Requirements and waiting variables only concern bindable variables of the
pattern, and every recorded image fits the sort of its variable. -/
theorem go_entries {tab : List (Bound s)} {bind : Variable → Bool} {eq : Term s → Term s → Bool} (p : Term s)
    {ctx : Option s.ACSym} {xs : List (Term s)} {part : Partial s}
    (m : part ∈ go tab bind eq p ctx xs) :
    (∀ v t, (v, t) ∈ part.1 → p.Occurs v ∧ bind v = true ∧ t.checkSort v.sort = true) ∧
      ∀ v ∈ part.2.2, p.Occurs v ∧ bind v = true := by
  induction p generalizing ctx xs part with
  | var w =>
    by_cases hb : bind w = true
    · simp only [go, hb, ite_true] at m
      cases ctx with
      | none =>
        obtain ⟨x, r, _, row, hr, rfl⟩ := mem_operand.mp m
        split at hr
        · next ok =>
          obtain rfl := List.mem_singleton.mp hr
          refine ⟨fun v t h => ?_, fun _ h => nomatch h⟩
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp h)
          exact ⟨rfl, hb, ok⟩
        · contradiction
      | some g =>
        obtain rfl := List.mem_singleton.mp m
        refine ⟨(fun _ _ h => nomatch h), fun v h => ?_⟩
        obtain rfl := List.mem_singleton.mp h
        exact ⟨rfl, hb⟩
    · have hb' : bind w = false := by simpa using hb
      simp only [go, hb', Bool.false_eq_true, ite_false] at m
      obtain ⟨x, r, _, row, hr, rfl⟩ := mem_operand.mp m
      split at hr
      · obtain rfl := List.mem_singleton.mp hr
        exact ⟨(fun _ _ h => nomatch h), fun _ h => nomatch h⟩
      · contradiction
  | atom a =>
    simp only [go] at m
    obtain ⟨x, r, _, row, hr, rfl⟩ := mem_operand.mp m
    refine ⟨fun v t h => ?_, fun _ h => nomatch h⟩
    cases x with
    | atom b =>
      dsimp only at hr
      split at hr
      · obtain rfl := List.mem_singleton.mp hr
        contradiction
      · contradiction
    | _ => contradiction
  | free f ps ih =>
    simp only [go] at m
    obtain ⟨x, r, _, row, hr, rfl⟩ := mem_operand.mp m
    refine ⟨fun v t h => ?_, fun _ h => nomatch h⟩
    cases x with
    | free g ys =>
      dsimp only at hr
      split at hr
      · next same =>
        subst g
        obtain ⟨piece, hpiece, part, hp, hit⟩ := entry_of_joined _ hr h
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hpiece
        obtain ⟨inner, hin, fin⟩ := List.mem_filterMap.mp hp
        obtain rfl := finish_eq.mp fin
        obtain ⟨occ, rest⟩ := (ih i hin).1 v t hit
        exact ⟨⟨i, occ⟩, rest⟩
      · contradiction
    | _ => contradiction
  | comm f a b ia ib =>
    simp only [go] at m
    obtain ⟨x, r, _, row, hr, rfl⟩ := mem_operand.mp m
    refine ⟨fun v t h => ?_, fun _ h => nomatch h⟩
    cases x with
    | comm g l k =>
      dsimp only at hr
      split at hr
      · have side {u w : Term s}
            (member : row ∈ andThen ((go tab bind eq a none [u]).filterMap finish)
              (fun _ => (go tab bind eq b none [w]).filterMap finish)) :
            (a.Occurs v ∨ b.Occurs v) ∧ bind v = true ∧ t.checkSort v.sort = true := by
          rw [andThen_eq] at member
          obtain ⟨ra, ha, rb, hb, rfl⟩ := mem_combine.mp member
          rcases List.mem_append.mp h with left | right
          · obtain ⟨inner, hin, fin⟩ := List.mem_filterMap.mp ha
            obtain rfl := finish_eq.mp fin
            obtain ⟨occ, rest⟩ := (ia hin).1 v t left
            exact ⟨.inl occ, rest⟩
          · obtain ⟨inner, hin, fin⟩ := List.mem_filterMap.mp hb
            obtain rfl := finish_eq.mp fin
            obtain ⟨occ, rest⟩ := (ib hin).1 v t right
            exact ⟨.inr occ, rest⟩
        rcases List.mem_append.mp (List.mem_filter.mp hr).1 with member | member
        · exact side member
        · exact side member
      · contradiction
    | _ => contradiction
  | ac g a b ia ib =>
    by_cases hc : ctx = some g
    · subst hc
      simp only [go, ite_true] at m
      obtain ⟨⟨r1, ys, v1⟩, m1, m2⟩ := List.mem_flatMap.mp m
      obtain ⟨⟨r2, zs, v2⟩, m3, fin⟩ := List.mem_filterMap.mp m2
      dsimp only at fin
      split at fin
      · cases fin
        refine ⟨fun v t h => ?_, fun v h => ?_⟩
        · rcases List.mem_append.mp h with left | right
          · obtain ⟨occ, rest⟩ := (ia m1).1 v t left
            exact ⟨.inl occ, rest⟩
          · obtain ⟨occ, rest⟩ := (ib m3).1 v t right
            exact ⟨.inr occ, rest⟩
        · rcases List.mem_append.mp h with left | right
          · exact ⟨.inl ((ia m1).2 v left).1, ((ia m1).2 v left).2⟩
          · exact ⟨.inr ((ib m3).2 v right).1, ((ib m3).2 v right).2⟩
      · contradiction
    · simp only [go, hc, ite_false] at m
      obtain ⟨x, r, _, row, hr, rfl⟩ := mem_operand.mp m
      obtain ⟨⟨r1, ys, v1⟩, m1, m2⟩ := List.mem_flatMap.mp (List.mem_filter.mp hr).1
      obtain ⟨⟨r2, zs, v2⟩, m3, m4⟩ := List.mem_flatMap.mp m2
      obtain ⟨r3, m5, rfl⟩ := List.mem_map.mp m4
      refine ⟨fun v t h => ?_, fun _ h => nomatch h⟩
      rcases List.mem_append.mp h with early | shared
      · rcases List.mem_append.mp early with left | right
        · obtain ⟨occ, rest⟩ := (ia m1).1 v t left
          exact ⟨.inl occ, rest⟩
        · obtain ⟨occ, rest⟩ := (ib m3).1 v t right
          exact ⟨.inr occ, rest⟩
      · obtain ⟨waits, ok⟩ := dist_entries tab g _ _ _ m5 shared
        rcases List.mem_append.mp waits with left | right
        · exact ⟨.inl ((ia m1).2 v left).1, ((ia m1).2 v left).2, ok⟩
        · exact ⟨.inr ((ib m3).2 v right).1, ((ib m3).2 v right).2, ok⟩

theorem rows_entries {tab : List (Bound s)} {bind : Variable → Bool} {eq : Term s → Term s → Bool} {p t : Term s}
    {row : Requirements s} (m : row ∈ rows tab bind eq p t) {v : Variable} {u : Term s}
    (h : (v, u) ∈ row) : p.Occurs v ∧ bind v = true ∧ u.checkSort v.sort = true := by
  obtain ⟨part, hp, fin⟩ := List.mem_filterMap.mp m
  obtain rfl := finish_eq.mp fin
  exact (go_entries p hp).1 v u h

theorem around_sound {bind : Variable → Bool} {eq : Term s → Term s → Bool}
    (heq : ∀ a b, eq a b = true ↔ EquivB a b) (σ : Substitution s) (g : s.ACSym) (p t : Term s)
    (fixed : ∀ v, p.Occurs v → bind v = false → σ.image v = .var v)
    {out : Requirements s × List (Term s)} (m : out ∈ around bind eq g p t)
    (sat : holds σ out.1) :
    (Cancellation.flatten g t).Perm (Cancellation.flatten g (σ.apply p) ++ cls out.2) ∧
      out.2 ≠ [] := by
  obtain ⟨⟨row, ys, vs⟩, hgo, inner⟩ := List.mem_flatMap.mp (List.mem_filter.mp m).1
  obtain ⟨more, hmore, rfl⟩ := List.mem_map.mp inner
  obtain ⟨s1, s2⟩ := holds_append.mp sat
  obtain ⟨flat, removed⟩ := ((spec heq σ p fixed) (some g) (flatten g t)).1 _ hgo s1
  obtain ⟨ordered, spare⟩ := share_sound (fun a b => (heq a b).mp) σ [] g true row _ ys hmore s1 s2
    (flat (flat_flatten g t))
  have shared := ordered.trans ((pend_perm _ σ (order_perm g row vs)).append_right _)
  refine ⟨?_, fun e => by simpa using spare.mp e⟩
  rw [← cls_flatten]
  dsimp only at removed
  have both : (cls (flatten g t) ++ pend (some g) σ vs).Perm
      ((Cancellation.flatten g (σ.apply p) ++ cls more.2) ++ pend (some g) σ vs) :=
    removed.trans ((shared.append_left _).trans (by
      rw [List.append_assoc]
      exact (List.perm_append_comm).append_left _))
  exact (List.perm_append_right_iff _).mp both

theorem around_complete {bind : Variable → Bool} {eq : Term s → Term s → Bool}
    (heq : ∀ a b, eq a b = true ↔ EquivB a b) (σ : Substitution s) (g : s.ACSym) (p t : Term s)
    (fixed : ∀ v, p.Occurs v → bind v = false → σ.image v = .var v)
    {W : List (Cancellation.Class s)}
    (h : (Cancellation.flatten g t).Perm (Cancellation.flatten g (σ.apply p) ++ W)) (hw : W ≠ []) :
    ∃ out ∈ around bind eq g p t, holds σ out.1 ∧ (cls out.2).Perm W := by
  rw [← cls_flatten] at h
  obtain ⟨⟨row, ys, vs⟩, hgo, s1, left⟩ := ((spec heq σ p fixed) (some g) (flatten g t)).2 (fits_nil σ) W h
  obtain ⟨more, hmore, s2, rest⟩ := share_complete heq σ [] (fits_nil σ) g true row (order g row vs) ys s1
    (left.trans ((pend_perm _ σ (order_perm g row vs)).symm.append_right _))
    ⟨fun e => (hw e).elim, fun e => nomatch e⟩
  have sat : holds σ (row ++ more.1) := holds_append.mpr ⟨s1, s2⟩
  exact ⟨(row ++ more.1, more.2), List.mem_filter.mpr ⟨List.mem_flatMap.mpr
    ⟨_, hgo, List.mem_map.mpr ⟨more, hmore, rfl⟩⟩, consistent_of_holds (fun a b => (heq a b).mpr) sat⟩,
    sat, rest⟩

theorem around_mentions {bind : Variable → Bool} {eq : Term s → Term s → Bool} {g : s.ACSym}
    {p t : Term s} {out : Requirements s × List (Term s)} (m : out ∈ around bind eq g p t)
    {v : Variable} (occ : p.Occurs v) (hb : bind v = true) : ∃ u, (v, u) ∈ out.1 := by
  obtain ⟨⟨row, ys, vs⟩, hgo, inner⟩ := List.mem_flatMap.mp (List.mem_filter.mp m).1
  obtain ⟨more, hmore, rfl⟩ := List.mem_map.mp inner
  rcases go_mentions p hgo occ hb with ⟨u, hu⟩ | waits
  · exact ⟨u, List.mem_append_left _ hu⟩
  · exact (share_mentions [] g true row _ ys hmore ((order_perm g row vs).mem_iff.mpr waits)).elim
      (fun ⟨u, hu⟩ => ⟨u, List.mem_append_right _ hu⟩) (fun ⟨u, hu⟩ => ⟨u, List.mem_append_left _ hu⟩)

theorem around_entries {bind : Variable → Bool} {eq : Term s → Term s → Bool} {g : s.ACSym}
    {p t : Term s} {out : Requirements s × List (Term s)} (m : out ∈ around bind eq g p t)
    {v : Variable} {u : Term s} (h : (v, u) ∈ out.1) :
    p.Occurs v ∧ bind v = true ∧ u.checkSort v.sort = true := by
  obtain ⟨⟨row, ys, vs⟩, hgo, inner⟩ := List.mem_flatMap.mp (List.mem_filter.mp m).1
  obtain ⟨more, hmore, rfl⟩ := List.mem_map.mp inner
  rcases List.mem_append.mp h with early | shared
  · exact (go_entries p hgo).1 v u early
  · obtain ⟨ordered, ok⟩ := share_entries [] g true row _ ys hmore shared
    have waits := (order_perm g row vs).mem_iff.mp ordered
    exact ⟨((go_entries p hgo).2 v waits).1, ((go_entries p hgo).2 v waits).2, ok⟩

theorem around_consistent {bind : Variable → Bool} {eq : Term s → Term s → Bool} {g : s.ACSym}
    {p t : Term s} {out : Requirements s × List (Term s)} (m : out ∈ around bind eq g p t) :
    consistent eq out.1 = true := by
  simpa using (List.mem_filter.mp m).2

end

end Tamarin.BagMatching
