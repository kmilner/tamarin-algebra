import Tamarin.BagMatching
import Tamarin.Interrupt

/-! First branch of the bag matcher without building the list of branches.
Each enumerator of `BagMatching` has a counterpart here that hands its
candidates to a continuation one at a time and stops at the first accepted
one. The counterpart equals `List.findSome?` on the enumerated list, so the
first branch found here is the head of the complete enumeration. -/
namespace Tamarin.BagMatching
open ReferenceMatching ACRepresentation

/-- Try the second search only when the first finds nothing. -/
def orLater {β : Type} (a : Option β) (b : Unit → Option β) : Option β :=
  match a with
  | some x => some x
  | none => b ()

theorem orLater_eq {β : Type} (a : Option β) (b : Unit → Option β) : orLater a b = a.or (b ()) := by
  cases a <;> rfl

theorem findSome_flatMap {α γ β : Type} (f : α → List γ) (k : γ → Option β) (l : List α) :
    (l.flatMap f).findSome? k = l.findSome? fun a => (f a).findSome? k := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.findSome?_append, ih, List.findSome?_cons]
    cases (f a).findSome? k <;> rfl

theorem findSome_filterMap {α γ β : Type} (f : α → Option γ) (k : γ → Option β) (l : List α) :
    (l.filterMap f).findSome? k = l.findSome? fun a => (f a).bind k := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filterMap_cons, List.findSome?_cons]
    cases h : f a with
    | none => simpa [h] using ih
    | some b =>
      simp only [List.findSome?_cons, Option.bind_some, ih]

theorem findSome_filter {α β : Type} (p : α → Bool) (k : α → Option β) (l : List α) :
    (l.filter p).findSome? k = l.findSome? fun a => if p a then k a else none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filter_cons, List.findSome?_cons]
    cases h : p a with
    | false => simpa [h] using ih
    | true => simp only [ite_true, List.findSome?_cons, ih]

theorem if_pos' {c : Prop} [Decidable c] {α : Type} {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem if_neg' {c : Prop} [Decidable c] {α : Type} {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

theorem findSome_some {α β : Type} (f : α → β) (l : List α) :
    (l.findSome? fun a => some (f a)) = l.head?.map f := by
  cases l <;> rfl

theorem head_flatMap {α γ : Type} (f : α → List γ) (l : List α) :
    (l.flatMap f).head? = l.findSome? fun a => (f a).head? := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.head?_append, ih, List.findSome?_cons]
    cases (f a).head? <;> rfl

theorem findSome_congr {α β : Type} {f g : α → Option β} (l : List α) (h : ∀ a, f a = g a) :
    l.findSome? f = l.findSome? g := by
  rw [show f = g from funext h]

section Bags
variable {α β : Type} (same : α → α → Bool)

/-- The first accepted sub-bag in the order of `sub`. -/
def subF [Interrupt] : Nat → List α → List α → (List α × List α → Option β) → Option β
  | 0, _, xs, k => k ([], xs)
  | _ + 1, _, [], k => k ([], [])
  | n + 1, banned, x :: xs, k =>
    if banned.any (same · x) then subF (n + 1) (x :: banned) xs fun out => k (out.1, x :: out.2)
    else orLater (subF n banned xs fun out => k (x :: out.1, out.2)) fun _ =>
      subF (n + 1) (x :: banned) xs fun out => k (out.1, x :: out.2)

/-- `subF` as it is compiled: every node of the search asks first. -/
private def subFAsking [Interrupt] :
    Nat → List α → List α → (List α × List α → Option β) → Option β
  | 0, _, xs, k => k ([], xs)
  | _ + 1, _, [], k => k ([], [])
  | n + 1, banned, x :: xs, k =>
    if Interrupt.poll () then none
    else if banned.any (same · x) then
      subFAsking (n + 1) (x :: banned) xs fun out => k (out.1, x :: out.2)
    else orLater (subFAsking n banned xs fun out => k (x :: out.1, out.2)) fun _ =>
      subFAsking (n + 1) (x :: banned) xs fun out => k (out.1, x :: out.2)

@[csimp] private theorem subF_eq_asking : @subF = @subFAsking := by
  funext α β same i n banned xs k
  induction xs generalizing n banned k with
  | nil => cases n <;> rfl
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ n => simp [subF, subFAsking, Interrupt.quiet, ih]

theorem subF_eq [Interrupt] (n : Nat) (banned xs : List α) (k : List α × List α → Option β) :
    subF same n banned xs k = (sub same n banned xs).findSome? k := by
  induction xs generalizing n banned k with
  | nil => cases n <;> simp [subF, sub]
  | cons x xs ih =>
    cases n with
    | zero => simp [subF, sub]
    | succ n =>
      simp only [subF, sub]
      split
      · rw [ih, List.findSome?_map]
        rfl
      · rw [orLater_eq, ih, ih, List.findSome?_append, List.findSome?_map, List.findSome?_map]
        rfl

end Bags

variable {s : Signature} {β : Type} [Interrupt]

/-- The first accepted combination in the order of `joined`. -/
def joinedF (eq : Term s → Term s → Bool) :
    List ((Requirements s → Option β) → Option β) → (Requirements s → Option β) → Option β
  | [], k => k []
  | e :: rest, k =>
    e fun a => joinedF eq rest fun b => if consistent eq (a ++ b) then k (a ++ b) else none

omit [Interrupt] in
theorem joinedF_eq {ι : Type} (eq : Term s → Term s → Bool) (items : List ι)
    (search : ι → (Requirements s → Option β) → Option β) (rows : ι → List (Requirements s))
    (same : ∀ i ∈ items, ∀ k, search i k = (rows i).findSome? k) (k : Requirements s → Option β) :
    joinedF eq (items.map search) k = (joined eq (items.map rows)).findSome? k := by
  induction items generalizing k with
  | nil => simp [joinedF, joined]
  | cons i items ih =>
    have tail := ih (fun j hj => same j (List.mem_cons_of_mem _ hj))
    simp only [List.map_cons, joinedF, joined, andThen_eq, combine]
    rw [findSome_filter, findSome_flatMap, same i List.mem_cons_self]
    apply findSome_congr
    intro a
    rw [tail, List.findSome?_map]
    rfl

omit [Interrupt] in
theorem ofFn_eq_map {α : Type} {n : Nat} (f : Fin n → α) : List.ofFn f = (List.finRange n).map f := by
  rw [List.finRange, List.map_ofFn]
  rfl

section
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

/-- The first accepted sharing in the order of `share`. -/
def shareF (eq : Term s → Term s → Bool) (tab : List (Bound s)) (g : s.ACSym) (spare : Bool) :
    Requirements s → List Variable → List (Term s) →
      (Requirements s × List (Term s) → Option β) → Option β
  | _, [], zs, k => if zs.isEmpty == spare then none else k ([], zs)
  | acc, v :: vs, zs, k =>
    match acc.lookup v with
    | some u =>
      match takeAll eq (flatten g u) zs with
      | some r => shareF eq tab g spare acc vs r k
      | none => none
    | none =>
      if !spare && vs.isEmpty then
        match decode g zs with
        | some t => if t.checkSort v.sort then k ([(v, t)], []) else none
        | none => none
      else
        let n := vs.count v + 1
        let others := vs.filter (· != v)
        let pool := pool eq (mine tab g v) n zs
        let must := forced eq spare n (others.map fun w => (others.count w, mine tab g w)) zs pool.1
        let size := room g v spare n others.length zs.length
        if size < must.1.length then none
        else subF same (size - must.1.length) [] must.2 fun (l, r) =>
          match decode g (must.1 ++ l) with
          | some t =>
            if t.checkSort v.sort then
              shareF eq tab g spare ((v, t) :: acc) vs (r ++ pool.2) fun out => k ((v, t) :: out.1, out.2)
            else none
          | none => none

theorem shareF_eq (eq : Term s → Term s → Bool) (tab : List (Bound s)) (g : s.ACSym) (spare : Bool)
    (acc : Requirements s) (vs : List Variable) (zs : List (Term s))
    (k : Requirements s × List (Term s) → Option β) :
    shareF eq tab g spare acc vs zs k = (share eq tab g spare acc vs zs).findSome? k := by
  induction vs generalizing acc zs k with
  | nil =>
    simp only [shareF, share]
    split <;> simp
  | cons v vs ih =>
    simp only [shareF, share]
    cases acc.lookup v with
    | some u =>
      dsimp only
      cases takeAll eq (flatten g u) zs with
      | some r => exact ih ..
      | none => rfl
    | none =>
      dsimp only
      by_cases last : (!spare && vs.isEmpty) = true
      · rw [if_pos' last, if_pos' last]
        cases decode g zs with
        | none => rfl
        | some t =>
          dsimp only
          split <;> simp
      · rw [if_neg' last, if_neg' last]
        split
        · rfl
        · rw [subF_eq, findSome_flatMap]
          apply findSome_congr
          rintro ⟨l, r⟩
          dsimp only
          generalize decode g (_ ++ l) = image
          cases image with
          | none => rfl
          | some t =>
            dsimp only
            split
            · rw [ih, List.findSome?_map]
              rfl
            · rfl

/-- The first accepted operand choice in the order of `operand`. -/
def operandF (xs : List (Term s)) (single : Term s → (Requirements s → Option β) → Option β)
    (k : Partial s → Option β) : Option β :=
  Interrupt.findSome? (fun (x, r) => single x fun row => k (row, r, [])) (picks same xs)

theorem operandF_eq (xs : List (Term s)) (search : Term s → (Requirements s → Option β) → Option β)
    (single : Term s → List (Requirements s))
    (agree : ∀ x c, search x c = (single x).findSome? c) (k : Partial s → Option β) :
    operandF xs search k = (operand xs single).findSome? k := by
  unfold operandF operand Interrupt.findSome?
  rw [findSome_flatMap]
  apply findSome_congr
  rintro ⟨x, r⟩
  dsimp only
  rw [agree, List.findSome?_map]
  rfl

/-- The first accepted partial branch in the order of `go`. -/
def goF (tab : List (Bound s)) (bind : Variable → Bool) (eq : Term s → Term s → Bool) :
    Term s → Option s.ACSym → List (Term s) → (Partial s → Option β) → Option β
  | .var v, ctx, xs, k =>
    if bind v then
      match ctx with
      | some _ => k ([], xs, [v])
      | none => operandF xs (fun x c => if x.checkSort v.sort then c [(v, x)] else none) k
    else operandF xs (fun x c => if isVariable v x then c [] else none) k
  | .atom a, _, xs, k => operandF xs (fun x c =>
      match x with
      | .atom b => if a = b then c [] else none
      | _ => none) k
  | .free f ps, _, xs, k => operandF xs (fun x c =>
      match x with
      | .free g ys =>
        if h : f = g then
          joinedF eq ((List.finRange (s.arity f)).map fun i => fun c' =>
            goF tab bind eq (ps i) none [ys (h ▸ i)] fun part => (finish part).bind c') c
        else none
      | _ => none) k
  | .comm f a b, _, xs, k => operandF xs (fun x c =>
      match x with
      | .comm g l m =>
        if f = g then
          orLater
            (goF tab bind eq a none [l] fun pa => (finish pa).bind fun ra =>
              goF tab bind eq b none [m] fun pb => (finish pb).bind fun rb =>
                if consistent eq (ra ++ rb) then c (ra ++ rb) else none)
            fun _ =>
              goF tab bind eq a none [m] fun pa => (finish pa).bind fun ra =>
                goF tab bind eq b none [l] fun pb => (finish pb).bind fun rb =>
                  if consistent eq (ra ++ rb) then c (ra ++ rb) else none
        else none
      | _ => none) k
  | .ac g a b, ctx, xs, k =>
    if ctx = some g then
      goF tab bind eq a ctx xs fun (r1, ys, v1) =>
        goF tab bind eq b ctx ys fun (r2, zs, v2) =>
          if consistent eq (r1 ++ r2) then k (r1 ++ r2, zs, v1 ++ v2) else none
    else operandF xs (fun x c =>
      goF tab bind eq a (some g) (flatten g x) fun (r1, ys, v1) =>
        goF tab bind eq b (some g) ys fun (r2, zs, v2) =>
          shareF eq tab g false (r1 ++ r2) (order g (r1 ++ r2) (v1 ++ v2)) zs fun out =>
            if consistent eq (r1 ++ r2 ++ out.1) then c (r1 ++ r2 ++ out.1) else none) k

theorem goF_eq (tab : List (Bound s)) (bind : Variable → Bool) (eq : Term s → Term s → Bool) (p : Term s)
    (ctx : Option s.ACSym) (xs : List (Term s)) (k : Partial s → Option β) :
    goF tab bind eq p ctx xs k = (go tab bind eq p ctx xs).findSome? k := by
  induction p generalizing ctx xs k with
  | var v =>
    simp only [goF, go]
    by_cases hb : bind v = true
    · rw [if_pos' hb, if_pos' hb]
      cases ctx with
      | some g => simp
      | none =>
        dsimp only
        apply operandF_eq
        intro x c
        split <;> simp
    · rw [if_neg' hb, if_neg' hb]
      apply operandF_eq
      intro x c
      split <;> simp
  | atom a =>
    simp only [goF, go]
    apply operandF_eq
    intro x c
    cases x with
    | atom b =>
      dsimp only
      split <;> simp
    | _ => rfl
  | free f ps ih =>
    simp only [goF, go]
    apply operandF_eq
    intro x c
    cases x with
    | free g ys =>
      dsimp only
      by_cases h : f = g
      · subst h
        simp only [↓reduceDIte]
        rw [ofFn_eq_map]
        apply joinedF_eq
        intro i _ k'
        rw [ih i, findSome_filterMap]
      · simp [h]
    | _ => rfl
  | comm f a b ia ib =>
    simp only [goF, go]
    apply operandF_eq
    intro x c
    cases x with
    | comm g l m =>
      dsimp only
      by_cases h : f = g
      · have pair (u w : Term s) :
            (goF tab bind eq a none [u] fun pa => (finish pa).bind fun ra =>
              goF tab bind eq b none [w] fun pb => (finish pb).bind fun rb =>
                if consistent eq (ra ++ rb) then c (ra ++ rb) else none) =
            (combine ((go tab bind eq a none [u]).filterMap finish)
              ((go tab bind eq b none [w]).filterMap finish)).findSome?
                fun row => if consistent eq row then c row else none := by
          rw [ia, combine, findSome_flatMap, findSome_filterMap]
          apply findSome_congr
          intro pa
          cases finish pa with
          | none => rfl
          | some ra =>
            simp only [Option.bind_some]
            rw [ib, List.findSome?_map, findSome_filterMap]
            rfl
        rw [if_pos' h, if_pos' h, orLater_eq, findSome_filter, List.findSome?_append, andThen_eq,
          andThen_eq, pair, pair]
      · simp [h]
    | _ => rfl
  | ac g a b ia ib =>
    simp only [goF, go]
    by_cases hc : ctx = some g
    · rw [if_pos' hc, if_pos' hc, ia, findSome_flatMap]
      apply findSome_congr
      rintro ⟨r1, ys, v1⟩
      dsimp only
      rw [ib, findSome_filterMap]
      apply findSome_congr
      rintro ⟨r2, zs, v2⟩
      dsimp only
      split <;> rfl
    · rw [if_neg' hc, if_neg' hc]
      apply operandF_eq
      intro x c
      rw [ia, findSome_filter, findSome_flatMap]
      apply findSome_congr
      rintro ⟨r1, ys, v1⟩
      dsimp only
      rw [ib, findSome_flatMap]
      apply findSome_congr
      rintro ⟨r2, zs, v2⟩
      dsimp only
      rw [shareF_eq, dist, List.map_map, List.findSome?_map]
      rfl

/-- The first accepted branch of a whole pattern against a whole subject. -/
def rowsF (tab : List (Bound s)) (bind : Variable → Bool) (eq : Term s → Term s → Bool) (p t : Term s)
    (k : Requirements s → Option β) : Option β :=
  goF tab bind eq p none [t] fun part => (finish part).bind k

theorem rowsF_eq (tab : List (Bound s)) (bind : Variable → Bool) (eq : Term s → Term s → Bool) (p t : Term s)
    (k : Requirements s → Option β) : rowsF tab bind eq p t k = (rows tab bind eq p t).findSome? k := by
  rw [rowsF, goF_eq, rows, findSome_filterMap]

/-- The first accepted branch of a pattern against a proper sub-product. -/
def aroundF (bind : Variable → Bool) (eq : Term s → Term s → Bool) (g : s.ACSym) (p t : Term s)
    (k : Requirements s × List (Term s) → Option β) : Option β :=
  goF [] bind eq p (some g) (flatten g t) fun (row, ys, vs) =>
    shareF eq [] g true row (order g row vs) ys fun out =>
      if consistent eq (row ++ out.1) then k (row ++ out.1, out.2) else none

theorem aroundF_eq (bind : Variable → Bool) (eq : Term s → Term s → Bool) (g : s.ACSym) (p t : Term s)
    (k : Requirements s × List (Term s) → Option β) :
    aroundF bind eq g p t k = (around bind eq g p t).findSome? k := by
  rw [aroundF, goF_eq, around, findSome_filter, findSome_flatMap]
  apply findSome_congr
  rintro ⟨row, ys, vs⟩
  dsimp only
  rw [shareF_eq, List.findSome?_map]
  rfl

end

end Tamarin.BagMatching
