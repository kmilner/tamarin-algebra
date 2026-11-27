import Tamarin.DHProduct

/-! Binary views of an ordinary AC subject. Each operand occurrence goes to
one side. A view keeps both sides nonempty, including at the kind level. -/
namespace Tamarin.ACSplits
open ACRepresentation
variable {s : Signature}

private def partitions {α : Type} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: xs =>
    let tail := partitions xs
    tail.map (fun (l, r) => (x :: l, r)) ++ tail.map (fun (l, r) => (l, x :: r))

private theorem partitions_sound {α : Type} (xs : List α) {l r}
    (h : (l, r) ∈ partitions xs) : xs.Perm (l ++ r) := by
  induction xs generalizing l r with
  | nil =>
    obtain ⟨rfl,rfl⟩ : l = [] ∧ r = [] := by simpa [partitions] using h
    exact .nil
  | cons x xs ih =>
    rcases List.mem_append.mp h with hl | hr
    · obtain ⟨⟨a,b⟩, hm, eq⟩ := List.mem_map.mp hl
      cases eq
      exact (ih hm).cons x
    · obtain ⟨⟨a,b⟩, hm, eq⟩ := List.mem_map.mp hr
      cases eq
      exact List.perm_cons_append_cons x (ih hm)

private theorem partitions_cover {α β : Type} (key : α → β) (xs : List α) {l r : List β}
    (h : (xs.map key).Perm (l ++ r)) :
    ∃ a b, (a,b) ∈ partitions xs ∧ (a.map key).Perm l ∧ (b.map key).Perm r := by
  classical
  induction xs generalizing l r with
  | nil =>
    have e := h.symm.eq_nil
    obtain ⟨rfl,rfl⟩ := List.append_eq_nil_iff.mp e
    exact ⟨[],[],by simp [partitions],.nil,.nil⟩
  | cons x xs ih =>
    rcases List.mem_append.mp (h.mem_iff.mp List.mem_cons_self) with hl | hr
    · have put := List.perm_cons_erase hl
      have rest := (h.trans (put.append_right r)).cons_inv
      obtain ⟨a,b,hm,ha,hb⟩ := ih rest
      exact ⟨x::a,b,List.mem_append_left _ (List.mem_map.mpr ⟨(a,b),hm,rfl⟩),
        (ha.cons _).trans put.symm,hb⟩
    · have put := List.perm_cons_erase hr
      have move := List.perm_cons_append_cons (key x) (List.Perm.refl (l ++ r.erase (key x)))
      have rest := (h.trans ((put.append_left l).trans move.symm)).cons_inv
      obtain ⟨a,b,hm,ha,hb⟩ := ih rest
      exact ⟨a,x::b,List.mem_append_right _ (List.mem_map.mpr ⟨(a,b),hm,rfl⟩),
        ha,(hb.cons _).trans put.symm⟩

private theorem foldClasses (f : s.ACSym) (xs : List (Term s)) :
    Cancellation.fold f (xs.map Cancellation.classOf) = (decode f xs).map Cancellation.classOf := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons, Cancellation.fold, ih]
    cases xs <;> rfl

def splits [DecidableEq s.ACSym] (f : s.ACSym) (t : Term s) : List (Term s × Term s) :=
  (partitions (flatten f t)).filterMap fun (l,r) => do
    return (← decode f l, ← decode f r)

theorem sound [DecidableEq s.ACSym] (f : s.ACSym) (t : Term s) {a b}
    (member : (a,b) ∈ splits f t) : EquivB t (.ac f a b) := by
  obtain ⟨⟨l,r⟩, part, vals⟩ := List.mem_filterMap.mp member
  cases hl : decode f l <;> cases hr : decode f r <;> simp [hl,hr] at vals
  obtain ⟨rfl,rfl⟩ := vals
  obtain ⟨u,hu,eu⟩ := flatten_correct f t
  obtain ⟨v,hv,ev⟩ := decode_append f l r _ _ hl hr
  exact eu.symm.trans ((decode_perm f (partitions_sound _ part) _ _ hu hv).trans ev)

theorem complete [DecidableEq s.ACSym] (f : s.ACSym) {t a b : Term s}
    (eq : EquivB t (.ac f a b)) :
    ∃ l r, (l,r) ∈ splits f t ∧ EquivB a l ∧ EquivB b r := by
  have bags := Cancellation.flatten_equiv f eq
  rw [Rewriting.DHProduct.classes f t, Cancellation.flatten_ac] at bags
  obtain ⟨ls,rs,part,hl,hr⟩ := partitions_cover Cancellation.classOf _ bags
  have side {xs : List (Term s)} {v : Term s}
      (perm : (xs.map Cancellation.classOf).Perm (Cancellation.flatten f v)) :
      ∃ u, decode f xs = some u ∧ EquivB v u := by
    have e := Cancellation.fold_perm f perm
    rw [foldClasses, Cancellation.fold_flatten] at e
    cases h : decode f xs with
    | none => simp [h] at e
    | some u =>
      have same : Cancellation.classOf u = Cancellation.classOf v := by simpa [h] using e
      exact ⟨u,rfl, Quotient.exact same.symm⟩
  obtain ⟨l,dl,el⟩ := side hl
  obtain ⟨r,dr,er⟩ := side hr
  exact ⟨l,r,List.mem_filterMap.mpr ⟨(ls,rs),part,by simp [dl,dr]⟩,el,er⟩

private theorem partitions_filter {α : Type} (p : α → Bool) (xs : List α) {l r : List α}
    (h : (l,r) ∈ partitions xs) (aside : ∀ z ∈ r, p z = true) :
    (l.filter p,r) ∈ partitions (xs.filter p) ∧
      l.filter (fun x => !p x) = xs.filter (fun x => !p x) := by
  induction xs generalizing l r with
  | nil =>
    obtain ⟨rfl,rfl⟩ : l = [] ∧ r = [] := by simpa [partitions] using h
    exact ⟨by simp [partitions],rfl⟩
  | cons x xs ih =>
    rcases List.mem_append.mp h with hl | hr
    · obtain ⟨⟨a,b⟩,hm,eq⟩ := List.mem_map.mp hl
      cases eq
      obtain ⟨inside,kept⟩ := ih hm aside
      cases px : p x with
      | true =>
        simp only [List.filter_cons,px,↓reduceIte,Bool.not_true,Bool.false_eq_true]
        exact ⟨List.mem_append_left _ (List.mem_map.mpr ⟨(_,_),inside,rfl⟩),kept⟩
      | false =>
        simp only [List.filter_cons,px,Bool.false_eq_true,↓reduceIte,Bool.not_false]
        exact ⟨inside,by rw [kept]⟩
    · obtain ⟨⟨a,b⟩,hm,eq⟩ := List.mem_map.mp hr
      cases eq
      obtain ⟨inside,kept⟩ := ih hm (fun z hz => aside z (List.mem_cons_of_mem _ hz))
      have px := aside x List.mem_cons_self
      simp only [List.filter_cons,px,↓reduceIte,Bool.not_true,Bool.false_eq_true]
      exact ⟨List.mem_append_right _ (List.mem_map.mpr ⟨(_,_),inside,rfl⟩),kept⟩

/-- The binary views that set aside only operands satisfying `p`: every
other operand stays on the left. Their number is exponential in the number
of operands that satisfy `p`, not in the width of the subject. -/
def asides [DecidableEq s.ACSym] (f : s.ACSym) (p : Term s → Bool) (t : Term s) :
    List (Term s × Term s) :=
  let operands := flatten f t
  let kept := operands.filter fun x => !p x
  (partitions (operands.filter p)).filterMap fun (l,r) => do
    return (← decode f (kept ++ l), ← decode f r)

theorem asides_sound [DecidableEq s.ACSym] (f : s.ACSym) (p : Term s → Bool) (t : Term s) {a b}
    (member : (a,b) ∈ asides f p t) : EquivB t (.ac f a b) := by
  obtain ⟨⟨l,r⟩,part,vals⟩ := List.mem_filterMap.mp member
  cases hl : decode f ((flatten f t).filter (fun x => !p x) ++ l) <;> cases hr : decode f r <;>
    simp [hl,hr] at vals
  obtain ⟨rfl,rfl⟩ := vals
  obtain ⟨u,hu,eu⟩ := flatten_correct f t
  obtain ⟨v,hv,ev⟩ := decode_append f _ r _ _ hl hr
  have whole : (flatten f t).Perm (((flatten f t).filter (fun x => !p x) ++ l) ++ r) := by
    have halves := (List.filter_append_perm (fun x => !p x) (flatten f t)).symm
    have same : (flatten f t).filter (fun x => !!p x) = (flatten f t).filter p := by
      congr 1
      funext x
      simp
    rw [same] at halves
    rw [List.append_assoc]
    exact halves.trans ((partitions_sound _ part).append_left _)
  exact eu.symm.trans ((decode_perm f whole _ _ hu hv).trans ev)

/-- A view whose set-aside side has operands satisfying `p` only is listed,
up to the declared laws on its other side. -/
theorem asides_complete [DecidableEq s.ACSym] (f : s.ACSym) (p : Term s → Bool) {t a b : Term s}
    (eq : EquivB t (.ac f a b))
    (aside : ∀ y, Cancellation.classOf y ∈ Cancellation.flatten f b → p y = true) :
    ∃ l r, (l,r) ∈ asides f p t ∧ EquivB a l := by
  have bags := Cancellation.flatten_equiv f eq
  rw [Rewriting.DHProduct.classes f t, Cancellation.flatten_ac] at bags
  obtain ⟨ls,rs,part,hl,hr⟩ := partitions_cover Cancellation.classOf _ bags
  have side {xs : List (Term s)} {v : Term s}
      (perm : (xs.map Cancellation.classOf).Perm (Cancellation.flatten f v)) :
      ∃ u, decode f xs = some u ∧ EquivB v u := by
    have e := Cancellation.fold_perm f perm
    rw [foldClasses, Cancellation.fold_flatten] at e
    cases h : decode f xs with
    | none => simp [h] at e
    | some u =>
      have same : Cancellation.classOf u = Cancellation.classOf v := by simpa [h] using e
      exact ⟨u,rfl, Quotient.exact same.symm⟩
  obtain ⟨l,dl,el⟩ := side hl
  obtain ⟨r,dr,_⟩ := side hr
  obtain ⟨inside,kept⟩ := partitions_filter p _ part fun z hz =>
    aside z (hr.mem_iff.mp (List.mem_map_of_mem hz))
  have regroup : (ls.filter (fun x => !p x) ++ ls.filter p).Perm ls := by
    have halves := List.filter_append_perm (fun x => !p x) ls
    have same : ls.filter (fun x => !!p x) = ls.filter p := by
      congr 1
      funext x
      simp
    rwa [same] at halves
  cases dk : decode f (ls.filter (fun x => !p x) ++ ls.filter p) with
  | none =>
    cases full : ls.filter (fun x => !p x) ++ ls.filter p with
    | nil =>
      rw [full] at regroup
      rw [regroup.symm.eq_nil] at dl
      cases dl
    | cons x xs => rw [full] at dk; cases dk
  | some l' =>
    refine ⟨l',r,List.mem_filterMap.mpr ⟨(ls.filter p,rs),inside,?_⟩,
      el.trans (decode_perm f regroup.symm _ _ dl dk)⟩
    rw [kept] at dk
    simp [dk,dr]

end Tamarin.ACSplits
