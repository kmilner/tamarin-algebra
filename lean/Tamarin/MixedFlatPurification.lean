import Tamarin.MixedReconstruction

/-! Purification that keeps a product flat. A product at one AC head receives
one definition over its operands, each with its multiplicity, in place of one
definition per binary node. The partial products inside it receive none: no
equation, free argument or other head can observe them. -/
namespace Tamarin.MixedUnification.Flat
variable {s : Signature} [DecidableEq s.ACSym]

open ACRepresentation (fold flatten)

/-- The subterms that receive a definition. Under a product, a product at the
same head is skipped and its operands are visited in its place. -/
def exposed (parent : Option s.ACSym) : Term s → List (Term s)
  | t@(.var _) | t@(.atom _) => [t]
  | t@(.free _ xs) => t :: (List.ofFn fun i => exposed none (xs i)).flatten
  | t@(.comm _ a b) => t :: (exposed none a ++ exposed none b)
  | t@(.ac f a b) =>
    if parent = some f then exposed (some f) a ++ exposed (some f) b
    else t :: (exposed (some f) a ++ exposed (some f) b)

omit [DecidableEq s.ACSym] in
theorem subterms_self (t : Term s) : t ∈ subterms t := by
  cases t <;> simp [subterms]

theorem exposed_subterms {parent : Option s.ACSym} {t u : Term s} (h : u ∈ exposed parent t) :
    u ∈ subterms t := by
  induction t generalizing parent with
  | var | atom => simpa [exposed, subterms] using h
  | free f xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact subterms_self _
    · obtain ⟨l, hl, hu⟩ := List.mem_flatten.mp h
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
      exact List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, ih i hu⟩)
  | comm f a b ia ib =>
    rcases List.mem_cons.mp h with rfl | h
    · exact subterms_self _
    · exact List.mem_cons_of_mem _ (List.mem_append.mpr ((List.mem_append.mp h).imp ia ib))
  | ac f a b ia ib =>
    have inner (h : u ∈ exposed (some f) a ++ exposed (some f) b) : u ∈ subterms (.ac f a b) :=
      List.mem_cons_of_mem _ (List.mem_append.mpr ((List.mem_append.mp h).imp ia ib))
    simp only [exposed] at h
    split at h
    · exact inner h
    · rcases List.mem_cons.mp h with rfl | h
      · exact subterms_self _
      · exact inner h

theorem flatten_subterms (f : s.ACSym) {t u : Term s} (h : u ∈ flatten f t) : u ∈ subterms t := by
  induction t with
  | var | atom | free | comm =>
    obtain rfl : u = _ := by simpa [flatten] using h
    exact subterms_self _
  | ac g a b ia ib =>
    simp only [flatten] at h
    split at h
    · exact List.mem_cons_of_mem _ (List.mem_append.mpr ((List.mem_append.mp h).imp ia ib))
    · obtain rfl := List.mem_singleton.mp h
      exact subterms_self _

/-- What the definition of a term says about a valuation of the terms. -/
def Defined (W : Term s → Term s) : Term s → Prop
  | .var _ => True
  | t@(.atom a) => EquivB (W t) (.atom a)
  | t@(.free f xs) => EquivB (W t) (.free f fun i => W (xs i))
  | t@(.comm f a b) => EquivB (W t) (.comm f (W a) (W b))
  | t@(.ac f _ _) => ∃ r, ACRepresentation.decode f ((flatten f t).map W) = some r ∧ EquivB (W t) r

omit [DecidableEq s.ACSym] in
private theorem fold_subst (f : s.ACSym) (θ : Variable → Term s) (a : Term s) (as : List (Term s)) :
    (fold f a as).subst θ = fold f (a.subst θ) (as.map (·.subst θ)) := by
  induction as generalizing a with
  | nil => rfl
  | cons b bs ih => simp only [fold, Term.subst, List.map_cons, ih]

omit [DecidableEq s.ACSym] in
private theorem fold_map_congr (f : s.ACSym) (g h : Term s → Term s) (x : Term s) (xs : List (Term s))
    (each : ∀ u ∈ x :: xs, EquivB (g u) (h u)) :
    EquivB (fold f (g x) (xs.map g)) (fold f (h x) (xs.map h)) := by
  induction xs generalizing x with
  | nil => exact each x List.mem_cons_self
  | cons y ys ih =>
    exact .ac_congr f (each x List.mem_cons_self) (ih y fun u hu => each u (List.mem_cons_of_mem _ hu))

/-- A product is its operands folded, under every substitution. -/
theorem subst_flatten (f : s.ACSym) (t : Term s) (θ : Variable → Term s) :
    ∃ r, ACRepresentation.decode f ((flatten f t).map (·.subst θ)) = some r ∧ EquivB r (t.subst θ) := by
  obtain ⟨u, hu, eq⟩ := ACRepresentation.flatten_correct f t
  cases hl : flatten f t with
  | nil => simp [hl, ACRepresentation.decode] at hu
  | cons a as =>
    rw [hl] at hu
    obtain rfl : fold f a as = u := by simpa [ACRepresentation.decode] using hu
    exact ⟨_, rfl, by rw [← fold_subst]; exact eq.subst θ⟩

omit [DecidableEq s.ACSym] in
/-- The folded images of a list under two maps that agree on it. -/
theorem decode_congr (f : s.ACSym) (l : List (Term s)) (g h : Term s → Term s)
    (each : ∀ u ∈ l, EquivB (g u) (h u)) {a b : Term s}
    (left : ACRepresentation.decode f (l.map g) = some a)
    (right : ACRepresentation.decode f (l.map h) = some b) : EquivB a b := by
  cases l with
  | nil => simp [ACRepresentation.decode] at left
  | cons x xs =>
    obtain rfl : fold f (g x) (xs.map g) = a := by simpa [ACRepresentation.decode] using left
    obtain rfl : fold f (h x) (xs.map h) = b := by simpa [ACRepresentation.decode] using right
    exact fold_map_congr f g h x xs each

/-- If every exposed subterm satisfies its definition, the valuation gives
each of them the value of the term under the substitution it induces on the
variables. Under a product the statement is about the operands. -/
theorem interpret (W : Term s → Term s) (t : Term s) (parent : Option s.ACSym)
    (defined : ∀ u ∈ exposed parent t, Defined W u) :
    ((∀ g a b, t = .ac g a b → parent ≠ some g) →
      EquivB (W t) (t.subst fun v => W (.var v))) ∧
    ∀ g, parent = some g → ∀ u ∈ flatten g t, EquivB (W u) (u.subst fun v => W (.var v)) := by
  induction t generalizing parent with
  | var v =>
    refine ⟨fun _ => .refl _, fun g _ u hu => ?_⟩
    obtain rfl : u = _ := by simpa [flatten] using hu
    exact .refl _
  | atom a =>
    have top : Defined W (.atom a) := defined _ (by simp [exposed])
    have here : EquivB (W (.atom a)) ((Term.atom a).subst fun v => W (.var v)) := top
    refine ⟨fun _ => here, fun g _ u hu => ?_⟩
    obtain rfl : u = _ := by simpa [flatten] using hu
    exact here
  | free f xs ih =>
    have here : EquivB (W (.free f xs)) ((Term.free f xs).subst fun v => W (.var v)) := by
      have top : Defined W (.free f xs) := defined _ (by simp [exposed])
      refine EquivB.trans top (.free _ _ _ fun i => ?_)
      apply (ih i none (fun u hu => defined u (List.mem_cons_of_mem _
        (List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, hu⟩)))).1
      intro g a b _ h
      cases h
    refine ⟨fun _ => here, fun g _ u hu => ?_⟩
    obtain rfl : u = _ := by simpa [flatten] using hu
    exact here
  | comm f a b ia ib =>
    have here : EquivB (W (.comm f a b)) ((Term.comm f a b).subst fun v => W (.var v)) := by
      have top : Defined W (.comm f a b) := defined _ (by simp [exposed])
      refine EquivB.trans top (.comm_congr _ ?_ ?_)
      · apply (ia none (fun u hu => defined u (List.mem_cons_of_mem _ (List.mem_append_left _ hu)))).1
        intro g a b _ h; cases h
      · apply (ib none (fun u hu => defined u (List.mem_cons_of_mem _ (List.mem_append_right _ hu)))).1
        intro g a b _ h; cases h
    refine ⟨fun _ => here, fun g _ u hu => ?_⟩
    obtain rfl : u = _ := by simpa [flatten] using hu
    exact here
  | ac f a b ia ib =>
    have inner (u : Term s) (hu : u ∈ exposed (some f) a ++ exposed (some f) b) : Defined W u := by
      apply defined
      simp only [exposed]
      split
      · exact hu
      · exact List.mem_cons_of_mem _ hu
    have operands : ∀ u ∈ flatten f (.ac f a b), EquivB (W u) (u.subst fun v => W (.var v)) := by
      intro u hu
      simp only [flatten, ite_true] at hu
      rcases List.mem_append.mp hu with h | h
      · exact (ia (some f) (fun w hw => inner w (List.mem_append_left _ hw))).2 f rfl u h
      · exact (ib (some f) (fun w hw => inner w (List.mem_append_right _ hw))).2 f rfl u h
    have here (top : parent ≠ some f) :
        EquivB (W (.ac f a b)) ((Term.ac f a b).subst fun v => W (.var v)) := by
      have mem : Term.ac f a b ∈ exposed parent (.ac f a b) := by
        simp only [exposed]
        split
        · next h => exact (top h).elim
        · exact List.mem_cons_self
      obtain ⟨r, shape, eq⟩ : Defined W (.ac f a b) := defined _ mem
      obtain ⟨r', images, product⟩ := subst_flatten f (.ac f a b) (fun v => W (.var v))
      exact eq.trans ((decode_congr f _ W (·.subst fun v => W (.var v)) operands shape images).trans product)
    refine ⟨fun top => here (top f a b rfl), fun g hg u hu => ?_⟩
    by_cases same : f = g
    · subst same
      exact operands u hu
    · have single : u = .ac f a b := by
        have : g ≠ f := fun e => same e.symm
        simpa [flatten, this] using hu
      subst single
      exact here (fun e => same (Option.some.inj (hg ▸ e)).symm)

/-- The values of a solution satisfy the definition of every term whose
subterms they cover. -/
theorem defined_of_values (W : Term s → Term s) (ρ : Variable → Term s) (t : Term s)
    (values : ∀ u ∈ subterms t, EquivB (u.subst ρ) (W u)) : Defined W t := by
  have self := values t (subterms_self t)
  cases t with
  | var => trivial
  | atom a => exact self.symm
  | free f xs =>
    refine self.symm.trans (.free _ _ _ fun i => ?_)
    exact values _ (List.mem_cons_of_mem _ (List.mem_flatten.mpr
      ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, subterms_self _⟩))
  | comm f a b =>
    refine self.symm.trans (.comm_congr _ ?_ ?_)
    · exact values _ (List.mem_cons_of_mem _ (List.mem_append_left _ (subterms_self _)))
    · exact values _ (List.mem_cons_of_mem _ (List.mem_append_right _ (subterms_self _)))
  | ac f a b =>
    obtain ⟨r', images, product⟩ := subst_flatten f (.ac f a b) ρ
    cases shape : ACRepresentation.decode f ((flatten f (.ac f a b)).map W) with
    | none =>
      cases hl : flatten f (.ac f a b) with
      | nil => exact (ACRepresentation.flatten_nonempty f _ hl).elim
      | cons x xs => simp [hl, ACRepresentation.decode] at shape
    | some r =>
      refine ⟨r, shape, self.symm.trans (product.symm.trans ?_)⟩
      exact decode_congr f _ (·.subst ρ) W (fun u hu => values u (flatten_subterms f hu)) images shape

end Tamarin.MixedUnification.Flat
