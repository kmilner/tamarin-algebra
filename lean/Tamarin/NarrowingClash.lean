import Tamarin.GroundACEquality
import Tamarin.SortClash

/-! Reject impossible unification queries before searching their AC components.
Heads are fixed except at variables. A rigid subtree which cannot inhabit a
required sort remains incompatible even if other variables narrow their sorts. -/
namespace Tamarin.NarrowingClash
variable {s : Signature}

def possible : Term s → SortId → Bool
  | .var v, k => Subsort.check v.sort k || Subsort.check k v.sort
  | .atom a, k => Subsort.check (s.atomSort a) k
  | .free f xs, k => Subsort.check (s.outputSort f) k &&
      (List.finRange (s.arity f)).all fun i => possible (xs i) (s.inputSort f i)
  | .comm f a b, k => Subsort.check (s.cSort f) k && possible a (s.cSort f) && possible b (s.cSort f)
  | .ac f a b, k => Subsort.check (s.acSort f) k && possible a (s.acSort f) && possible b (s.acSort f)

private theorem possible_of_instance (t : Term s) (σ : Substitution s) (k)
    (h : (σ.apply t).checkSort k) : possible t k := by
  induction t generalizing k with
  | var v =>
    have left := Term.rootSort_le (σ.sorted v)
    have right := Term.rootSort_le (Term.checkSort_sound _ _ h)
    change Subsort (σ.image v).rootSort k at right
    have comparable {a b c : SortId} (ab : Subsort a b) (ac : Subsort a c) :
        Subsort b c ∨ Subsort c b := by
      cases ab <;> cases ac <;> first | exact .inl (by constructor) | exact .inr (by constructor)
    exact Bool.or_eq_true_iff.mpr ((comparable left right).imp
      (Subsort.check_iff ..).mpr (Subsort.check_iff ..).mpr)
  | atom => exact h
  | free f xs ih =>
    simp only [Substitution.apply,Term.subst,Term.checkSort,Bool.and_eq_true,List.all_eq_true] at h
    exact Bool.and_eq_true_iff.mpr ⟨h.1,List.all_eq_true.mpr fun i hi => ih i _ (h.2 i hi)⟩
  | ac f a b ia ib | comm f a b ia ib =>
    simp only [Substitution.apply,Term.subst,Term.checkSort,Bool.and_eq_true] at h
    simp only [possible,Bool.and_eq_true]
    exact ⟨⟨h.1.1,ia _ h.1.2⟩,ib _ h.2⟩

def sortClash (a b : Term s) := a.checkSort a.rootSort && !(possible b a.rootSort)

private theorem no_sort_clash (a b : Term s) (σ : Substitution s) (eq : EquivB (σ.apply a) (σ.apply b)) :
    sortClash a b = false := by
  apply Bool.eq_false_iff.mpr
  intro clash
  obtain ⟨typed,no⟩ := Bool.and_eq_true_iff.mp clash
  have same := SortClash.check_equiv eq a.rootSort
  have ok := Term.checkSort_complete ((Term.checkSort_sound a _ typed).subst σ.image σ.sorted)
  have yes := possible_of_instance b σ _ (same.symm.trans ok)
  simp [yes] at no

variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

def heads : Term s → Term s → Bool
  | .var _, _ | _, .var _ => true
  | .atom a,.atom b => decide (a = b)
  | .free f _,.free g _ => decide (f = g)
  | .comm f ..,.comm g .. => decide (f = g)
  | .ac f ..,.ac g .. => decide (f = g)
  | _,_ => false

private theorem heads_of_solution (a b : Term s) (σ : Substitution s)
    (eq : EquivB (σ.apply a) (σ.apply b)) : heads a b := by
  have root := eq.head_eq
  cases a <;> cases b <;> simp_all [heads,Substitution.apply,Term.subst,Model.eval,headModel]

/-- Rigid outer constructors that no instance identifies. -/
def clash (a b : Term s) : Bool := !(heads a b)

theorem no_clash (a b : Term s) (σ : Substitution s)
    (eq : EquivB (σ.apply a) (σ.apply b)) : clash a b = false := by
  simp [clash, heads_of_solution a b σ eq]

def impossible (e : Equation s) :=
  !(heads e.lhs e.rhs) || sortClash e.lhs e.rhs || sortClash e.rhs e.lhs

theorem refutes {p : Problem s} (h : p.any impossible) : CompleteSet p [] := by
  apply (complete_empty_iff _).mpr
  rintro ⟨σ,sol⟩
  obtain ⟨e,he,bad⟩ := List.any_eq_true.mp h
  have eq := sol e he
  simp [impossible,heads_of_solution _ _ σ eq,no_sort_clash _ _ σ eq,no_sort_clash _ _ σ eq.symm] at bad

/-- A complete unifier with a verified early rejection for impossible
equations. The supplied solver handles the entire remaining conjunction. -/
def unifier (u : VerifiedUnifier s (fun _ => True)) : VerifiedUnifier s (fun _ => True) where
  solve p hp avoid := if p.any impossible then [] else u.solve p hp avoid
  correct p hp avoid := by split <;> first | exact refutes ‹_› | exact u.correct p hp avoid
  domain p hp avoid := by split <;> first | simp | exact u.domain p hp avoid
  fresh p hp avoid := by split <;> first | simp | exact u.fresh p hp avoid

/-- The outer constructor admits the sort. -/
def rootPossible : Term s → SortId → Bool
  | .var v, k => Subsort.check v.sort k || Subsort.check k v.sort
  | .atom a, k => Subsort.check (s.atomSort a) k
  | .free f _, k => Subsort.check (s.outputSort f) k
  | .comm f _ _, k => Subsort.check (s.cSort f) k
  | .ac f _ _, k => Subsort.check (s.acSort f) k

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
private theorem rootPossible_of_possible (t : Term s) (k : SortId) (h : possible t k = true) :
    rootPossible t k = true := by
  cases t <;> simp_all [possible, rootPossible]

/-- A variable equated with a term whose outer constructor lies outside its sort. -/
def shallow : Term s → Term s → Bool
  | .var v, b => !(rootPossible b v.sort)
  | _, _ => false

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
private theorem sortClash_of_shallow (a b : Term s) (h : shallow a b = true) : sortClash a b = true := by
  cases a with
  | var v =>
    have root : rootPossible b v.sort = false := by simpa [shallow] using h
    have deep : possible b v.sort = false := by
      cases hp : possible b v.sort with
      | false => rfl
      | true => rw [rootPossible_of_possible _ _ hp] at root; cases root
    have self : Subsort.check v.sort v.sort = true := (Subsort.check_iff ..).mpr (.refl _)
    simp [sortClash, Term.checkSort, Term.rootSort, deep, self]
  | _ => simp [shallow] at h

/-- The clashes visible at the roots of an equation, found without traversing either side. -/
def quick (e : Equation s) : Bool :=
  !(heads e.lhs e.rhs) || shallow e.lhs e.rhs || shallow e.rhs e.lhs

theorem impossible_of_quick {e : Equation s} (h : quick e = true) : impossible e = true := by
  simp only [quick, Bool.or_eq_true] at h
  simp only [impossible, Bool.or_eq_true]
  rcases h with (h | h) | h
  · exact .inl (.inl h)
  · exact .inl (.inr (sortClash_of_shallow _ _ h))
  · exact .inr (sortClash_of_shallow _ _ h)

theorem quick_refutes {p : Problem s} (h : p.any quick) : CompleteSet p [] := by
  obtain ⟨e,he,bad⟩ := List.any_eq_true.mp h
  exact refutes (List.any_eq_true.mpr ⟨e,he,impossible_of_quick bad⟩)

/-- Early rejection by the root constructors alone. The check costs one
comparison per equation, so it suits inputs that are decomposed afterwards. -/
def rootUnifier (u : VerifiedUnifier s (fun _ => True)) : VerifiedUnifier s (fun _ => True) where
  solve p hp avoid := if p.any quick then [] else u.solve p hp avoid
  correct p hp avoid := by split <;> first | exact quick_refutes ‹_› | exact u.correct p hp avoid
  domain p hp avoid := by split <;> first | simp | exact u.domain p hp avoid
  fresh p hp avoid := by split <;> first | simp | exact u.fresh p hp avoid

end Tamarin.NarrowingClash
