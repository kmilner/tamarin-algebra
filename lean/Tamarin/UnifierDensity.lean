import Tamarin.MixedUnification

/-! The variables that an answer of the unifier adds to a query. They are
named by consecutive identifiers from the fresh bound of the query and the
avoided variables, without a gap: the fresh variables of an answer are the
members of a list whose entry `i` has identifier `bound + i`. A family can
therefore leave the 64-bit identifiers only through an answer that uses all
of them from the bound up. -/
namespace Tamarin.UnifierDensity
open VariablePermutation (freshBound lt_freshBound)
variable {s : Signature}

theorem freshBound_append (a b : List Variable) :
    freshBound (a ++ b) = max (freshBound a) (freshBound b) := by
  induction a with
  | nil => simp [freshBound]
  | cons v vs ih => simp only [List.cons_append, freshBound, ih]; omega

theorem freshBound_mono {a b : List Variable} (sub : ∀ v ∈ a, v ∈ b) :
    freshBound a ≤ freshBound b := by
  induction a with
  | nil => exact Nat.zero_le _
  | cons v vs ih =>
    have head := lt_freshBound b v (sub v List.mem_cons_self)
    have tail := ih fun w hw => sub w (List.mem_cons_of_mem _ hw)
    simp only [freshBound]
    omega

/-- A variable of the residual of free factoring is not bound by the
accumulated substitution. -/
theorem unbound {p q : Problem s} {θ ψ : Substitution s} (tr : FactoredUnification.Trace p θ q ψ)
    (start : ∀ u, p.Occurs u → θ.image u = .var u) : ∀ u, q.Occurs u → ψ.image u = .var u := by
  induction tr with
  | done => exact start
  | bind v t ht ho p θ =>
    rintro u ⟨_, hm, occ⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
    let β := Substitution.binding v t ht
    have source (side : Term s) (inSide : e.lhs = side ∨ e.rhs = side)
        (h : (β.apply side).Occurs u) :
        u ≠ v ∧ Problem.Occurs ((⟨.var v, t⟩ : Equation s) :: p) u := by
      obtain ⟨x, hx, hu⟩ := β.occurs_in_image side u h
      by_cases same : x = v
      · subst same
        rw [show β.image x = t from Substitution.binding_image_self ..] at hu
        exact ⟨fun eq => ho (eq ▸ hu), ⟨_, List.mem_cons_self, .inr hu⟩⟩
      · rw [show β.image x = .var x from Substitution.binding_image_other _ _ _ _ same] at hu
        obtain rfl : u = x := hu
        refine ⟨same, ⟨e, List.mem_cons_of_mem _ he, ?_⟩⟩
        rcases inSide with rfl | rfl
        · exact .inl hx
        · exact .inr hx
    obtain ⟨ne, old⟩ : u ≠ v ∧ Problem.Occurs ((⟨.var v, t⟩ : Equation s) :: p) u :=
      occ.elim (source _ (.inl rfl)) (source _ (.inr rfl))
    change β.apply (θ.image u) = _
    rw [start u old]
    exact Substitution.binding_image_other _ _ _ _ ne
  | positional f xs ys p θ =>
    rintro u ⟨e, he, hu⟩
    apply start
    rcases List.mem_append.mp he with hc | hp
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
      exact ⟨_, List.mem_cons_self, hu.imp (fun h => ⟨i, h⟩) (fun h => ⟨i, h⟩)⟩
    · exact ⟨e, List.mem_cons_of_mem _ hp, hu⟩
  | swap a b p θ =>
    rintro u ⟨e, he, hu⟩
    apply start
    rcases List.mem_cons.mp he with rfl | h
    · exact ⟨_, List.mem_cons_self, hu.symm⟩
    · exact ⟨e, List.mem_cons_of_mem _ h, hu⟩
  | discard _ p θ => exact fun u ⟨e, he, hu⟩ => start u ⟨e, List.mem_cons_of_mem _ he, hu⟩
  | perm perm θ => exact fun u ⟨e, he, hu⟩ => start u ⟨e, perm.mem_iff.mpr he, hu⟩
  | trans _ _ ih ik => exact ik (ih start)

/-- A variable outside the query in the image of a query variable. -/
def Fresh (p : Problem s) (σ : Substitution s) (w : Variable) : Prop :=
  ¬ p.Occurs w ∧ ∃ v, p.Occurs v ∧ (σ.image v).Occurs w

/-- The fresh variables of the answer are the members of a list whose entry
`i` has identifier `bound + i`. -/
def Dense (p : Problem s) (bound : Nat) (σ : Substitution s) : Prop :=
  ∃ ws : List Variable, (∀ i (h : i < ws.length), ws[i].id = bound + i) ∧ ∀ w, Fresh p σ w ↔ w ∈ ws

variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

/-- Free factoring keeps the answers of the residual dense: a residual
variable is a query variable that the bindings leave alone, and the bindings
mention query variables only. -/
theorem factored (u : VerifiedUnifier s (fun _ => True)) (p : Problem s) (avoid : List Variable)
    (range : ∀ (q : Problem s) (reserved : List Variable), ∀ σ ∈ u.solve q trivial reserved,
      Dense q (freshBound (q.variables ++ reserved)) σ)
    (τ : Substitution s) (mem : τ ∈ FreeFactoring.solve u p avoid) :
    Dense p (freshBound (p.variables ++ avoid)) τ := by
  rw [FreeFactoring.solve_eq] at mem
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp mem
  let st := FreeFactoring.factor p
  let q := st.todo ++ st.kept
  have scope := st.trace.original_scope
  have free := unbound st.trace (fun _ _ => rfl)
  obtain ⟨ws, ids, members⟩ := range q (p.variables ++ avoid) σ hσ
  have inside : ∀ v ∈ q.variables, v ∈ p.variables := fun v hv =>
    (p.mem_variables v).mpr (scope.pending v ((q.mem_variables v).mp hv))
  have bound : freshBound (q.variables ++ (p.variables ++ avoid)) = freshBound (p.variables ++ avoid) := by
    have le := freshBound_mono inside
    rw [freshBound_append, freshBound_append]
    omega
  have domain := u.domain q trivial (p.variables ++ avoid) σ hσ
  refine ⟨ws, fun i h => bound ▸ ids i h, fun w => ⟨?_, ?_⟩⟩
  · rintro ⟨new, v, live, occ⟩
    obtain ⟨x, hx, hw⟩ := σ.occurs_in_image (st.θ.image v) w occ
    by_cases residual : q.Occurs x
    · exact (members w).mp ⟨fun old => new (scope.pending w old), x, residual, hw⟩
    · rw [domain x residual] at hw
      obtain rfl : w = x := hw
      exact (new (scope.images v live w hx)).elim
  · intro hw
    obtain ⟨-, x, residual, occ⟩ := (members w).mpr hw
    refine ⟨fun old => ?_, x, scope.pending x residual, ?_⟩
    · obtain ⟨i, lt, rfl⟩ := List.getElem_of_mem hw
      have below := lt_freshBound (p.variables ++ avoid) _
        (List.mem_append_left _ ((p.mem_variables _).mpr old))
      have at_i := ids i lt
      rw [bound] at at_i
      omega
    · change (σ.apply (st.θ.image x)).Occurs w
      rw [free x residual]
      exact occ

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
/-- An answer whose image variables are all consecutive from the bound is dense. -/
theorem dense_of_range {q : Problem s} {reserved : List Variable} {σ : Substitution s}
    (range : ∃ ws : List Variable,
      (∀ i (h : i < ws.length), ws[i].id = freshBound (q.variables ++ reserved) + i) ∧
        ∀ w, (∃ v, q.Occurs v ∧ (σ.image v).Occurs w) ↔ w ∈ ws) :
    Dense q (freshBound (q.variables ++ reserved)) σ := by
  obtain ⟨ws, ids, members⟩ := range
  refine ⟨ws, ids, fun w => ⟨fun h => (members w).mp h.2, fun hw => ⟨fun old => ?_, (members w).mpr hw⟩⟩⟩
  obtain ⟨i, lt, rfl⟩ := List.getElem_of_mem hw
  have below := lt_freshBound (q.variables ++ reserved) _
    (List.mem_append_left _ ((q.mem_variables _).mpr old))
  have at_i := ids i lt
  omega

/-- The answers of the residual solver stay dense behind any number of rounds
of forced equalities: these mention variables of the residual only. -/
theorem forcing_dense (k : Nat) (q : Problem s) (reserved : List Variable) (σ : Substitution s)
    (mem : σ ∈ (MixedUnification.forcing (s := s) k).solve q trivial reserved) :
    Dense q (freshBound (q.variables ++ reserved)) σ := by
  have base (q : Problem s) (reserved : List Variable) (σ : Substitution s)
      (mem : σ ∈ (MixedUnification.residual (s := s)).solve q trivial reserved) :
      Dense q (freshBound (q.variables ++ reserved)) σ := by
    change σ ∈ (if q.any NarrowingClash.impossible then []
      else UnifierSorts.solve q (MixedUnification.solve q) reserved) at mem
    split at mem
    · cases mem
    · exact dense_of_range (UnifierSorts.solve_range q _ reserved σ mem)
  induction k generalizing q reserved σ with
  | zero => exact base q reserved σ mem
  | succ k ih =>
    rcases ForcedOperands.solve_cases _ _ q reserved σ mem with direct | ⟨extra, forced, again⟩
    · exact base q reserved σ direct
    · have dense := factored _ (extra ++ q) reserved (fun q' r' τ h => ih q' r' τ h) σ again
      have same (v : Variable) : Problem.Occurs (extra ++ q) v ↔ q.Occurs v := by
        constructor
        · rintro ⟨e, he, occ⟩
          rcases List.mem_append.mp he with he | he
          · exact forced.scope v ⟨e, he, occ⟩
          · exact ⟨e, he, occ⟩
        · rintro ⟨e, he, occ⟩
          exact ⟨e, List.mem_append_right _ he, occ⟩
      have bound : freshBound ((extra ++ q).variables ++ reserved) =
          freshBound (q.variables ++ reserved) := by
        have le := freshBound_mono (a := (extra ++ q).variables) (b := q.variables) fun v hv =>
          (q.mem_variables v).mpr ((same v).mp ((Problem.mem_variables _ v).mp hv))
        have ge := freshBound_mono (a := q.variables) (b := (extra ++ q).variables) fun v hv =>
          (Problem.mem_variables _ v).mpr ((same v).mpr ((q.mem_variables v).mp hv))
        rw [freshBound_append, freshBound_append]
        omega
      obtain ⟨ws, ids, members⟩ := dense
      refine ⟨ws, fun i h => bound ▸ ids i h, fun w => ?_⟩
      rw [← members w]
      simp only [Fresh, same]

/-- The fresh variables of every answer of the unifier are named by the
consecutive identifiers from the fresh bound of the query and the avoided
variables. -/
theorem verified_dense (p : Problem s) (avoid : List Variable) (σ : Substitution s)
    (mem : σ ∈ (MixedUnification.verified (s := s)).solve p trivial avoid) :
    Dense p (freshBound (p.variables ++ avoid)) σ := by
  rw [MixedUnification.verified_solve] at mem
  split at mem
  · cases mem
  · exact factored _ p avoid (fun q reserved τ h => forcing_dense _ q reserved τ h) σ
      (DistinctAnswers.distinct_subset p _ σ mem)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
/-- The distinct fresh variables of a dense answer that contains a variable
whose identifier is at least `limit`: more than `limit - bound` of them. -/
theorem Dense.count {p : Problem s} {bound : Nat} {σ : Substitution s} (dense : Dense p bound σ)
    {limit : Nat} {w : Variable} (fresh : Fresh p σ w) (large : limit ≤ w.id) :
    ∃ ws : List Variable, ws.Nodup ∧ limit - bound < ws.length ∧ ∀ x ∈ ws, Fresh p σ x := by
  obtain ⟨ws, ids, members⟩ := dense
  refine ⟨ws, ?_, ?_, fun x hx => (members x).mpr hx⟩
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj lt eq
    have a := ids i hi
    have b := ids j hj
    have same : ws[i].id = ws[j].id := congrArg Variable.id eq
    omega
  · obtain ⟨i, lt, rfl⟩ := List.getElem_of_mem ((members w).mp fresh)
    have := ids i lt
    omega

end Tamarin.UnifierDensity
