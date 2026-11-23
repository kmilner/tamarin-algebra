import Tamarin.MixedUnification
import Tamarin.ACFeasibility
import Tamarin.Commutative

/-! Whether a unification problem has a unifier, without listing a complete
family. Free factoring and the decomposition of commutative roots reduce the
problem to residuals. A residual in which every side is a sum of variables at
one AC head, all of the sort of that head, is a homogeneous linear system, and
has a unifier exactly when the system has a positive solution. Every other
residual is decided by listing. The verdict is exact in both cases. -/
namespace Tamarin.UnifyExists
variable {s : Signature} [DecidableEq s.Atom] [DecidableEq s.FreeSym] [DecidableEq s.CSym]
  [DecidableEq s.ACSym] [Interrupt]

/-- The variables of a list of terms, if all are variables of the sort of the head. -/
def variablesOf (f : s.ACSym) : List (Term s) → Option (List Variable)
  | [] => some []
  | .var v :: ts => if v.sort = s.acSort f then (variablesOf f ts).map (v :: ·) else none
  | _ :: _ => none

omit [DecidableEq s.Atom] [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] in
omit [Interrupt] in
theorem variablesOf_spec (f : s.ACSym) (ts : List (Term s)) (vs : List Variable)
    (h : variablesOf f ts = some vs) : ts = vs.map Term.var ∧ ∀ v ∈ vs, v.sort = s.acSort f := by
  induction ts generalizing vs with
  | nil =>
    obtain rfl : [] = vs := by simpa [variablesOf] using h
    simp
  | cons t ts ih =>
    cases t with
    | var v =>
      simp only [variablesOf] at h
      split at h
      · next sorted =>
        cases rest : variablesOf f ts with
        | none => simp [rest] at h
        | some ws =>
          obtain rfl : v :: ws = vs := by simpa [rest] using h
          obtain ⟨shape, sorts⟩ := ih ws rest
          refine ⟨by rw [shape]; rfl, fun w hw => ?_⟩
          rcases List.mem_cons.mp hw with rfl | hw
          · exact sorted
          · exact sorts w hw
      · cases h
    | atom | free | comm | ac => simp [variablesOf] at h

/-- A side that is a sum of variables at the head, as a side of a linear row.
A single variable is a sum of one. -/
def sideOf (f : s.ACSym) (t : Term s) : Option ACSystem.Side :=
  match variablesOf f (ACRepresentation.flatten f t) with
  | some (v :: vs) => some ⟨v, vs⟩
  | _ => none

omit [DecidableEq s.Atom] [DecidableEq s.FreeSym] [DecidableEq s.CSym] in
omit [Interrupt] in
theorem sideOf_spec (f : s.ACSym) (t : Term s) (side : ACSystem.Side) (h : sideOf f t = some side) :
    EquivB (side.term f) t ∧ ∀ v ∈ side.vars, v.sort = s.acSort f := by
  unfold sideOf at h
  split at h
  · next v vs found =>
    obtain rfl := Option.some.inj h
    obtain ⟨shape, sorts⟩ := variablesOf_spec f _ _ found
    obtain ⟨u, hu, eq⟩ := ACRepresentation.flatten_correct f t
    rw [shape] at hu
    obtain rfl : ACRepresentation.fold f (.var v) (vs.map Term.var) = u := by
      simpa [ACRepresentation.decode] using hu
    exact ⟨eq, sorts⟩
  · cases h

def rowOf (f : s.ACSym) (e : Equation s) : Option ACSystem.Row :=
  match sideOf f e.lhs, sideOf f e.rhs with
  | some l, some r => some ⟨l, r⟩
  | _, _ => none

/-- The rows of a problem all of whose sides are sums of variables at the head. -/
def rowsOf (f : s.ACSym) : Problem s → Option (List ACSystem.Row)
  | [] => some []
  | e :: es =>
    match rowOf f e, rowsOf f es with
    | some r, some rs => some (r :: rs)
    | _, _ => none

omit [DecidableEq s.Atom] [DecidableEq s.FreeSym] [DecidableEq s.CSym] in
omit [Interrupt] in
theorem rowsOf_spec (f : s.ACSym) (q : Problem s) (rows : List ACSystem.Row)
    (h : rowsOf f q = some rows) :
    (∀ σ : Substitution s, q.Solves σ ↔ (ACSystem.problem f rows).Solves σ) ∧
    ∀ v ∈ ACSystem.variables rows, v.sort = s.acSort f := by
  induction q generalizing rows with
  | nil =>
    obtain rfl : [] = rows := by simpa [rowsOf] using h
    exact ⟨fun σ => Iff.rfl, fun v hv => by simp [ACSystem.variables] at hv⟩
  | cons e es ih =>
    simp only [rowsOf] at h
    split at h
    · next r rs hr hrs =>
      obtain rfl := Option.some.inj h
      obtain ⟨same, sorts⟩ := ih rs hrs
      unfold rowOf at hr
      split at hr
      · next l r' hl hrr =>
        obtain rfl := Option.some.inj hr
        obtain ⟨el, sl⟩ := sideOf_spec f _ _ hl
        obtain ⟨er, sr⟩ := sideOf_spec f _ _ hrr
        constructor
        · intro σ
          have head : EquivB (σ.apply e.lhs) (σ.apply e.rhs) ↔
              EquivB (σ.apply (l.term f)) (σ.apply (r'.term f)) :=
            ⟨fun eq => (el.subst σ.image).trans (eq.trans (er.subst σ.image).symm),
              fun eq => (el.subst σ.image).symm.trans (eq.trans (er.subst σ.image))⟩
          simp only [Problem.Solves, ACSystem.problem, List.map_cons, List.forall_mem_cons]
          exact and_congr head (same σ)
        · intro v hv
          simp only [ACSystem.variables, List.flatMap_cons, List.mem_append] at hv
          rcases hv with (hv | hv) | hv
          · exact sl v hv
          · exact sr v hv
          · exact sorts v hv
      · cases hr
    · cases h

/-- A positive solution of the system, decided by the feasibility checks
where they answer and by the support of the basis otherwise. -/
def feasible {n : Nat} (matrix : List (ACBasis.Row n)) : Bool :=
  match ACFeasibility.checkRows matrix with
  | some b => b
  | none => ACBasis.coversCoordinates (ACBasis.hilbert matrix)

omit [Interrupt] in
theorem feasible_iff {n : Nat} (matrix : List (ACBasis.Row n)) :
    feasible matrix = true ↔ ACFeasibility.Feasible matrix := by
  unfold feasible
  split
  · next b h => exact ACFeasibility.checkedRows matrix b h
  · exact ACBasis.coversCoordinates_iff matrix _ (ACBasis.hilbert_correct matrix)

/-- The head of the first product. -/
def headOf : Problem s → Option s.ACSym
  | [] => none
  | e :: es =>
    match e.lhs, e.rhs with
    | .ac f _ _, _ => some f
    | _, .ac f _ _ => some f
    | _, _ => headOf es

/-- The verdict for a problem between sums of variables at one head. -/
def linear (q : Problem s) : Option Bool :=
  match q with
  | [] => some true
  | _ :: _ =>
    match headOf q with
    | none => none
    | some f =>
      match h : rowsOf f q with
      | none => none
      | some rows =>
        let fr := ACSystem.Reference.frame f rows (rowsOf_spec f q rows h).2
        some (feasible (rows.map (ACBasis.encode fr.names)))

omit [DecidableEq s.Atom] [DecidableEq s.FreeSym] [DecidableEq s.CSym] in
omit [Interrupt] in
theorem linear_sound (q : Problem s) (b : Bool) (h : linear q = some b) :
    b = true ↔ q.Satisfiable := by
  unfold linear at h
  split at h
  · obtain rfl := Option.some.inj h
    exact iff_of_true rfl ⟨.identity, fun e he => nomatch he⟩
  · split at h
    · cases h
    · next f _ =>
      split at h
      · cases h
      · next rows found =>
        obtain rfl := Option.some.inj h
        obtain ⟨same, sorts⟩ := rowsOf_spec f _ rows found
        rw [feasible_iff, ← ACFeasibility.term_feasible_iff f rows]
        exact ⟨fun ⟨σ, sol⟩ => ⟨σ, (same σ).mpr sol⟩, fun ⟨σ, sol⟩ => ⟨σ, (same σ).mp sol⟩⟩

/-- The two alignments of the first equation between applications of one
commutative symbol. -/
def splitComm : Problem s → Option (Problem s × Problem s)
  | [] => none
  | e :: es =>
    match e with
    | ⟨.comm g a b, .comm g' c d⟩ =>
      if g = g' then some (⟨a,c⟩ :: ⟨b,d⟩ :: es, ⟨a,d⟩ :: ⟨b,c⟩ :: es)
      else (splitComm es).map fun alts => (e :: alts.1, e :: alts.2)
    | e => (splitComm es).map fun alts => (e :: alts.1, e :: alts.2)

omit [DecidableEq s.Atom] [DecidableEq s.FreeSym] [DecidableEq s.ACSym] in
omit [Interrupt] in
theorem splitComm_spec (q : Problem s) (alts : Problem s × Problem s) (h : splitComm q = some alts)
    (σ : Substitution s) : q.Solves σ ↔ alts.1.Solves σ ∨ alts.2.Solves σ := by
  induction q generalizing alts with
  | nil => cases h
  | cons e es ih =>
    have tail (found : (splitComm es).map (fun alts => (e :: alts.1, e :: alts.2)) = some alts) :
        Problem.Solves (e :: es) σ ↔ alts.1.Solves σ ∨ alts.2.Solves σ := by
      cases rest : splitComm es with
      | none => simp [rest] at found
      | some inner =>
        obtain rfl : (e :: inner.1, e :: inner.2) = alts := by simpa [rest] using found
        have step := ih inner rest
        simp only [Problem.Solves, List.forall_mem_cons] at step ⊢
        rw [step]
        exact ⟨fun ⟨he, hs⟩ => hs.imp (⟨he, ·⟩) (⟨he, ·⟩),
          fun hs => hs.elim (fun ⟨he, hs⟩ => ⟨he, .inl hs⟩) (fun ⟨he, hs⟩ => ⟨he, .inr hs⟩)⟩
    unfold splitComm at h
    split at h
    · next g a b g' c d =>
      split at h
      · next same =>
        subst same
        obtain rfl := Option.some.inj h
        simp only [Problem.Solves, List.forall_mem_cons]
        have root := Commutative.equiv_iff g (σ.apply a) (σ.apply b) (σ.apply c) (σ.apply d)
        change EquivB (σ.apply (.comm g a b)) (σ.apply (.comm g c d)) ∧ _ ↔ _
        change (EquivB (.comm g (σ.apply a) (σ.apply b)) (.comm g (σ.apply c) (σ.apply d)) ∧ _) ↔ _
        rw [root]
        constructor
        · rintro ⟨(⟨x, y⟩ | ⟨x, y⟩), rest⟩
          · exact .inl ⟨x, y, rest⟩
          · exact .inr ⟨x, y, rest⟩
        · rintro (⟨x, y, rest⟩ | ⟨x, y, rest⟩)
          · exact ⟨.inl ⟨x, y⟩, rest⟩
          · exact ⟨.inr ⟨x, y⟩, rest⟩
      · exact tail h
    · exact tail h

/-- The residual of free factoring, or the verdict when a clash decides. -/
def residual (p : Problem s) : Bool ⊕ Problem s :=
  if p.any NarrowingClash.quick then .inl false
  else
    let st := FreeFactoring.factor p
    let q := st.todo ++ st.kept
    if q.any NarrowingClash.impossible then .inl false else .inr q

omit [Interrupt] in
theorem residual_verdict (p : Problem s) (b : Bool) (h : residual p = .inl b) :
    b = true ↔ p.Satisfiable := by
  unfold residual at h
  split at h
  · next clash =>
    obtain rfl : false = b := by simpa using h
    exact iff_of_false (by simp) ((complete_empty_iff p).mp (NarrowingClash.quick_refutes clash))
  · dsimp only at h
    split at h
    · next clash =>
      obtain rfl : false = b := by simpa using h
      refine iff_of_false (by simp) fun ⟨ρ, sol⟩ => ?_
      exact (complete_empty_iff _).mp (NarrowingClash.refutes clash)
        ⟨ρ, (FreeFactoring.factor p).trace.factoring.residual ρ sol⟩
    · cases h

omit [Interrupt] in
theorem residual_same (p q : Problem s) (h : residual p = .inr q) :
    p.Satisfiable ↔ q.Satisfiable := by
  unfold residual at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · obtain rfl : _ = q := Sum.inr.inj h
      have fact := (FreeFactoring.factor p).trace.factoring
      exact ⟨fun ⟨ρ, sol⟩ => ⟨ρ, fact.residual ρ sol⟩, fun ⟨σ, sol⟩ => ⟨_, fact.forward σ sol⟩⟩

/-- One round: factor, decide a linear residual, or hand the two alignments
of a commutative equation to the continuation. -/
def attempt (p : Problem s) (alternatives : Problem s → Problem s → Option Bool) : Option Bool :=
  match residual p with
  | .inl b => some b
  | .inr q =>
    match linear q with
    | some b => some b
    | none =>
      match splitComm q with
      | none => none
      | some alts => alternatives alts.1 alts.2

omit [Interrupt] in
theorem attempt_sound (p : Problem s) (alternatives : Problem s → Problem s → Option Bool)
    (sound : ∀ a c b, alternatives a c = some b → (b = true ↔ a.Satisfiable ∨ c.Satisfiable))
    (b : Bool) (h : attempt p alternatives = some b) : b = true ↔ p.Satisfiable := by
  unfold attempt at h
  split at h
  · next v verdict =>
    obtain rfl := Option.some.inj h
    exact residual_verdict p _ verdict
  · next q same =>
    rw [residual_same p q same]
    split at h
    · next v found =>
      obtain rfl := Option.some.inj h
      exact linear_sound q _ found
    · split at h
      · cases h
      · next alts found =>
        rw [sound _ _ b h]
        exact ⟨fun yes => yes.elim (fun ⟨σ, sol⟩ => ⟨σ, (splitComm_spec q alts found σ).mpr (.inl sol)⟩)
            (fun ⟨σ, sol⟩ => ⟨σ, (splitComm_spec q alts found σ).mpr (.inr sol)⟩),
          fun ⟨σ, sol⟩ => ((splitComm_spec q alts found σ).mp sol).imp (⟨σ, ·⟩) (⟨σ, ·⟩)⟩

/-- A verdict for either alignment. The second is examined only when the
first has no unifier or no verdict. -/
def either (first : Option Bool) (second : Unit → Option Bool) : Option Bool :=
  match first with
  | some true => some true
  | some false => second ()
  | none => match second () with
    | some true => some true
    | _ => none

/-- The verdict without listing, where the problem reduces to linear
residuals within the given number of nested commutative alignments. -/
def fast : Nat → Problem s → Option Bool
  | 0, p => attempt p fun _ _ => none
  | fuel+1, p => attempt p fun a c => either (fast fuel a) fun _ => fast fuel c

omit [Interrupt] in
theorem fast_sound (fuel : Nat) (p : Problem s) (b : Bool) (h : fast fuel p = some b) :
    b = true ↔ p.Satisfiable := by
  induction fuel generalizing p b with
  | zero => exact attempt_sound p _ (fun _ _ _ h => by simp at h) b h
  | succ fuel ih =>
    apply attempt_sound p _ _ b h
    intro a c v hv
    unfold either at hv
    split at hv
    · next first =>
      obtain rfl := Option.some.inj hv
      exact iff_of_true rfl (.inl ((ih a true first).mp rfl))
    · next first =>
      have none : ¬ a.Satisfiable := fun yes => by
        have := (ih a false first).mpr yes
        cases this
      rw [ih c v hv]
      exact ⟨.inr, fun yes => yes.resolve_left none⟩
    · split at hv
      · next second =>
        obtain rfl := Option.some.inj hv
        exact iff_of_true rfl (.inr ((ih c true second).mp rfl))
      · cases hv

/-- The number of nested commutative alignments decided without listing. -/
def depth : Nat := 16

/-- Whether the problem has a unifier. Listing a complete family decides the
problems that the linear residuals do not. -/
def decide (p : Problem s) : Bool :=
  match fast depth p with
  | some b => b
  | none => !((MixedUnification.verified (s := s)).solve p trivial []).isEmpty

theorem decide_iff (p : Problem s) : decide p = true ↔ p.Satisfiable := by
  unfold decide
  split
  · next b h => exact fast_sound depth p b h
  · have complete := (MixedUnification.verified (s := s)).correct p trivial []
    cases answers : (MixedUnification.verified (s := s)).solve p trivial [] with
    | nil =>
      rw [answers] at complete
      exact iff_of_false (by simp) ((complete_empty_iff p).mp complete)
    | cons σ rest =>
      rw [answers] at complete
      exact iff_of_true (by simp) ⟨σ, complete.sound σ List.mem_cons_self⟩

end Tamarin.UnifyExists
