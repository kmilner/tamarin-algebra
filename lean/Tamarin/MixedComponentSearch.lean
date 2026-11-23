import Tamarin.MixedRigidBranches
import Tamarin.ACReferenceBranch
import Tamarin.NarrowingClash

/-! Combine the homogeneous answers of distinct AC operators on a shared worklist.
The denotation observes the same slots in every child, including slots that disappear
from the pending equations. A deferred child prevents completion of its parent. -/
namespace Tamarin.MixedUnification.ComponentSearch
open OperandBatch.Reference
variable {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

private def sameHead : Constraint s → Constraint s → Bool
  | .atom _ a,.atom _ b => decide (a = b)
  | .free _ f _,.free _ g _ => decide (f = g)
  | .comm _ f ..,.comm _ g .. => decide (f = g)
  | .ac _ f ..,.ac _ g .. => decide (f = g)
  | _,_ => false

private def compatible (cs : List (Constraint s)) :=
  cs.all fun a => cs.all fun b => a.out != b.out || sameHead a b

private theorem model_compatible (q : System s) {V} (h : q.Model V) : compatible q.constraints := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  by_cases eq : a.out = b.out
  · have lhs := h a ha
    have rhs := h b hb
    unfold Constraint.Holds at lhs rhs
    rw [eq] at lhs
    have heads := (lhs.symm.trans rhs).head_eq
    simp [eq]
    cases a <;> cases b <;> simp_all [sameHead,Constraint.term,headModel,Model.eval]
  · simp [eq]

private def anchors (vs : List Variable) : Problem s := vs.map fun v => ⟨.var v,.var v⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] [DecidableEq s.ACSym] in
private theorem anchored (p : Problem s) (vs : List Variable) (v) (h : v ∈ vs) :
    (p ++ anchors vs).Occurs v :=
  ⟨⟨.var v,.var v⟩,List.mem_append_right _ (List.mem_map_of_mem h),.inl rfl⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] [DecidableEq s.ACSym] in
private theorem solves_anchored (p : Problem s) (vs) (δ : Substitution s) :
    (p ++ anchors vs).Solves δ ↔ p.Solves δ := by
  constructor
  · exact fun h e he => h e (List.mem_append_left _ he)
  · intro h e he
    rcases List.mem_append.mp he with he | he
    · exact h e he
    · obtain ⟨_,_,rfl⟩ := List.mem_map.mp he; exact .refl _

abbrev Exact (p : Problem s) (observe : List Variable) (answers : List (Substitution s)) :=
  ∀ ρ, Residual.Denotes (· ∈ observe) p .identity ρ ↔
    ∃ σ ∈ answers, Substitution.InstanceOn (· ∈ observe) ρ σ

private def direct (p : Problem s) : RigidBranches.Certified p := by
  let q := purify p
  if ok : compatible q.constraints then
    exact ⟨reconstructOf q,fun _ => reconstruct_correct⟩
  else
    refine ⟨some [],?_⟩
    rintro _ ⟨⟩
    refine ⟨by simp,fun δ hd => ?_⟩
    obtain ⟨_,model,_⟩ := extend_solution p δ.image hd
    exact False.elim (ok (model_compatible _ model))

private def leaf (p : Problem s) (observe : List Variable) :
    {r : Option (List (Substitution s)) // ∀ ans, r = some ans → Exact p observe ans} := by
  let a := p ++ anchors observe
  let raw := direct a
  match hr : raw.val with
  | none => exact ⟨none,by simp⟩
  | some rows =>
    let ans := UnifierSorts.solve a rows []
    have cert := (UnifierSorts.correct a rows (raw.property _ hr) []).mathematical
    refine ⟨some ans,?_⟩
    rintro _ ⟨⟩ ρ
    constructor
    · rintro ⟨δ,hd,agree⟩
      obtain ⟨σ,hσ,μ,hm⟩ := cert.covers δ ((solves_anchored ..).mpr hd)
      exact ⟨σ,hσ,μ,fun v hv => (agree v hv).trans (hm v (anchored p observe v hv))⟩
    · rintro ⟨σ,hσ,μ,hm⟩
      exact ⟨μ.compose σ,p.solves_compose ((solves_anchored ..).mp (cert.sound σ hσ)) μ,hm⟩

/-- Sufficient structural coverage for a leaf. Either two rigid heads clash
at a slot, or every competing definition agrees modulo B for all slot values. -/
def ConstructorDecided (p : Problem s) (obs : List Variable) : Prop :=
  let cs := (purify (p ++ anchors (s := s) obs)).constraints
  compatible cs = false ∨ AgreeingDefinitions cs

private theorem leaf_completes (p : Problem s) (obs) (h : ConstructorDecided p obs) :
    (leaf p obs).val.isSome := by
  let a := p ++ anchors (s := s) obs
  have ha : (direct a).val.isSome := by
    unfold direct
    dsimp only
    split
    next ok =>
      rcases h with bad | agree
      · change compatible (purify a).constraints = false at bad; simp_all
      · exact reconstructs_agreeing a agree
    next => rfl
  obtain ⟨rows,hr⟩ := Option.isSome_iff_exists.mp ha
  dsimp only [a] at hr
  unfold leaf
  dsimp only
  split <;> simp_all

private def selected (f : s.ACSym) (e : Equation s) : Bool :=
  match e.rhs with
  | .ac g _ _ => decide (f = g) && e.lhs.checkSort (s.acSort f) && e.rhs.checkSort (s.acSort f)
  | _ => false

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] in
private theorem selected_sort {f : s.ACSym} {e : Equation s} (h : selected f e) :
    HasSort e.lhs (s.acSort f) ∧ HasSort e.rhs (s.acSort f) := by
  unfold selected at h
  split at h <;> simp_all only [Bool.and_eq_true, Bool.false_eq_true]
  exact ⟨Term.checkSort_sound _ _ h.1.2, Term.checkSort_sound _ _ h.2⟩

private def children (p : Problem s) (f : s.ACSym) (observe : List Variable) :
    {cs : List (Problem s) // ∀ ρ,
      Residual.Denotes (· ∈ observe) p .identity ρ ↔
        ∃ c ∈ cs, Residual.Denotes (· ∈ observe) c .identity ρ} := by
  let sel := p.filter (selected f)
  let pending := p.filter (fun e => !(selected f e))
  have perm : p.Perm (sel ++ pending) := (List.filter_append_perm (selected f) p).symm
  have hs : SortedAt f sel := fun _ he => selected_sort (List.mem_filter.mp he).2
  -- A branch that equates a product with a different head or an impossible
  -- sort has no solution. Drop it before the remaining heads multiply it.
  refine ⟨(splitProblem f sel hs pending observe [] .identity).filter
      (fun c => !c.any NarrowingClash.impossible), fun ρ =>
    (splitProblem_correct f sel hs pending p perm observe [] .identity ρ).trans ⟨?_,?_⟩⟩
  · rintro ⟨c,hc,hd⟩
    refine ⟨c,List.mem_filter.mpr ⟨hc,?_⟩,hd⟩
    obtain ⟨δ,sol,_⟩ := hd
    cases bad : c.any NarrowingClash.impossible with
    | false => rfl
    | true => exact ((complete_empty_iff c).mp (NarrowingClash.refutes bad) ⟨δ,sol⟩).elim
  · rintro ⟨c,hc,hd⟩
    exact ⟨c,(List.mem_filter.mp hc).1,hd⟩

/-- Generate the entire residual family, independently of whether reconstruction
can close each leaf. The head list decreases at every homogeneous split. -/
def frontier (heads : List s.ACSym) (p : Problem s) (observe : List Variable) :
    {cs : List (Problem s) // ∀ ρ, Residual.Denotes (· ∈ observe) p .identity ρ ↔
      ∃ c ∈ cs, Residual.Denotes (· ∈ observe) c .identity ρ} := by
  match heads with
  | [] =>
    let r := RigidBranches.refineProblem p
    refine ⟨r.val,fun ρ => ⟨?_,?_⟩⟩
    · rintro ⟨δ,hs,agree⟩
      obtain ⟨c,hc,sol⟩ := r.property.2 δ.image hs
      exact ⟨c,hc,δ,sol,agree⟩
    · rintro ⟨c,hc,δ,hs,agree⟩
      exact ⟨δ,fun e he => hs e (r.property.1 c hc e he),agree⟩
  | f :: fs =>
    let cs := children p f observe
    let tail := fun c => frontier fs c observe
    refine ⟨cs.val.flatMap (fun c => (tail c).val),fun ρ => (cs.property ρ).trans ⟨?_,?_⟩⟩
    · rintro ⟨c,hc,hd⟩
      obtain ⟨d,mem,sol⟩ := ((tail c).property ρ).mp hd
      exact ⟨d,List.mem_flatMap.mpr ⟨c,hc,mem⟩,sol⟩
    · rintro ⟨d,mem,sol⟩
      obtain ⟨c,hc,hd⟩ := List.mem_flatMap.mp mem
      exact ⟨c,hc,((tail c).property ρ).mpr ⟨d,hd,sol⟩⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem ac_of_equiv {t : Term s} {f : s.ACSym} {a b : Term s} (h : EquivB t (.ac f a b)) :
    ∃ c d, t = .ac f c d := by
  have root := h.head_eq
  cases t <;> simp_all [Model.eval, headModel]

/-- A variable that one equation identifies with `x`. -/
private def link (x : Variable) : Equation s → Option Variable
  | ⟨.var a, .var b⟩ => if a = x then some b else if b = x then some a else none
  | _ => none

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
private theorem link_equiv {δ : Substitution s} {e : Equation s}
    (eq : EquivB (δ.apply e.lhs) (δ.apply e.rhs)) {x y : Variable} (h : link x e = some y) :
    EquivB (δ.image x) (δ.image y) := by
  unfold link at h
  split at h
  · split at h
    · next ha => cases h; subst ha; exact eq
    · split at h
      · next hb => cases h; subst hb; exact eq.symm
      · cases h
  · cases h

/-- A non-variable term that one equation identifies with `x`. -/
private def definition (x : Variable) : Equation s → Option (Term s)
  | ⟨.var _, .var _⟩ => none
  | ⟨.var a, t⟩ => if a = x then some t else none
  | ⟨t, .var b⟩ => if b = x then some t else none
  | _ => none

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
private theorem definition_equiv {δ : Substitution s} {e : Equation s}
    (eq : EquivB (δ.apply e.lhs) (δ.apply e.rhs)) {x : Variable} {t : Term s}
    (h : definition x e = some t) : EquivB (δ.image x) (δ.apply t) := by
  unfold definition at h
  split at h
  · cases h
  · split at h
    · next ha => cases h; subst ha; exact eq
    · cases h
  · split at h
    · next hb => cases h; subst hb; exact eq.symm
    · cases h
  · cases h

/-- Variables within two alias steps of `x`. A residual witness links the
operand columns that share it. -/
private def near (c : Problem s) (x : Variable) : List Variable :=
  let one := c.filterMap (link x)
  x :: (one ++ one.flatMap fun y => c.filterMap (link y))

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
private theorem near_equiv {c : Problem s} {δ : Substitution s} (sol : c.Solves δ)
    {x y : Variable} (h : y ∈ near c x) : EquivB (δ.image x) (δ.image y) := by
  rcases List.mem_cons.mp h with rfl | h
  · exact .refl _
  · rcases List.mem_append.mp h with h | h
    · obtain ⟨e,he,hit⟩ := List.mem_filterMap.mp h
      exact link_equiv (sol e he) hit
    · obtain ⟨z,hz,h⟩ := List.mem_flatMap.mp h
      obtain ⟨e,he,hit⟩ := List.mem_filterMap.mp hz
      obtain ⟨e',he',hit'⟩ := List.mem_filterMap.mp h
      exact (link_equiv (sol e he) hit).trans (link_equiv (sol e' he') hit')

private def rigid (c : Problem s) (x : Variable) : List (Term s) :=
  (near c x).flatMap fun y => c.filterMap (definition y)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
private theorem rigid_equiv {c : Problem s} {δ : Substitution s} (sol : c.Solves δ)
    {x : Variable} {t : Term s} (h : t ∈ rigid c x) : EquivB (δ.image x) (δ.apply t) := by
  obtain ⟨y,hy,h⟩ := List.mem_flatMap.mp h
  obtain ⟨e,he,hit⟩ := List.mem_filterMap.mp h
  exact (near_equiv sol hy).trans (definition_equiv (sol e he) hit)

/-- Outer constructors that an admissible solution never gives to a slot: the
slot stands for a sorted variable, and no term of that head has its sort. -/
def Shaped (ban : Variable → Head s → Bool) (ρ : Substitution s) : Prop :=
  ∀ y h, ban y h = true → (headModel s).eval Head.var (ρ.image y) ≠ h

/-- The rigid head of the term is banned at the slot. -/
private def banned (ban : Variable → Head s → Bool) (y : Variable) : Term s → Bool
  | .var _ => false
  | t => ban y ((headModel s).eval Head.var t)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
private theorem unbanned {ban : Variable → Head s → Bool} {obs : List Variable}
    {ρ δ : Substitution s} (inside : ∀ y h, ban y h = true → y ∈ obs) (shaped : Shaped ban ρ)
    (agree : ∀ v, v ∈ obs → EquivB (ρ.image v) (δ.apply (Substitution.identity.image v)))
    {y : Variable} {t : Term s} (eq : EquivB (δ.image y) (δ.apply t)) : banned ban y t = false := by
  cases hb : banned ban y t with
  | false => rfl
  | true =>
    exfalso
    cases t with
    | var => simp [banned] at hb
    | _ => exact shaped y _ hb ((agree y (inside y _ hb)).trans eq).head_eq

/-- A homogeneous split writes each operand on the right of its equation. -/
private def operand : Equation s → Option Variable
  | ⟨_, .var x⟩ => some x
  | _ => none

/-- Some operand is equated with two rigid terms of different heads, or with a
rigid term whose head is banned at one of its aliases. -/
private def excluded (ban : Variable → Head s → Bool) (c : Problem s) : Bool :=
  (c.filterMap operand).any fun x =>
    let ts := rigid c x
    ts.any (fun a => ts.any (NarrowingClash.clash a)) ||
      (near c x).any fun y => ts.any (banned ban y)

private theorem admitted {ban : Variable → Head s → Bool} {obs : List Variable} {c : Problem s}
    {ρ : Substitution s} (inside : ∀ y h, ban y h = true → y ∈ obs) (shaped : Shaped ban ρ)
    (hd : Residual.Denotes (· ∈ obs) c .identity ρ) : excluded ban c = false := by
  obtain ⟨δ,sol,agree⟩ := hd
  cases bad : excluded ban c with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨x,-,hx⟩ := List.any_eq_true.mp bad
    rcases Bool.or_eq_true_iff.mp hx with pair | sort
    · obtain ⟨a,ha,inner⟩ := List.any_eq_true.mp pair
      obtain ⟨b,hb,cl⟩ := List.any_eq_true.mp inner
      have eq := (rigid_equiv sol ha).symm.trans (rigid_equiv sol hb)
      simp [NarrowingClash.no_clash a b δ eq] at cl
    · obtain ⟨y,hy,prod⟩ := List.any_eq_true.mp sort
      obtain ⟨t,ht,pt⟩ := List.any_eq_true.mp prod
      have no := unbanned inside shaped agree ((near_equiv sol hy).symm.trans (rigid_equiv sol ht))
      rw [pt] at no
      cases no

/-- What the pending equations say about an operand: the rigid terms it is
equated with, and its aliases. -/
private def tagOf (pending : Problem s) : Term s → List (Term s) × List Variable
  | .var x => (rigid pending x, near pending x)
  | _ => ([], [])

/-- The two operands cannot be equal. -/
private def conflictTag (ban : Variable → Head s → Bool) (a b : List (Term s) × List Variable) : Bool :=
  a.1.any (fun t => b.1.any (NarrowingClash.clash t)) ||
    a.2.any (fun y => b.1.any (banned ban y)) || b.2.any (fun y => a.1.any (banned ban y))

/-- The operand cannot be a product at `f`. -/
private def capTag (ban : Variable → Head s → Bool) (f : s.ACSym)
    (t : List (Term s) × List Variable) : Bool :=
  t.2.any (fun y => ban y (.ac f)) || t.1.any (fun a => NarrowingClash.clash a (.ac f a a)) ||
    conflictTag ban t t

private theorem clash_ac (t : Term s) (f : s.ACSym) (a b c d : Term s) :
    NarrowingClash.clash t (.ac f a b) = NarrowingClash.clash t (.ac f c d) := by
  cases t <;> rfl

/-- The children of a homogeneous split, without the branches that equate a
capped operand with a product or identify two conflicting operands. The
selection of basis generators never builds those branches. -/
private def childrenWith (ban : Variable → Head s → Bool) (p : Problem s)
    (f : s.ACSym) (observe : List Variable) : List (Problem s) :=
  let sel := p.filter (selected f)
  let pending := p.filter (fun e => !(selected f e))
  have hs : SortedAt f sel := fun _ he => selected_sort (List.mem_filter.mp he).2
  (splitProblemWith f sel hs pending observe [] .identity
      (tagOf pending) (capTag ban f) (conflictTag ban)).filter
    (fun c => !c.any NarrowingClash.impossible)

private theorem childrenWith_subset {ban : Variable → Head s → Bool} {p : Problem s}
    {f : s.ACSym} {observe : List Variable} {c : Problem s}
    (h : c ∈ childrenWith ban p f observe) : c ∈ (children p f observe).val := by
  obtain ⟨hc,ok⟩ := List.mem_filter.mp h
  exact List.mem_filter.mpr ⟨splitProblemWith_subset hc,ok⟩

/-- Operands with conflicting tags have different values in every admissible solution. -/
private theorem no_conflict {ban : Variable → Head s → Bool} {obs : List Variable}
    {pending : Problem s} {ρ δ : Substitution s} (inside : ∀ y h, ban y h = true → y ∈ obs)
    (shaped : Shaped ban ρ)
    (agree : ∀ v, v ∈ obs → EquivB (ρ.image v) (δ.apply (Substitution.identity.image v)))
    (sol : pending.Solves δ) {x y : Variable} (same : EquivB (δ.image x) (δ.image y)) :
    conflictTag ban (tagOf pending (.var x)) (tagOf pending (.var y)) = false := by
  cases bad : conflictTag ban (tagOf pending (.var x)) (tagOf pending (.var y)) with
  | false => rfl
  | true =>
    exfalso
    simp only [conflictTag, tagOf, Bool.or_eq_true] at bad
    rcases bad with (pair | sort) | sort
    · obtain ⟨a,ha,inner⟩ := List.any_eq_true.mp pair
      obtain ⟨b,hb,cl⟩ := List.any_eq_true.mp inner
      have eq := (rigid_equiv sol ha).symm.trans (same.trans (rigid_equiv sol hb))
      simp [NarrowingClash.no_clash a b δ eq] at cl
    · obtain ⟨z,hz,inner⟩ := List.any_eq_true.mp sort
      obtain ⟨t,ht,pt⟩ := List.any_eq_true.mp inner
      have no := unbanned inside shaped agree
        ((near_equiv sol hz).symm.trans (same.trans (rigid_equiv sol ht)))
      rw [pt] at no
      cases no
    · obtain ⟨z,hz,inner⟩ := List.any_eq_true.mp sort
      obtain ⟨t,ht,pt⟩ := List.any_eq_true.mp inner
      have no := unbanned inside shaped agree
        ((near_equiv sol hz).symm.trans (same.symm.trans (rigid_equiv sol ht)))
      rw [pt] at no
      cases no

private theorem childrenWith_covers {ban : Variable → Head s → Bool} {obs : List Variable}
    (inside : ∀ y h, ban y h = true → y ∈ obs) {p : Problem s} {f : s.ACSym} {c : Problem s}
    {ρ : Substitution s} (shaped : Shaped ban ρ) (hc : c ∈ (children p f obs).val)
    (hd : Residual.Denotes (· ∈ obs) c .identity ρ) : c ∈ childrenWith ban p f obs := by
  obtain ⟨member,ok⟩ := List.mem_filter.mp hc
  apply Classical.byContradiction
  intro absent
  have out := fun h => absent (List.mem_filter.mpr ⟨h,ok⟩)
  obtain ⟨δ,sol,agree⟩ := hd
  have rest : Problem.Solves (p.filter (fun e => !(selected f e))) δ :=
    fun e he => sol e (splitProblem_pending member e he)
  rcases splitProblemWith_missing member out with ⟨t,capped,a,b,eq⟩ | ⟨t,u,conflict,w,et,eu⟩
  · have val := sol _ eq
    cases t with
    | var x =>
      simp only [capTag, Bool.or_eq_true] at capped
      rcases capped with (sort | pair) | self
      · obtain ⟨y,hy,by_sort⟩ := List.any_eq_true.mp sort
        exact shaped y _ by_sort ((agree y (inside y _ by_sort)).trans
          ((near_equiv rest hy).symm.trans val.symm)).head_eq
      · obtain ⟨r,hr,cl⟩ := List.any_eq_true.mp pair
        have no := NarrowingClash.no_clash r (.ac f a b) δ ((rigid_equiv rest hr).symm.trans val.symm)
        rw [clash_ac r f a b r r, cl] at no
        cases no
      · rw [no_conflict inside shaped agree rest (.refl _)] at self
        cases self
    | _ => simp [tagOf, capTag, conflictTag] at capped
  · cases t with
    | var x =>
      cases u with
      | var y =>
        have ex := sol _ et
        have ey := sol _ eu
        rw [no_conflict inside shaped agree rest (ex.symm.trans ey)] at conflict
        cases conflict
      | _ => simp [tagOf, conflictTag] at conflict
    | _ => simp [tagOf, conflictTag] at conflict

/-- The residual family without the branches that no admissible solution reaches. -/
def pruned (ban : Variable → Head s → Bool) :
    List s.ACSym → Problem s → List Variable → List (Problem s)
  | [], p, _ => (RigidBranches.refineProblem p).val
  | f :: rest, p, observe =>
    ((childrenWith ban p f observe).filter fun c => !excluded ban c).flatMap fun c =>
      pruned ban rest c observe

theorem pruned_subset (ban : Variable → Head s → Bool) (heads : List s.ACSym)
    (p : Problem s) (observe : List Variable) :
    ∀ c ∈ pruned ban heads p observe, c ∈ (frontier heads p observe).val := by
  induction heads generalizing p with
  | nil => intro c hc; exact hc
  | cons f rest ih =>
    intro d hd
    obtain ⟨c,hc,mem⟩ := List.mem_flatMap.mp hd
    exact List.mem_flatMap.mpr ⟨c,childrenWith_subset (List.mem_filter.mp hc).1,ih c d mem⟩

theorem pruned_covers {ban : Variable → Head s → Bool} {observe : List Variable}
    (inside : ∀ y h, ban y h = true → y ∈ observe) (heads : List s.ACSym) (p : Problem s)
    (ρ : Substitution s) (shaped : Shaped ban ρ)
    (hd : Residual.Denotes (· ∈ observe) p .identity ρ) :
    ∃ c ∈ pruned ban heads p observe, Residual.Denotes (· ∈ observe) c .identity ρ := by
  induction heads generalizing p with
  | nil => exact ((frontier [] p observe).property ρ).mp hd
  | cons f rest ih =>
    obtain ⟨c,hc,cd⟩ := ((children p f observe).property ρ).mp hd
    obtain ⟨d,mem,dd⟩ := ih c cd
    refine ⟨d,List.mem_flatMap.mpr ⟨c,List.mem_filter.mpr
      ⟨childrenWith_covers inside shaped hc cd,?_⟩,mem⟩,dd⟩
    simp [admitted inside shaped cd]

/-- A blocked leaf can instead force identifications of observed slots. Look
only for literal aliases in the purified leaf, and report all of them at once.
Anchoring both variables prevents an absent variable from being mistaken for
an alias. -/
private def forced {ι : Type} (key : ι → Variable × Variable)
    (c : Problem s) (obs : List Variable) (candidates : List ι) :
    {is : List ι // ∀ i ∈ is, i ∈ candidates ∧ ∀ ρ : Substitution s,
      Residual.Denotes (· ∈ obs) c .identity ρ →
      EquivB (ρ.image (key i).1) (ρ.image (key i).2)} := by
  let a := c ++ anchors (s := s) obs
  let k := (purify a).slot
  let test (i : ι) := let (x,y) := key i
    x != y && obs.contains x && obs.contains y && k (.var x) == k (.var y)
  refine ⟨candidates.filter test,?_⟩
  intro i hi
  have yes := (List.mem_filter.mp hi).2
  simp only [test,Bool.and_eq_true,List.contains_iff_mem,beq_iff_eq] at yes
  refine ⟨(List.mem_filter.mp hi).1,?_⟩
  rintro ρ ⟨δ,hd,agree⟩
  obtain ⟨V,values⟩ := inventory_values a δ.image ((solves_anchored ..).mpr hd)
  have atSlot (v) (hv : v ∈ obs) : EquivB (ρ.image v) (V (k (.var v))) :=
    (agree v hv).trans (values _ (var_in_inventory (anchored c obs v hv)))
  have left := atSlot _ yes.1.1.2
  rw [yes.2] at left
  exact left.trans (atSlot _ yes.1.2).symm

/-- Each entry either solves the remaining equations or requests a nonempty
set of original equalities. Together the entries cover every denoted input. -/
abbrev Report {ι : Type} (key : ι → Variable × Variable) (cs : List ι)
    (p : Problem s) (obs : List Variable) :=
  {r : Option (List (Substitution s ⊕ List ι)) // ∀ as, r = some as →
      (∀ is, Sum.inr is ∈ as → is ≠ [] ∧ ∀ i ∈ is, i ∈ cs) ∧
      (∀ σ, Sum.inl σ ∈ as → Residual.Denotes (· ∈ obs) p .identity σ) ∧
      ∀ ρ, Residual.Denotes (· ∈ obs) p .identity ρ →
        (∃ σ, Sum.inl σ ∈ as ∧ Substitution.InstanceOn (· ∈ obs) ρ σ) ∨
        ∃ is, Sum.inr is ∈ as ∧ ∀ i ∈ is, EquivB (ρ.image (key i).1) (ρ.image (key i).2)}

/-- The report of a leaf that reconstruction closes. -/
private def solved {ι : Type} (key : ι → Variable × Variable) (cs : List ι)
    (p : Problem s) (obs : List Variable) (rows : List (Substitution s))
    (hr : (leaf p obs).val = some rows) : Report key cs p obs := by
  refine ⟨some (rows.map Sum.inl),?_⟩
  rintro _ ⟨⟩
  simp
  refine ⟨?_,?_⟩
  · intro σ hm
    exact ((leaf p obs).property rows hr σ).mpr ⟨σ,hm,Substitution.instanceOn_refl _ _⟩
  · intro ρ h
    exact ((leaf p obs).property rows hr ρ).mp h

/-- The report of a blocked leaf. The candidate equalities are needed only
here, so the list is built on first use. -/
private def request {ι : Type} (key : ι → Variable × Variable)
    (cs : Thunk (List ι)) (p : Problem s) (obs : List Variable) :
    Report key cs.get p obs := by
  match hf : (forced key p obs cs.get).val with
  | [] => exact ⟨none,by simp⟩
  | i :: is =>
    refine ⟨some [.inr (i :: is)],?_⟩
    rintro _ ⟨⟩
    have all := (forced key p obs cs.get).property
    rw [hf] at all
    simp only [List.mem_singleton, reduceCtorEq, false_imp_iff, implies_true, Sum.inr.injEq,
      false_and, exists_false, false_or, true_and]
    refine ⟨?_,?_⟩
    · rintro _ rfl
      exact ⟨by simp,fun j hj => (all j hj).1⟩
    · intro ρ h
      exact ⟨_,rfl,fun j hj => (all j hj).2 ρ h⟩

private def finish {ι : Type} (key : ι → Variable × Variable)
    (cs : Thunk (List ι)) (p : Problem s) (obs : List Variable) :
    Report key cs.get p obs :=
  match hr : (leaf p obs).val with
  | some rows => solved key cs.get p obs rows hr
  | none => request key cs p obs

/-- A report that need only account for the admissible solutions. -/
abbrev Guarded {ι : Type} (key : ι → Variable × Variable) (cs : List ι)
    (ban : Variable → Head s → Bool) (p : Problem s) (obs : List Variable) :=
  {r : Option (List (Substitution s ⊕ List ι)) // ∀ as, r = some as →
      (∀ is, Sum.inr is ∈ as → is ≠ [] ∧ ∀ i ∈ is, i ∈ cs) ∧
      (∀ σ, Sum.inl σ ∈ as → Residual.Denotes (· ∈ obs) p .identity σ) ∧
      ∀ ρ, Shaped ban ρ → Residual.Denotes (· ∈ obs) p .identity ρ →
        (∃ σ, Sum.inl σ ∈ as ∧ Substitution.InstanceOn (· ∈ obs) ρ σ) ∨
        ∃ is, Sum.inr is ∈ as ∧ ∀ i ∈ is, EquivB (ρ.image (key i).1) (ρ.image (key i).2)}

/-- A report for every denoted input accounts for the admissible ones. -/
private def relax {ι : Type} {key : ι → Variable × Variable} {cs : List ι}
    {ban : Variable → Head s → Bool} {p : Problem s} {obs : List Variable}
    (r : Report key cs p obs) : Guarded key cs ban p obs :=
  ⟨r.val,fun as hr => ⟨(r.property as hr).1,(r.property as hr).2.1,
    fun ρ _ hd => (r.property as hr).2.2 ρ hd⟩⟩

/-- A report of a problem with the same denotation. -/
private def transport {ι : Type} {key : ι → Variable × Variable} {cs : List ι}
    {ban : Variable → Head s → Bool} {p p' : Problem s} {obs : List Variable}
    (same : ∀ ρ, Residual.Denotes (· ∈ obs) p .identity ρ ↔ Residual.Denotes (· ∈ obs) p' .identity ρ)
    (r : Guarded key cs ban p' obs) : Guarded key cs ban p obs :=
  ⟨r.val,fun as hr => ⟨(r.property as hr).1,fun σ hm => (same σ).mpr ((r.property as hr).2.1 σ hm),
    fun ρ shaped hd => (r.property as hr).2.2 ρ shaped ((same ρ).mp hd)⟩⟩

/-- Collect the reports of the residual family of a problem. -/
private def analyzeWith {ι : Type} (key : ι → Variable × Variable) (cs : List ι)
    (heads : List s.ACSym) (obs : List Variable)
    (ban : Variable → Head s → Bool) (inside : ∀ y h, ban y h = true → y ∈ obs)
    (visit : ∀ c : Problem s, Guarded key cs ban c obs) (p : Problem s) :
    Guarded key cs ban p obs := by
  let fs := pruned ban heads p obs
  match RigidBranches.collect (fun c => (visit c).val) fs with
  | none => exact ⟨none,by simp⟩
  | some out =>
    refine ⟨some out.val,?_⟩
    rintro _ ⟨⟩
    refine ⟨?_,?_,?_⟩
    · intro i hi
      obtain ⟨c,_,ans,hr,mem⟩ := out.property.2 _ hi
      exact ((visit c).property ans hr).1 i mem
    · intro σ hm
      obtain ⟨c,hc,ans,hr,mem⟩ := out.property.2 _ hm
      exact ((frontier heads p obs).property σ).mpr
        ⟨c,pruned_subset ban heads p obs c hc,((visit c).property ans hr).2.1 σ mem⟩
    · intro ρ flat h
      obtain ⟨c,hc,hd⟩ := pruned_covers inside heads p ρ flat h
      obtain ⟨ans,hr,sub⟩ := out.property.1 c hc
      rcases ((visit c).property ans hr).2.2 ρ flat hd with ⟨σ,hm,agree⟩ | ⟨i,hm,eq⟩
      · exact .inl ⟨σ,sub hm,agree⟩
      · exact .inr ⟨i,sub hm,eq⟩

/-- A product equated with a variable of one of the given slots. -/
private def contested (bad : Nat → Bool) (k : Term s → Nat) : Equation s → Bool
  | ⟨.ac _ _ _, .var x⟩ => bad (k (.var x))
  | _ => false

/-- Write the equation over the given class representatives, with the product
on the right, and link each renamed variable to its representative. -/
private def restate (r : Variable → Variable) (e : Equation s) : Problem s :=
  ⟨e.rhs.subst (fun v => .var (r v)), e.lhs.subst (fun v => .var (r v))⟩ ::
    ((e.lhs.variables ++ e.rhs.variables).filter (fun v => r v != v)).map
      (fun v => ⟨.var v, .var (r v)⟩)

/-- Restate the picked equations. The homogeneous split then sees one column
for all the aliases of a variable. -/
private def realign (pick : Equation s → Bool) (r : Variable → Variable) (c : Problem s) : Problem s :=
  c.flatMap fun e => if pick e then restate r e else [e]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
private theorem renamed (r : Variable → Variable) (δ : Substitution s) (t : Term s)
    (same : ∀ v, t.Occurs v → EquivB (δ.image v) (δ.image (r v))) :
    EquivB (δ.apply t) (δ.apply (t.subst (fun v => .var (r v)))) := by
  unfold Substitution.apply
  rw [Term.subst_comp]
  exact Term.subst_equiv _ _ t same

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
private theorem realign_solves (pick : Equation s → Bool) (r : Variable → Variable) (c : Problem s)
    (δ : Substitution s)
    (same : c.Solves δ → ∀ v, c.Occurs v → EquivB (δ.image v) (δ.image (r v))) :
    c.Solves δ ↔ (realign pick r c).Solves δ := by
  constructor
  · intro sol e' he'
    obtain ⟨e,he,mem⟩ := List.mem_flatMap.mp he'
    have alias (v) (hv : e.lhs.Occurs v ∨ e.rhs.Occurs v) := same sol v ⟨e,he,hv⟩
    split at mem
    · rcases List.mem_cons.mp mem with head | link
      · rw [head]
        exact (renamed r δ e.rhs (fun v hv => alias v (.inr hv))).symm.trans
          ((sol e he).symm.trans (renamed r δ e.lhs (fun v hv => alias v (.inl hv))))
      · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp link
        have occ := (List.mem_filter.mp hv).1
        simp only [List.mem_append, Term.mem_variables] at occ
        exact alias v occ
    · rw [List.mem_singleton.mp mem]
      exact sol e he
  · intro sol e he
    by_cases picked : pick e = true
    · have inside : ∀ e' ∈ restate r e, e' ∈ realign pick r c := fun e' h =>
        List.mem_flatMap.mpr ⟨e,he,by simpa [picked] using h⟩
      have alias (v) (hv : e.lhs.Occurs v ∨ e.rhs.Occurs v) :
          EquivB (δ.image v) (δ.image (r v)) := by
        by_cases fixed : r v = v
        · rw [fixed]; exact .refl _
        · exact sol _ (inside _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨v,List.mem_filter.mpr
            ⟨by simpa only [List.mem_append, Term.mem_variables] using hv,by simpa using fixed⟩,rfl⟩)))
      exact (renamed r δ e.lhs (fun v hv => alias v (.inl hv))).trans
        ((sol _ (inside _ List.mem_cons_self)).symm.trans
          (renamed r δ e.rhs (fun v hv => alias v (.inr hv))).symm)
    · exact sol e (List.mem_flatMap.mpr ⟨e,he,by simp [picked]⟩)

/-- The first listed variable of the slot, or the variable itself. -/
private def representative (k : Term s → Nat) (table : List (Nat × Variable)) (v : Variable) : Variable :=
  let i := k (.var v)
  match table.find? (fun z => z.1 == i) with
  | some z => z.2
  | none => v

/-- The variables among the terms, with their slots. -/
private def slotTable (k : Term s → Nat) (ts : List (Term s)) : List (Nat × Variable) :=
  ts.filterMap fun t => match t with
    | .var w => some (k (.var w), w)
    | _ => none

/-- Every solution gives a variable and its representative the same value. -/
private theorem representative_equiv (c : Problem s) (obs : List Variable) (δ : Substitution s)
    (sol : c.Solves δ) (v : Variable) (hv : c.Occurs v) :
    EquivB (δ.image v) (δ.image (representative (purify (c ++ anchors (s := s) obs)).slot
      (slotTable (purify (c ++ anchors (s := s) obs)).slot
        (inventory (c ++ anchors (s := s) obs))) v)) := by
  let a := c ++ anchors (s := s) obs
  obtain ⟨V,values⟩ := inventory_values a δ.image ((solves_anchored ..).mpr sol)
  have live : a.Occurs v := by
    obtain ⟨e,he,occ⟩ := hv
    exact ⟨e,List.mem_append_left _ he,occ⟩
  unfold representative
  dsimp only
  split
  next z found =>
    obtain ⟨t,ht,eq⟩ := List.mem_filterMap.mp (List.mem_of_find?_eq_some found)
    have hit := List.find?_some found
    cases t with
    | var w =>
      cases eq
      simp only [beq_iff_eq] at hit
      have left := values _ (var_in_inventory live)
      have right := values _ ht
      change EquivB (δ.image v) _ at left
      change EquivB (δ.image w) _ at right
      rw [hit] at right
      exact left.trans right.symm
    | _ => cases eq
  next => exact .refl _

/-- Slots that carry two products. -/
private def crowded (q : System s) : List Nat :=
  let outs := q.constraints.filterMap fun c => match c with | .ac n .. => some n | _ => none
  outs.filter fun n => (outs.filter (· == n)).length ≥ 2

/-- The slot of each product equated with a variable, with the slots of its variables. -/
private def products (k : Term s → Nat) (p : Problem s) : List (Nat × List Nat) :=
  p.filterMap fun e => match e with
    | ⟨t@(.ac _ _ _), .var x⟩ => some (k (.var x), t.variables.map fun v => k (.var v))
    | _ => none

/-- The slots that the products of the given slots mention, transitively. -/
private def reach (table : List (Nat × List Nat)) : Nat → List Nat → List Nat
  | 0, seen => seen
  | n+1, seen =>
    let next := table.foldl (fun acc pr =>
      if seen.contains pr.1 then pr.2.foldl (fun a i => if a.contains i then a else i :: a) acc
      else acc) seen
    if next.length == seen.length then seen else reach table n next

/-- The slots of the products that the aliases of a blocked leaf have brought
together, with the slots of the products that define their operands. A second
homogeneous split of exactly these products decides whether they agree: a
product left outside is only an operand of the split, and one left out of its
own definition would let a cycle through the products reappear at every round. -/
private def tangled (q : System s) (p : Problem s) : List Nat :=
  let table := products q.slot p
  reach table table.length (crowded q)

/-- Solve a leaf, or split again the products that its aliases have brought
together, or report the aliases it forces among the original slots. The
second split keeps the denotation of the leaf, so the search need not return
to the original equations. The round bound keeps the recursion structural. -/
private def settle {ι : Type} (key : ι → Variable × Variable) (cs : Thunk (List ι))
    (heads : List s.ACSym) (obs : List Variable)
    (ban : Variable → Head s → Bool) (inside : ∀ y h, ban y h = true → y ∈ obs) :
    Nat → (p : Problem s) → Guarded key cs.get ban p obs
  | 0, p => relax (finish key cs p obs)
  | n+1, p =>
    match hr : (leaf p obs).val with
    | some rows => relax (solved key cs.get p obs rows hr)
    | none =>
      let a := p ++ anchors (s := s) obs
      let q := purify a
      let bad := tangled q p
      let pick := contested (fun i => bad.contains i) q.slot
      if p.any pick then
        let r := representative q.slot (slotTable q.slot (inventory a))
        transport (Residual.equivalent (· ∈ obs) (fun δ => realign_solves pick r p δ
            (fun sol v hv => representative_equiv p obs δ sol v hv)) .identity)
          (analyzeWith key cs.get heads obs ban inside (settle key cs heads obs ban inside n)
            (realign pick r p))
      else relax (request key cs p obs)

private theorem settle_solved {ι : Type} (key : ι → Variable × Variable) (cs : Thunk (List ι))
    (heads : List s.ACSym) (obs : List Variable)
    (ban : Variable → Head s → Bool) (inside : ∀ y h, ban y h = true → y ∈ obs)
    (n : Nat) (p : Problem s) (rows : List (Substitution s)) (hr : (leaf p obs).val = some rows) :
    (settle key cs heads obs ban inside n p).val = some (rows.map Sum.inl) := by
  cases n with
  | zero =>
    unfold settle finish
    split
    next found eq => rw [hr] at eq; cases eq; rfl
    next eq => rw [hr] at eq; cases eq
  | succ n =>
    unfold settle
    split
    next found eq => rw [hr] at eq; cases eq; rfl
    next eq => rw [hr] at eq; cases eq

/-- The number of further homogeneous splits of one residual branch. -/
def rounds : Nat := 8

/-- The combined search returns solved leaves and the original slot equalities
needed to reopen blocked ones. Every reported equality belongs to the supplied
finite list and is forced on the branch it replaces. Branches that equate a
slot with a banned head, or one variable with two different rigid heads, are
never produced by a homogeneous split. -/
def analyze {ι : Type} (key : ι → Variable × Variable) (cs : Thunk (List ι))
    (heads : List s.ACSym) (p : Problem s) (obs : List Variable)
    (ban : Variable → Head s → Bool) (inside : ∀ y h, ban y h = true → y ∈ obs) :
    Guarded key cs.get ban p obs :=
  analyzeWith key cs.get heads obs ban inside (settle key cs heads obs ban inside rounds) p

theorem analyze_closed {ι : Type} (key : ι → Variable × Variable) (candidates : Thunk (List ι))
    (heads : List s.ACSym) (p : Problem s) (obs : List Variable)
    (ban : Variable → Head s → Bool) (inside : ∀ y h, ban y h = true → y ∈ obs)
    (closed : ∀ c ∈ (frontier heads p obs).val, ConstructorDecided c obs) :
    ∃ as, (analyze key candidates heads p obs ban inside).val = some as ∧ ∀ i, Sum.inr i ∉ as := by
  let fs := pruned ban heads p obs
  let visit := fun (c : Problem s) => (settle key candidates heads obs ban inside rounds c).val
  have yes (c) (hc : c ∈ fs) : ∃ out, visit c = some out ∧ ∀ i, Sum.inr i ∉ out := by
    obtain ⟨rows,hr⟩ := Option.isSome_iff_exists.mp
      (leaf_completes c obs (closed c (pruned_subset ban heads p obs c hc)))
    exact ⟨rows.map Sum.inl,settle_solved key candidates heads obs ban inside rounds c rows hr,by simp⟩
  have total := RigidBranches.collect_completes visit fs (fun c hc => by
    obtain ⟨_,hr,_⟩ := yes c hc; simp [hr])
  obtain ⟨all,hr⟩ := Option.isSome_iff_exists.mp total
  refine ⟨all.val,?_,?_⟩
  · unfold analyze analyzeWith
    simp only [visit,fs] at hr
    simp [hr]
  · intro i hi
    obtain ⟨c,hc,rows,eq,mem⟩ := all.property.2 _ hi
    obtain ⟨_,hr,clean⟩ := yes c hc
    rw [eq] at hr; cases hr
    exact clean _ mem

end Tamarin.MixedUnification.ComponentSearch
