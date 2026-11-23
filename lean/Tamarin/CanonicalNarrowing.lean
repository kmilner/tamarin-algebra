import Tamarin.CompleteNarrowing
import Tamarin.NeededExtensions
import Tamarin.CertifiedReductionWire

/-! Root narrowing of a term through the term with its variables numbered in
order of occurrence. The numbered term does not depend on the names of the
variables or on what surrounds the term, so the members of a family, which
share most subterms up to renaming, share its unifiers. Branches that bind a
variable of the numbered term to a reducible term are dropped at once: every
instance of such a branch is reducible on that variable as well. The kept
branches are moved to the variables of the term, with their other variables
renamed away from the anchors. -/
namespace Tamarin.VariantCertificate
open Rewriting
variable {s : Signature} {rules : List (Equation s)}
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]
variable [Interrupt]

/-- Whether no rule rewrites the term. The search stops at the first redex. -/
def quiet (rules : List (Equation s)) (t : Term s) : Bool :=
  (ReferenceReduction.follow rules 1 t).isSome

theorem quiet_eq (rules : List (Equation s)) (t : Term s) :
    quiet rules t = (ReferenceReduction.successors rules t).isEmpty := by
  unfold quiet
  rw [ReferenceReduction.follow_succ]
  cases ReferenceReduction.successors rules t <;> rfl

theorem quiet_of_normal (bound : ReferenceReduction.Bound rules) {t : Term s}
    (h : Normal (ruleRoot rules) t) : quiet rules t = true := by
  rw [quiet_eq]
  exact List.isEmpty_iff.mpr (List.eq_nil_iff_forall_not_mem.mpr fun u hu =>
    h u ((ReferenceReduction.exactSteps rules bound ..).mp ⟨u,hu,.refl _⟩))

end Tamarin.VariantCertificate

namespace Tamarin.TableNarrowing
open Rewriting RootNarrowing VariantJoin ContextualReduction ACSubproductReduction
variable {s : Signature} {rules : List (Equation s)}

/-- The place of a variable in a list, with the sort of the variable. -/
def numbered (vs : List Variable) (v : Variable) : Variable := ⟨vs.idxOf v,v.sort⟩

theorem numbered_inj {vs : List Variable} {v w : Variable} (hv : v ∈ vs)
    (h : numbered vs v = numbered vs w) : v = w := by
  have same : vs.idxOf v = vs.idxOf w := congrArg Variable.id h
  have lt_v : vs.idxOf v < vs.length := List.idxOf_lt_length_of_mem hv
  have lt_w : vs.idxOf w < vs.length := same ▸ lt_v
  have at_v : vs[vs.idxOf v] = v := List.getElem_idxOf lt_v
  have at_w : vs[vs.idxOf w] = w := List.getElem_idxOf lt_w
  rw [← at_v,← at_w]
  congr 1

/-- The term with every variable replaced by its number. -/
def number (vs : List Variable) (t : Term s) : Term s := t.subst fun v => .var (numbered vs v)

/-- A branch with its substitution tabulated on the listed variables. -/
def freeze (ws : List Variable) (b : Branch s) : Branch s :=
  ⟨Substitution.fromBindings (ws.map fun w => (w,b.subst.image w)) (by
    intro v t member
    obtain ⟨w,_,eq⟩ := List.mem_map.mp member
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    exact b.subst.sorted _),b.value⟩

theorem freeze_image {ws : List Variable} (b : Branch s) {w : Variable} (hw : w ∈ ws) :
    (freeze ws b).subst.image w = b.subst.image w := by
  change Substitution.lookupBinding _ w = _
  rw [Substitution.lookupBinding_tabulate,ite_eq_left hw]

/-- The variables in the images of the numbered variables and in the value. -/
def reach (vs : List Variable) (b : Branch s) : List Variable :=
  (vs.map fun v => b.subst.image (numbered vs v)).flatMap Term.variables ++ b.value.variables

/-- The renaming that moves the variables of a branch above the avoided ones. -/
def lifting (avoid vs : List Variable) (b : Branch s) : VariablePermutation :=
  .ofBlock (reach vs b) (VariablePermutation.freshBound (avoid ++ reach vs b))
    (fun v hv => VariablePermutation.lt_freshBound _ v (List.mem_append_right _ hv))

/-- A branch of the numbered term as a branch of the term: every variable of
the term takes the image of its number, renamed away from the avoided
variables. -/
def place (avoid vs : List Variable) (b : Branch s) : Branch s :=
  let π := (lifting avoid vs b).subst s
  ⟨Substitution.fromBindings (vs.map fun v => (v,π.apply (b.subst.image (numbered vs v)))) (by
    intro v t member
    obtain ⟨w,_,eq⟩ := List.mem_map.mp member
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    exact (b.subst.sorted (numbered vs _)).subst π.image π.sorted),π.apply b.value⟩

theorem place_image (avoid vs : List Variable) (b : Branch s) (v : Variable) :
    (place avoid vs b).subst.image v =
      if v ∈ vs then ((lifting avoid vs b).subst s).apply (b.subst.image (numbered vs v)) else .var v :=
  Substitution.lookupBinding_tabulate vs _ v

theorem place_apply (avoid vs : List Variable) (b : Branch s) (t : Term s)
    (inside : ∀ v, t.Occurs v → v ∈ vs) :
    (place avoid vs b).subst.apply t =
      ((lifting avoid vs b).subst s).apply (b.subst.apply (number vs t)) := by
  unfold Substitution.apply number
  rw [Term.subst_comp,Term.subst_comp]
  apply Term.subst_eq_of_agree
  intro v hv
  rw [place_image,ite_eq_left (inside v hv)]
  rfl

theorem number_occurs (vs : List Variable) (t : Term s) (w : Variable) :
    (number vs t).Occurs w ↔ ∃ v, t.Occurs v ∧ w = numbered vs v :=
  Term.occurs_rename t (numbered vs) w

section
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]
variable [Interrupt]

/-- The root branches of a term that stands alone: those of a subproduct for
an AC product, those of the whole term otherwise. -/
def rootsAt (bound : ReferenceReduction.Bound rules) (t : Term s) : List (Branch s) :=
  let u := MixedUnification.verified (s := s)
  match t with
  | .ac f _ _ => KindACNarrowing.rootsIn u (ACEquationExtensions.needed_bound bound) f [] t
  | t => roots u bound [] t

theorem rootsAt_genuine (bound : ReferenceReduction.Bound rules) (t : Term s) (b : Branch s)
    (hb : b ∈ rootsAt bound t) : StepModulo (ruleRoot rules) (b.subst.apply t) b.value := by
  unfold rootsAt at hb
  split at hb
  · exact KindACNarrowing.rootsIn_genuine _ (ACEquationExtensions.needed_bound bound)
      (fun _ _ => ACEquationExtensions.needed_modulo rules) _ [] _ b hb
  · exact roots_genuine _ bound [] _ b hb

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
omit [Interrupt] in
private theorem alone {t : Term s} {ρ μ : Substitution s} {u value : Term s}
    (h : FitsOn (fun w => t.Occurs w ∨ Observed ([] : List (Term s)) w) ρ u μ value) : FitsOn t.Occurs ρ u μ value := by
  obtain ⟨η,agree,out⟩ := h
  exact ⟨η,fun w hw => agree w (.inl hw),out⟩

theorem rootsAt_plain (bound : ReferenceReduction.Bound rules) (t : Term s)
    (other : ∀ f a b, t ≠ .ac f a b) (ρ : Substitution s) {v : Term s}
    (fire : AtRoot (ruleRoot rules) (ρ.apply t) v) :
    ∃ b ∈ rootsAt bound t, FitsOn t.Occurs ρ v b.subst b.value := by
  unfold rootsAt
  split
  · next f a b => exact absurd rfl (other f a b)
  · obtain ⟨b,hb,fit⟩ := roots_cover (MixedUnification.verified (s := s)) bound [] t ρ fire
    exact ⟨b,hb,alone fit⟩

theorem rootsAt_product (bound : ReferenceReduction.Bound rules)
    (vars : Normalized (ruleRoot rules) Substitution.identity) (f : s.ACSym) (a b : Term s)
    (ρ : Substitution s) {v : Term s}
    (step : Occurrence (ruleRoot rules) f (ρ.apply (.ac f a b)) v) :
    ∃ d ∈ rootsAt bound (.ac f a b), FitsOn (Term.ac f a b).Occurs ρ v d.subst d.value := by
  obtain ⟨d,hd,fit⟩ := KindACNarrowing.rootsIn_cover (MixedUnification.verified (s := s)) bound
    (ACEquationExtensions.needed_bound bound) (fun _ _ => ACEquationExtensions.atRoot_needed rules)
    vars f [] (.ac f a b) ρ step
  exact ⟨d,hd,alone fit⟩

/-- The first branch is at least as general as the second one on the listed
variables: one substitution turns its images and its value into theirs. -/
def Above (ws : List Variable) (a b : Branch s) : Prop :=
  ∃ θ : Substitution s, (∀ w ∈ ws, EquivB (b.subst.image w) (θ.apply (a.subst.image w))) ∧
    EquivB b.value (θ.apply a.value)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
omit [Interrupt] in
theorem Above.refl (ws : List Variable) (a : Branch s) : Above ws a a :=
  ⟨.identity,fun _ _ => by rw [Substitution.apply_identity]; exact .refl _,
    by rw [Substitution.apply_identity]; exact .refl _⟩

/-- The root branches of a numbered term that keep its variables normal,
tabulated on those variables. -/
def numberedRoots (rules : List (Equation s)) (bound : ReferenceReduction.Bound rules) (t : Term s)
    (ws : List Variable) : List (Branch s) :=
  ((rootsAt bound t).filter fun b => ws.all fun w => VariantCertificate.quiet rules (b.subst.image w)).map
    (freeze ws)

theorem numberedRoots_sub {bound : ReferenceReduction.Bound rules} {t : Term s} {ws : List Variable}
    {b : Branch s} (h : b ∈ numberedRoots rules bound t ws) :
    ∃ raw ∈ rootsAt bound t, b = freeze ws raw := by
  obtain ⟨raw,hr,rfl⟩ := List.mem_map.mp h
  exact ⟨raw,(List.mem_filter.mp hr).1,rfl⟩

theorem numberedRoots_above {bound : ReferenceReduction.Bound rules} {t : Term s} {ws : List Variable}
    {raw : Branch s} (h : raw ∈ rootsAt bound t)
    (kept : (ws.all fun w => VariantCertificate.quiet rules (raw.subst.image w)) = true) :
    ∃ a ∈ numberedRoots rules bound t ws, Above ws a (freeze ws raw) :=
  ⟨_,List.mem_map_of_mem (f := freeze ws) ((List.mem_filter (p := fun b =>
    ws.all fun w => VariantCertificate.quiet rules (b.subst.image w))).mpr ⟨h,kept⟩),.refl ws _⟩

/-- The root branches of a term among anchors, found on the numbered term. -/
def canonicalRoots (bound : ReferenceReduction.Bound rules) (anchors : List (Term s)) (t : Term s) :
    List (Branch s) :=
  let vs := t.variables.eraseDups
  (numberedRoots rules bound (number vs t) (vs.map (numbered vs))).map
    (place (anchors.flatMap Term.variables) vs)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
omit [Interrupt] in
private theorem listed (t : Term s) (v : Variable) : v ∈ t.variables.eraseDups ↔ t.Occurs v := by
  rw [List.mem_eraseDups,Term.mem_variables]

theorem canonicalRoots_genuine (bound : ReferenceReduction.Bound rules) (anchors : List (Term s))
    (t : Term s) (b : Branch s) (hb : b ∈ canonicalRoots bound anchors t) :
    StepModulo (ruleRoot rules) (b.subst.apply t) b.value := by
  obtain ⟨frozen,hf,rfl⟩ := List.mem_map.mp hb
  obtain ⟨raw,hr,rfl⟩ := numberedRoots_sub hf
  have step := rootsAt_genuine bound _ raw hr
  let vs := t.variables.eraseDups
  rw [place_apply _ vs _ t (fun v hv => (listed t v).mpr hv)]
  have same : (freeze (vs.map (numbered vs)) raw).subst.apply (number vs t) =
      raw.subst.apply (number vs t) := by
    apply Term.subst_eq_of_agree
    intro w hw
    obtain ⟨v,hv,rfl⟩ := (number_occurs vs t w).mp hw
    exact freeze_image raw (List.mem_map_of_mem ((listed t v).mpr hv))
  rw [same]
  exact SpecializedFresh.stepModulo_subst rules _ step

/-- A cover of the numbered term by root branches is a cover of the term by
the placed branches, for substitutions that are normal on its variables. -/
theorem canonicalRoots_cover (bound : ReferenceReduction.Bound rules) (anchors : List (Term s))
    (t : Term s) (live : ∀ w, t.Occurs w → Observed anchors w) (ρ : Substitution s)
    (norm : ∀ w, Observed anchors w → Normal (ruleRoot rules) (ρ.image w)) {v : Term s}
    (root : ∀ κ : Substitution s, κ.apply (number t.variables.eraseDups t) = ρ.apply t →
      ∃ b ∈ rootsAt bound (number t.variables.eraseDups t),
        FitsOn (number t.variables.eraseDups t).Occurs κ v b.subst b.value) :
    ∃ b ∈ canonicalRoots bound anchors t, FitsOn (Observed anchors) ρ v b.subst b.value := by
  let vs := t.variables.eraseDups
  let ws := vs.map (numbered vs)
  let avoid := anchors.flatMap Term.variables
  -- The substitution on the numbers.
  let κ : Substitution s := Substitution.fromBindings (vs.map fun x => (numbered vs x,ρ.image x)) (by
    intro x u member
    obtain ⟨y,_,eq⟩ := List.mem_map.mp member
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    exact ρ.sorted y)
  have at_number (x : Variable) (hx : x ∈ vs) : κ.image (numbered vs x) = ρ.image x := by
    apply Substitution.lookupBinding_eq_of_mem
    · intro w a c ha hc
      obtain ⟨y,hy,eq⟩ := List.mem_map.mp ha
      obtain ⟨z,_,eq'⟩ := List.mem_map.mp hc
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
      obtain ⟨same,rfl⟩ := Prod.mk.inj eq'
      rw [numbered_inj hy same.symm]
    · exact List.mem_map.mpr ⟨x,hx,rfl⟩
  have source : κ.apply (number vs t) = ρ.apply t := by
    unfold Substitution.apply number
    rw [Term.subst_comp]
    apply Term.subst_eq_of_agree
    intro x hx
    exact at_number x ((listed t x).mpr hx)
  obtain ⟨raw,hraw,δr,agree_r,out_r⟩ := root κ source
  have kept : (ws.all fun w => VariantCertificate.quiet rules (raw.subst.image w)) = true := by
    apply List.all_eq_true.mpr
    intro w hw
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hw
    apply VariantCertificate.quiet_of_normal bound
    have occurs : (number vs t).Occurs (numbered vs x) :=
      (number_occurs vs t _).mpr ⟨x,(listed t x).mp hx,rfl⟩
    have normal := norm x (live x ((listed t x).mp hx))
    rw [← at_number x hx] at normal
    exact VariantJoin.normal_of_instance ((normal_equiv _ (agree_r _ occurs)).mp normal)
  obtain ⟨frozen,hfrozen,θ,up,upValue⟩ := numberedRoots_above (ws := ws) hraw kept
  let δ0 := δr.compose θ
  have agree (x : Variable) (hx : x ∈ vs) :
      EquivB (κ.image (numbered vs x)) (δ0.apply (frozen.subst.image (numbered vs x))) := by
    have listed' : numbered vs x ∈ ws := List.mem_map_of_mem hx
    have first := agree_r _ ((number_occurs vs t _).mpr ⟨x,(listed t x).mp hx,rfl⟩)
    rw [← freeze_image raw listed'] at first
    rw [Substitution.apply_compose]
    exact first.trans ((up _ listed').subst δr.image)
  have out : EquivB v (δ0.apply frozen.value) := by
    rw [Substitution.apply_compose]
    exact out_r.trans (upValue.subst δr.image)
  let b := place avoid vs frozen
  have member : b ∈ canonicalRoots bound anchors t := List.mem_map_of_mem hfrozen
  let π := lifting avoid vs frozen
  let range := reach vs frozen
  let moved (x : Variable) : Prop := x ∈ range.map π.forward
  let δ := VariantJoin.choose moved (δ0.compose (π.inverse.subst s)) ρ
  have back (z : Variable) (hz : z ∈ range) : δ.image (π.forward z) = δ0.image z := by
    have yes : moved (π.forward z) := List.mem_map_of_mem hz
    have left := (VariantJoin.choose_apply moved (δ0.compose (π.inverse.subst s)) ρ
      (.var (π.forward z))).1 (fun x hx => by cases hx; exact yes)
    change δ.image (π.forward z) = δ0.apply (.var (π.backward (π.forward z))) at left
    rw [π.left_inverse] at left
    exact left
  have lowered (u : Term s) (inside : ∀ z, u.Occurs z → z ∈ range) :
      δ.apply ((π.subst s).apply u) = δ0.apply u := by
    unfold Substitution.apply
    rw [Term.subst_comp]
    apply Term.subst_eq_of_agree
    intro z hz
    exact back z (inside z hz)
  have stays (w : Variable) (hw : w ∈ avoid) : δ.image w = ρ.image w := by
    have no : ¬moved w := by
      intro yes
      obtain ⟨z,hz,eq⟩ := List.mem_map.mp yes
      have low := VariablePermutation.lt_freshBound (avoid ++ range) w (List.mem_append_left _ hw)
      have shifted : π.forward z = VariablePermutation.shift
          (VariablePermutation.freshBound (avoid ++ range)) z :=
        VariablePermutation.swapBlock_source _ _ z hz
      rw [← eq,shifted] at low
      simp only [VariablePermutation.shift] at low
      omega
    exact (VariantJoin.choose_apply moved (δ0.compose (π.inverse.subst s)) ρ (.var w)).2
      (fun x hx => by cases hx; exact no)
  refine ⟨b,member,δ,?_,?_⟩
  · intro w hw
    have avoided : w ∈ avoid := by
      obtain ⟨a,ha,occ⟩ := hw
      exact List.mem_flatMap.mpr ⟨a,ha,(a.mem_variables w).mpr occ⟩
    change EquivB _ (δ.apply ((place avoid vs frozen).subst.image w))
    rw [place_image]
    split
    · next hx =>
      have inside : ∀ z, (frozen.subst.image (numbered vs w)).Occurs z → z ∈ range := by
        intro z hz
        exact List.mem_append_left _ (List.mem_flatMap.mpr
          ⟨_,List.mem_map_of_mem hx,(Term.mem_variables _ z).mpr hz⟩)
      rw [lowered _ inside,← at_number w hx]
      exact agree w hx
    · change EquivB _ (δ.image w)
      rw [stays w avoided]
      exact .refl _
  · change EquivB v (δ.apply ((π.subst s).apply frozen.value))
    rw [lowered _ (fun z hz => List.mem_append_right _ ((Term.mem_variables _ z).mpr hz))]
    exact out

/-- Numbering the variables of a term does not change whether a rule rewrites
it: the term and the numbered term are instances of each other. -/
theorem quiet_number (bound : ReferenceReduction.Bound rules) (t : Term s) :
    VariantCertificate.quiet rules (number t.variables.eraseDups t) = VariantCertificate.quiet rules t := by
  let vs := t.variables.eraseDups
  have iff (u : Term s) : VariantCertificate.quiet rules u = true ↔ Normal (ruleRoot rules) u := by
    constructor
    · intro h w step
      obtain ⟨v,hv,_⟩ := (ReferenceReduction.exactSteps rules bound _ _).mpr step
      rw [VariantCertificate.quiet_eq] at h
      rw [List.isEmpty_iff.mp h] at hv
      exact List.not_mem_nil hv
    · exact VariantCertificate.quiet_of_normal bound
  let forth : Substitution s := Substitution.fromBindings (vs.map fun x => (x,.var (numbered vs x))) (by
    intro x u member
    obtain ⟨y,_,eq⟩ := List.mem_map.mp member
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    exact .var (numbered vs _))
  have there : forth.apply t = number vs t := by
    apply Term.subst_eq_of_agree
    intro x hx
    change Substitution.lookupBinding _ x = _
    rw [Substitution.lookupBinding_tabulate,ite_eq_left ((listed t x).mpr hx)]
  let back : Substitution s := Substitution.fromBindings (vs.map fun x => (numbered vs x,.var x)) (by
    intro x u member
    obtain ⟨y,_,eq⟩ := List.mem_map.mp member
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    exact .var y)
  have at_number (x : Variable) (hx : x ∈ vs) : back.image (numbered vs x) = .var x := by
    apply Substitution.lookupBinding_eq_of_mem
    · intro w a c ha hc
      obtain ⟨y,hy,eq⟩ := List.mem_map.mp ha
      obtain ⟨z,_,eq'⟩ := List.mem_map.mp hc
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
      obtain ⟨same,rfl⟩ := Prod.mk.inj eq'
      rw [numbered_inj hy same.symm]
    · exact List.mem_map.mpr ⟨x,hx,rfl⟩
  have here : back.apply (number vs t) = t := by
    unfold Substitution.apply number
    rw [Term.subst_comp]
    have same := Term.subst_eq_of_agree (fun v => (Term.var (numbered vs v)).subst back.image) Term.var t
      (fun x hx => at_number x ((listed t x).mpr hx))
    exact same.trans t.subst_id
  have both : VariantCertificate.quiet rules (number vs t) = true ↔ VariantCertificate.quiet rules t = true := by
    rw [iff,iff]
    constructor
    · intro h
      exact VariantJoin.normal_of_instance (σ := forth) (by rw [there]; exact h)
    · intro h
      exact VariantJoin.normal_of_instance (σ := back) (by rw [here]; exact h)
  cases a : VariantCertificate.quiet rules (number vs t) <;> cases b : VariantCertificate.quiet rules t <;>
    simp_all

/-- The root branches found on numbered terms. -/
def canonical (bound : ReferenceReduction.Bound rules)
    (vars : Normalized (ruleRoot rules) Substitution.identity) : RootSource rules where
  roots := canonicalRoots bound
  genuine := fun anchors t _ b hb => canonicalRoots_genuine bound anchors t b hb
  plain := by
    intro anchors t live other ρ norm v fire
    apply canonicalRoots_cover bound anchors t live ρ norm
    intro κ source
    apply rootsAt_plain bound _ _ κ (source ▸ fire)
    intro f a b eq
    cases t with
    | ac g c d => exact other g c d rfl
    | var _ => cases eq
    | atom _ => cases eq
    | free _ _ => cases eq
    | comm _ _ _ => cases eq
  product := by
    intro anchors f a b live ρ norm v step
    apply canonicalRoots_cover bound anchors (.ac f a b) live ρ norm
    intro κ source
    exact rootsAt_product bound vars f _ _ κ (source ▸ step)

/-- The narrower of the variant certificate checker. -/
def checking {n : Nat} (bound : ReferenceReduction.Bound rules)
    (vars : Normalized (ruleRoot rules) Substitution.identity) (query : Fin n → Term s) :
    FoldingNarrowing.Narrower rules query :=
  positionalWith (canonical bound vars) bound query

end
end Tamarin.TableNarrowing
