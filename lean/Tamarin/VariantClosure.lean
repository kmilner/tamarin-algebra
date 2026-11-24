import Tamarin.GeneralVariants
import Tamarin.CertifiedReductionWire
import Tamarin.GuessedMatching
import Tamarin.CanonicalNarrowing

/-! The closure test of the variant certificate checker. A member is a
substitution that is normal on the variables of the query, together with
normal forms of the instantiated query. A list of members passes when some
member subsumes the normalized query itself and every normalized one-step
narrowing successor of a member is subsumed by a member. On a canonical
presentation every normal substitution is then an instance of a member.
Nothing is searched: the cost is one narrowing layer per member. -/
namespace Tamarin.VariantCertificate
open Rewriting VariantJoin MaudeOperations ReferenceVariantFrontier TupleNarrowingFrontier
variable {s : Signature} {n : Nat} {rules : List (Equation s)} {query : Fin n → Term s}

/-- A rejection names what failed and the member it failed for. Reason 1: the
member's substitution is not normal. Reason 2: no member subsumes the
normalized query. Reason 3: a narrowing successor of the member is not
subsumed. Reason 4: the table has a variable left side or an unbound
right-side variable. -/
inductive Verdict where
  | accepted
  | rejected (reason index : Nat)
  | exhausted
  deriving DecidableEq

theorem mapM_some_mem {α β : Type} (f : α → Option β) {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : ∀ x ∈ xs, ∃ y ∈ ys, f x = some y := by
  induction xs generalizing ys with
  | nil => exact fun _ hx => nomatch hx
  | cons a as ih =>
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases tail : as.mapM f with
      | none => simp [ha,tail] at h
      | some bs =>
        simp [ha,tail] at h
        subst ys
        intro x hx
        rcases List.mem_cons.mp hx with rfl | later
        · exact ⟨b,List.mem_cons_self,ha⟩
        · obtain ⟨y,hy,e⟩ := ih tail x later
          exact ⟨y,List.mem_cons_of_mem _ hy,e⟩

theorem mapM_some_source {α β : Type} (f : α → Option β) {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : ∀ y ∈ ys, ∃ x ∈ xs, f x = some y := by
  induction xs generalizing ys with
  | nil =>
    simp at h
    subst ys
    exact fun _ hy => nomatch hy
  | cons a as ih =>
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases tail : as.mapM f with
      | none => simp [ha,tail] at h
      | some bs =>
        simp [ha,tail] at h
        subst ys
        intro y hy
        rcases List.mem_cons.mp hy with rfl | later
        · exact ⟨a,List.mem_cons_self,ha⟩
        · obtain ⟨x,hx,e⟩ := ih tail y later
          exact ⟨x,List.mem_cons_of_mem _ hx,e⟩

theorem mapM_some_zip {α β : Type} (f : α → Option β) {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) :
    ys.length = xs.length ∧ ∀ pair ∈ xs.zip ys, f pair.1 = some pair.2 := by
  induction xs generalizing ys with
  | nil =>
    simp at h
    subst ys
    exact ⟨rfl,fun _ hp => nomatch hp⟩
  | cons a as ih =>
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases tail : as.mapM f with
      | none => simp [ha,tail] at h
      | some bs =>
        simp [ha,tail] at h
        subst ys
        obtain ⟨len,each⟩ := ih tail
        refine ⟨by simp [len],fun pair hp => ?_⟩
        rcases List.mem_cons.mp hp with rfl | later
        · exact ha
        · exact each pair later

private theorem projected (p : Point s n) (query : Fin n → Term s) (i : Fin n) :
    (p.answer (keysOf query)).subst.apply (query i) = p.assignment.apply (query i) := by
  apply Term.subst_eq_of_agree
  intro v hv
  have mem := (observed query v).mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,hv⟩
  exact (p.row _).project_key (fun k => p.assignment.sorted k.val) ⟨v,mem⟩

/-- Coverage from a closed family that subsumes the seed of an expansion. The
descent is that of `VariantSaturation`; it starts at the member that subsumes
the seed, so the seed itself need not belong to the family. -/
theorem covers (g : VariantSaturation.Expansion rules query)
    (canonical : CanonicalPresentation (ruleRoot rules)) (live : Point s n → Prop)
    (valid : ∀ p, live p → VariantSaturation.Sound rules query p)
    (closed : ∀ p, live p → ∀ c ∈ g.next p,
      ∃ q, live q ∧ (q.row (keysOf query)).Subsumes (c.row (keysOf query)))
    (start : ∃ q, live q ∧ (q.row (keysOf query)).Subsumes (g.seed.row (keysOf query)))
    (ρ : Substitution s) (norm : Normalized (ruleRoot rules) ρ) (out : Fin n → Term s)
    (forms : ∀ i, NormalForm (ruleRoot rules) (ρ.apply (query i)) (out i)) :
    ∃ p, live p ∧ ∃ δ, Fits (p.row (keysOf query)) (fun i => ρ.image i.val) out δ := by
  let keys := keysOf query
  have go (k : Nat) : ∀ p, live p → ∀ δ : Substitution s,
      (∀ i : Key keys, EquivB (ρ.image i.val) (δ.apply (p.assignment.image i.val))) →
      g.measure (fun i => δ.apply (p.value i)) = k →
      ∃ q, live q ∧ ∃ η, Fits (q.row keys) (fun i => ρ.image i.val) out η := by
    induction k using Nat.strongRecOn with
    | ind k smaller =>
      intro p hp δ inputs rank
      rcases g.progress p (valid p hp) δ (fun i => (normal_equiv _ (inputs i)).mp (norm i.val)) with
        normal | ⟨c,hc,η,same,less⟩
      · exact ⟨p,hp,δ,inputs,
          VariantSaturation.endpoint canonical p (valid p hp) ρ δ out forms inputs normal⟩
      · obtain ⟨q,hq,θ,fit⟩ := closed p hp c hc
        have values (i) : EquivB (η.apply (c.value i)) ((η.compose θ).apply (q.value i)) := by
          rw [Substitution.apply_compose]
          exact (fit.values i).subst η.image
        have eq := g.invariant _ _ values
        apply smaller _ (eq ▸ rank ▸ less) q hq (η.compose θ) _ rfl
        intro i
        rw [Substitution.apply_compose]
        exact (inputs i).trans ((same i).trans ((fit.inputs i).subst η.image))
  obtain ⟨first,hfirst,θ,fit⟩ := start
  apply go _ first hfirst (ρ.compose θ) _ rfl
  intro i
  have image : EquivB (.var i.val) (θ.apply (first.assignment.image i.val)) := by
    have at_seed := fit.inputs i
    change EquivB (g.seed.assignment.image i.val) _ at at_seed
    rwa [g.identity _ i.property] at at_seed
  rw [Substitution.apply_compose]
  exact image.subst ρ.image

theorem mapM_ofFn {α β : Type} (f : α → Option β) {n : Nat} {g : Fin n → α} {ys : List β}
    (h : (List.ofFn g).mapM f = some ys) :
    ∃ k : Fin n → β, ys = List.ofFn k ∧ ∀ i, f (g i) = some (k i) := by
  induction n generalizing ys with
  | zero =>
    simp at h
    subst ys
    exact ⟨Fin.elim0,rfl,fun i => i.elim0⟩
  | succ n ih =>
    rw [List.ofFn_succ] at h
    cases ha : f (g 0) with
    | none => simp [ha] at h
    | some b =>
      cases tail : (List.ofFn fun i : Fin n => g i.succ).mapM f with
      | none => simp [ha,tail] at h
      | some bs =>
        simp [ha,tail] at h
        subst ys
        obtain ⟨k,rfl,each⟩ := ih tail
        refine ⟨Fin.cases b k,by simp [List.ofFn_succ],Fin.cases ha each⟩

/-- `some true` when the test succeeds on every entry. The first entry on
which it does not ends the scan with its result. -/
def every {α : Type} (f : α → Option Bool) : List α → Option Bool
  | [] => some true
  | x :: xs =>
    match f x with
    | some true => every f xs
    | other => other

theorem every_true {α : Type} {f : α → Option Bool} {xs : List α} (h : every f xs = some true) :
    ∀ x ∈ xs, f x = some true := by
  induction xs with
  | nil => exact fun _ hx => nomatch hx
  | cons a as ih =>
    unfold every at h
    intro x hx
    split at h
    · next ok =>
      rcases List.mem_cons.mp hx with rfl | later
      · exact ok
      · exact ih h x later
    · next other =>
      rcases List.mem_cons.mp hx with rfl | later
      · exact h
      · exact absurd h (other · )

theorem zipWith_ofFn {α β γ : Type} (f : α → β → γ) {n : Nat} (a : Fin n → α) (b : Fin n → β) :
    List.zipWith f (List.ofFn a) (List.ofFn b) = List.ofFn (fun i => f (a i) (b i)) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.ofFn_succ,ih]

/-- A point whose values are read from a table. -/
def frozen (σ : Substitution s) (query : Fin n → Term s) (values : List (Term s)) : Point s n :=
  let table := values.toArray
  ⟨σ,fun i => (table[i.val]?).getD (query i)⟩

theorem frozen_ofFn (σ : Substitution s) (query k : Fin n → Term s) :
    frozen σ query (List.ofFn k) = ⟨σ,k⟩ := by
  simp [frozen]

/-- The terms a point is compared on: the images of the keys, then the values. -/
def terms (keys : List Variable) (p : Point s n) : List (Term s) :=
  keys.map p.assignment.image ++ List.ofFn p.value

/-- What the closure test assumes of a member: its substitution is normal on
the keys and its values are normal forms of the instantiated query. -/
def Formed (rules : List (Equation s)) (query : Fin n → Term s) (p : Point s n) : Prop :=
  (∀ i : Key (keysOf query), Normal (ruleRoot rules) (p.assignment.image i.val)) ∧
    ∀ i, NormalForm (ruleRoot rules) (p.assignment.apply (query i)) (p.value i)

section
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]
variable [Interrupt]

/-- The normal forms of a tuple, each computed once along its first rewrite
path. That path is the one the reference reducer takes, so the result does
not depend on the depth once the depth suffices. -/
def settle (rules : List (Equation s)) (fuel : Nat) (raw : Fin n → Term s) : Option (List (Term s)) :=
  (List.ofFn raw).mapM (ReferenceReduction.follow rules fuel)

theorem follow_reduce (bound : ReferenceReduction.Bound rules)
    (canonical : CanonicalPresentation (ruleRoot rules)) {fuel : Nat} {t u : Term s}
    (h : ReferenceReduction.follow rules fuel t = some u) :
    u = (ReferenceReduction.reducer rules bound canonical).reduce t := by
  rw [CertifiedReductionWire.follow_eq] at h
  exact CertifiedReductionWire.choose_exact bound canonical fuel t u h

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] [Interrupt] in
/-- The terms of two points side by side: the images of each key, then the
values of each slot. -/
theorem zip_terms (keys : List Variable) (g t : Point s n) : (terms keys g).zip (terms keys t) =
    keys.map (fun v => (g.assignment.image v,t.assignment.image v)) ++
      List.ofFn (fun i => (g.value i,t.value i)) := by
  simp [terms,List.zip_eq_zipWith,List.zipWith_append,List.zipWith_map,List.zipWith_self,zipWith_ofFn]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] [Interrupt] in
/-- A substitution that turns the terms of one point into those of another
makes the first row subsume the second. -/
theorem rows_subsume {keys : List Variable} {g t : Point s n} {θ : Substitution s}
    (h : ∀ e ∈ (terms keys g).zip (terms keys t), EquivB (θ.apply e.1) e.2) :
    (g.row keys).Subsumes (t.row keys) := by
  rw [zip_terms] at h
  refine ⟨θ,fun i => ?_,fun a => ?_⟩
  · exact (h _ (List.mem_append_left _ (List.mem_map_of_mem (f := fun v =>
      (g.assignment.image v,t.assignment.image v)) i.property))).symm
  · exact (h _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨a,rfl⟩))).symm

/-- Whether one substitution turns every entry of the first list into the
entry of the second list at the same place. Only the first answer of the
matcher is looked for. -/
def instanceOf (general specific : List (Term s)) : Bool :=
  let p : Problem s := (general.zip specific).map fun e => ⟨e.1,e.2⟩
  (ReferenceMatching.first p (patternVariables p)).isSome

theorem instanceOf_sound {keys : List Variable} {g t : Point s n}
    (h : instanceOf (terms keys g) (terms keys t) = true) : (g.row keys).Subsumes (t.row keys) := by
  unfold instanceOf at h
  dsimp only at h
  obtain ⟨σ,found⟩ := Option.isSome_iff_exists.mp h
  rw [ReferenceMatching.first_eq] at found
  have ok := (((ReferenceMatching.matcher s).correct _ trivial _).sound σ (List.mem_of_mem_head? found)).1
  exact rows_subsume fun e member => ok _ (List.mem_map_of_mem (f := fun e : Term s × Term s =>
    (⟨e.1,e.2⟩ : Equation s)) member)

/-- The same question answered by a guessed substitution that passes the
test. `false` does not mean that there is no such substitution. -/
def guessedInstance (general specific : List (Term s)) : Bool :=
  (GuessedMatching.find (general.zip specific)).isSome

omit [Interrupt] in
theorem guessedInstance_sound {keys : List Variable} {g t : Point s n}
    (h : guessedInstance (terms keys g) (terms keys t) = true) : (g.row keys).Subsumes (t.row keys) := by
  obtain ⟨θ,found⟩ := Option.isSome_iff_exists.mp h
  exact rows_subsume (GuessedMatching.find_sound found)

/-- Whether an instance of the first term can have the root of the second. -/
def sameRoot : Term s → Term s → Bool
  | .var _, _ => true
  | .atom a, .atom b => a == b
  | .free f _, .free g _ => f == g
  | .comm f _ _, .comm g _ _ => f == g
  | .ac f _ _, .ac g _ _ => f == g
  | _, _ => false

def bare : Term s → Bool
  | .var _ => true
  | _ => false

/-- A cheap necessary condition for an instance of the first term to equal
the second one. An instance of a product has at least as many operands as the
product, exactly as many when no operand is a variable, and every operand
that is not a variable keeps its root. No proof uses the condition: a wrong
answer can only send the caller to the complete matcher. -/
def plausible : Term s → Term s → Bool
  | .var _, _ => true
  | .atom a, .atom b => a == b
  | .free f xs, .free g ys =>
    if h : f = g then (List.finRange (s.arity f)).all fun i => plausible (xs i) (ys (h ▸ i)) else false
  | .comm f a b, .comm g c d =>
    f == g && ((plausible a c && plausible b d) || (plausible a d && plausible b c))
  | .ac f a b, .ac g c d =>
    f == g &&
      (let pattern := ACRepresentation.flatten f (.ac f a b)
       let subject := ACRepresentation.flatten f (.ac g c d)
       let solid := pattern.filter fun x => !bare x
       (if solid.length == pattern.length then pattern.length == subject.length
        else pattern.length ≤ subject.length) &&
         solid.all fun x => subject.any (sameRoot x))
  | _, _ => false

def plausibleAll : List (Term s) → List (Term s) → Bool
  | a :: as, b :: bs => plausibleAll as bs && plausible a b
  | _, _ => true

/-- Whether the list of terms is an instance of one of the rows. The guessed
substitutions are tried first, on the rows that pass the cheap test. When
none of them succeeds the complete matcher decides. -/
def covered (rows : List (List (Term s))) (child : List (Term s)) : Bool :=
  (rows.any fun g => plausibleAll g child && guessedInstance g child) ||
    rows.any fun g => instanceOf g child

theorem covered_sound {keys : List Variable} {members : List (Point s n)} {c : Point s n}
    (h : covered (members.map (terms keys)) (terms keys c) = true) :
    ∃ m, m ∈ members ∧ (m.row keys).Subsumes (c.row keys) := by
  rcases Bool.or_eq_true_iff.mp h with quick | slow
  · obtain ⟨_,hg,ok⟩ := List.any_eq_true.mp quick
    obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hg
    exact ⟨m,hm,guessedInstance_sound (Bool.and_eq_true_iff.mp ok).2⟩
  · obtain ⟨_,hg,ok⟩ := List.any_eq_true.mp slow
    obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hg
    exact ⟨m,hm,instanceOf_sound ok⟩

omit [Interrupt] in
theorem admissible_iff (bound : ReferenceReduction.Bound rules) (p : Point s n) :
    FoldingNarrowing.admissible rules query p = true ↔
      ∀ i : Key (keysOf query), Normal (ruleRoot rules) (p.assignment.image i.val) := by
  constructor
  · intro h i u step
    obtain ⟨v,hv,_⟩ := (ReferenceReduction.exactSteps rules bound _ _).mpr step
    rw [List.isEmpty_iff.mp (List.all_eq_true.mp h i.val i.property)] at hv
    exact List.not_mem_nil hv
  · intro h
    apply List.all_eq_true.mpr
    intro v hv
    exact List.isEmpty_iff.mpr (List.eq_nil_iff_forall_not_mem.mpr (fun u hu =>
      h ⟨v,hv⟩ u ((ReferenceReduction.exactSteps rules bound ..).mp ⟨u,hu,.refl _⟩)))

/-- Whether the substitution of the point is normal on the keys. -/
def normalOn (rules : List (Equation s)) (keys : List Variable) (σ : Substitution s) : Bool :=
  keys.all fun v => quiet rules (σ.image v)

theorem normalOn_eq (p : Point s n) :
    normalOn rules (keysOf query) p.assignment = FoldingNarrowing.admissible rules query p := by
  simp [normalOn,FoldingNarrowing.admissible,quiet_eq]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] [Interrupt] in
/-- A substitution with normal images on the keys, together with normal
forms of the instantiated query, is a sound variant. -/
theorem sound_member (vars : Normalized (ruleRoot rules) Substitution.identity) (p : Point s n)
    (formed : Formed rules query p) : VariantSaturation.Sound rules query p := by
  refine ⟨(p.row _).project_normal (fun k => p.assignment.sorted k.val) vars
    ⟨formed.1,fun i => (formed.2 i).2.1⟩,alignedFn query p.value (fun i => ?_)⟩
  rw [projected p query i]
  exact formed.2 i

/-- The proposed substitution with the normal forms of the instantiated query. -/
def member (rules : List (Equation s)) (query : Fin n → Term s) (fuel : Nat) (σ : Substitution s) :
    Option (Point s n) :=
  (settle rules fuel fun i => σ.apply (query i)).map (frozen σ query)

theorem member_form {fuel : Nat} {σ : Substitution s} {p : Point s n}
    (h : member rules query fuel σ = some p) :
    p.assignment = σ ∧ ∀ i, ReferenceReduction.follow rules fuel (σ.apply (query i)) = some (p.value i) := by
  obtain ⟨values,made,rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨k,rfl,each⟩ := mapM_ofFn _ made
  rw [frozen_ofFn]
  exact ⟨rfl,each⟩

/-- A slot whose query term is a variable holds the image of that variable.
A narrowing step there makes that image reducible, so the slot has no
admissible successor. -/
def idle : Term s → Bool
  | .var _ => true
  | _ => false

/-- One narrowing successor of a member. When its substitution is normal on
the keys, its normalized values must make it an instance of a row. -/
def childOk (rules : List (Equation s)) (keys : List Variable) (fuel : Nat)
    (rows : List (List (Term s))) (p : Point s n) (j : Fin n) (b : RootNarrowing.Branch s) :
    Option Bool :=
  let images := keys.map (b.subst.compose p.assignment).image
  if images.all (quiet rules) then
    (settle rules fuel (replace (fun i => b.subst.apply (p.value i)) j b.value)).map fun values =>
      covered rows (images ++ values)
  else some true

/-- One member's narrowing layer, read in order: every admissible successor,
normalized, must be an instance of a row. The first successor that is not, or
whose normal form the depth does not reach, ends the scan. -/
def strictAt (rules : List (Equation s)) (query : Fin n → Term s) (keys : List Variable)
    (branches : Point s n → Fin n → List (RootNarrowing.Branch s)) (fuel : Nat)
    (rows : List (List (Term s))) (p : Point s n) : Option Bool :=
  every (fun j => if idle (query j) then some true
    else every (childOk rules keys fuel rows p j) (branches p j)) (List.finRange n)

/-- The successor of a member along one branch, before normalization. -/
abbrev successor (p : Point s n) (j : Fin n) (b : RootNarrowing.Branch s) : Point s n :=
  ⟨b.subst.compose p.assignment,replace (fun i => b.subst.apply (p.value i)) j b.value⟩

/-- The branches of the slots that are narrowed. -/
def layer (query : Fin n → Term s) (branches : Point s n → Fin n → List (RootNarrowing.Branch s))
    (p : Point s n) : List (Fin n × RootNarrowing.Branch s) :=
  (List.finRange n).flatMap fun j => if idle (query j) then [] else (branches p j).map fun b => (j,b)

/-- The whole layer of a member whose scan the depth ended. A successor that
is not an instance of a row still rejects. A successor whose normal form the
depth does not reach is passed over when it is an instance of another
successor of the member that was normalized and found to be an instance of a
row: it is then no most general successor, and the descent that proves
coverage goes through the more general one. -/
def rescue (rules : List (Equation s)) (query : Fin n → Term s) (keys : List Variable)
    (branches : Point s n → Fin n → List (RootNarrowing.Branch s)) (fuel : Nat)
    (rows : List (List (Term s))) (p : Point s n) : Option Bool :=
  let outcomes := (layer query branches p).map fun e => (e,childOk rules keys fuel rows p e.1 e.2)
  if outcomes.any (fun e => e.2 == some false) then some false
  else
    let good := (outcomes.filter fun e => e.2 == some true &&
      (keys.map (e.1.2.subst.compose p.assignment).image).all (quiet rules)).map fun e =>
        terms keys (successor p e.1.1 e.1.2)
    if (outcomes.filter fun e => e.2 == none).all fun e =>
        good.any fun g => instanceOf g (terms keys (successor p e.1.1 e.1.2)) then some true
    else none

/-- One member's narrowing layer: every admissible successor, normalized, must
be an instance of a row, unless it is an instance of another successor for
which this was established. -/
def closedAt (rules : List (Equation s)) (query : Fin n → Term s) (keys : List Variable)
    (branches : Point s n → Fin n → List (RootNarrowing.Branch s)) (fuel : Nat)
    (rows : List (List (Term s))) (p : Point s n) : Option Bool :=
  match strictAt rules query keys branches fuel rows p with
  | none => rescue rules query keys branches fuel rows p
  | other => other

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] [Interrupt] in
theorem mem_layer {branches : Point s n → Fin n → List (RootNarrowing.Branch s)} {p : Point s n}
    {j : Fin n} {b : RootNarrowing.Branch s} :
    (j,b) ∈ layer query branches p ↔ idle (query j) = false ∧ b ∈ branches p j := by
  unfold layer
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨i,_,inside⟩
    split at inside
    · exact nomatch inside
    · next live =>
      obtain ⟨c,hc,eq⟩ := List.mem_map.mp inside
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
      exact ⟨by simpa using live,hc⟩
  · rintro ⟨live,hb⟩
    exact ⟨j,List.mem_finRange j,by simp [live,hb]⟩

/-- What a layer that passes has established for each of its successors:
it was normalized and found to be an instance of a row, or it is an instance
of another successor of the layer for which that holds and whose images on
the keys are normal. -/
theorem closedAt_true {keys : List Variable}
    {branches : Point s n → Fin n → List (RootNarrowing.Branch s)} {fuel : Nat}
    {rows : List (List (Term s))} {p : Point s n}
    (h : closedAt rules query keys branches fuel rows p = some true) (j : Fin n)
    (live : idle (query j) = false) (b : RootNarrowing.Branch s) (hb : b ∈ branches p j) :
    childOk rules keys fuel rows p j b = some true ∨
      ∃ j0 b0, idle (query j0) = false ∧ b0 ∈ branches p j0 ∧
        childOk rules keys fuel rows p j0 b0 = some true ∧
        (keys.map (b0.subst.compose p.assignment).image).all (quiet rules) = true ∧
        instanceOf (terms keys (successor p j0 b0)) (terms keys (successor p j b)) = true := by
  unfold closedAt at h
  split at h
  · unfold rescue at h
    dsimp only at h
    split at h
    · cases h
    · next clean =>
      split at h
      · next all =>
        cases outcome : childOk rules keys fuel rows p j b with
        | none =>
          have inside : ((j,b),(none : Option Bool)) ∈ ((layer query branches p).map fun e =>
              (e,childOk rules keys fuel rows p e.1 e.2)).filter fun e => e.2 == none :=
            List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(j,b),mem_layer.mpr ⟨live,hb⟩,by rw [outcome]⟩,rfl⟩
          obtain ⟨g,hg,sub⟩ := List.any_eq_true.mp (List.all_eq_true.mp all _ inside)
          obtain ⟨e,he,rfl⟩ := List.mem_map.mp hg
          obtain ⟨made,ok⟩ := List.mem_filter.mp he
          obtain ⟨⟨j0,b0⟩,hl,rfl⟩ := List.mem_map.mp made
          obtain ⟨live0,hb0⟩ := mem_layer.mp hl
          simp only [Bool.and_eq_true,beq_iff_eq] at ok
          exact .inr ⟨j0,b0,live0,hb0,ok.1,ok.2,sub⟩
        | some value =>
          cases value with
          | true => exact .inl rfl
          | false =>
            exfalso
            apply clean
            exact List.any_eq_true.mpr ⟨((j,b),some false),
              List.mem_map.mpr ⟨(j,b),mem_layer.mpr ⟨live,hb⟩,by rw [outcome]⟩,rfl⟩
      · cases h
  · unfold strictAt at h
    have slot := every_true h j (List.mem_finRange j)
    rw [live] at slot
    exact .inl (every_true slot b hb)

/-- A number that terms of the same form share. Symbols and names do not
enter it, so different terms may share it too. -/
def code : Term s → UInt64
  | .var v => mixHash 1 (hash v.id)
  | .atom _ => 2
  | .free f xs => (List.finRange (s.arity f)).foldl (fun h i => mixHash h (code (xs i)))
      (mixHash 3 (hash (s.arity f)))
  | .comm _ a b => mixHash 4 (mixHash (code a) (code b))
  | .ac _ a b => mixHash 5 (mixHash (code a) (code b))

/-- Normality tests that have been made, each with its term, in rows by the
number of the term. The terms have their variables numbered in order of
occurrence, so a term is found under any names of its variables. Every entry
carries the proof of its own answer, so no property of the table is needed to
trust what is read from it. -/
abbrev Quiets (rules : List (Equation s)) :=
  Array (List {e : Term s × Bool // e.2 = quiet rules e.1})

/-- The term with its variables numbered in order of occurrence. -/
def numberedTerm (t : Term s) : Term s := TableNarrowing.number t.variables.eraseDups t

/-- The normality test, looked up among the tests made so far or made now. -/
def quietS (rules : List (Equation s)) (made : Quiets rules) (t : Term s) : Quiets rules × Bool :=
  let key := numberedTerm t
  let row := (code key).toNat % made.size
  match (made.getD row []).find? fun e => decide (e.val.1 = key) with
  | some e => (made,e.val.2)
  | none =>
    let b := quiet rules key
    (made.modify row (⟨(key,b),rfl⟩ :: ·),b)

theorem quietS_eq (bound : ReferenceReduction.Bound rules) (made : Quiets rules) (t : Term s) :
    (quietS rules made t).2 = quiet rules t := by
  unfold quietS
  dsimp only
  split
  · next e found =>
    have hit := List.find?_some found
    simp only [decide_eq_true_eq] at hit
    rw [e.property,hit]
    exact TableNarrowing.quiet_number bound t
  · exact TableNarrowing.quiet_number bound t

/-- Whether all the terms are normal, with the tests looked up. The scan
stops at the first term that is not, as `List.all` does. -/
def allQuietS (rules : List (Equation s)) : Quiets rules → List (Term s) → Quiets rules × Bool
  | made, [] => (made,true)
  | made, t :: ts =>
    match quietS rules made t with
    | (more,true) => allQuietS rules more ts
    | (more,false) => (more,false)

theorem allQuietS_eq (bound : ReferenceReduction.Bound rules) (made : Quiets rules)
    (ts : List (Term s)) : (allQuietS rules made ts).2 = ts.all (quiet rules) := by
  induction ts generalizing made with
  | nil => rfl
  | cons t ts ih =>
    rw [List.all_cons]
    unfold allQuietS
    have head := quietS_eq bound made t
    split
    · next more ok =>
      rw [ok] at head
      rw [ih more,← head,Bool.true_and]
    · next more ok =>
      rw [ok] at head
      rw [← head,Bool.false_and]

/-- The branches that keep the listed variables normal, in their order. The
images of different branches are often the same term up to the names of its
variables, and such a term is tested once. -/
def keptS (rules : List (Equation s)) (ws : List Variable) :
    Quiets rules → List (RootNarrowing.Branch s) → Array (RootNarrowing.Branch s) →
      List (RootNarrowing.Branch s)
  | _, [], acc => acc.toList
  | made, b :: bs, acc =>
    match allQuietS rules made (ws.map b.subst.image) with
    | (more,true) => keptS rules ws more bs (acc.push b)
    | (more,false) => keptS rules ws more bs acc

theorem keptS_eq (bound : ReferenceReduction.Bound rules) (ws : List Variable)
    (made : Quiets rules) (bs : List (RootNarrowing.Branch s))
    (acc : Array (RootNarrowing.Branch s)) :
    keptS rules ws made bs acc =
      acc.toList ++ bs.filter fun b => ws.all fun w => quiet rules (b.subst.image w) := by
  induction bs generalizing made acc with
  | nil => simp [keptS]
  | cons b bs ih =>
    unfold keptS
    have head := allQuietS_eq bound made (ws.map b.subst.image)
    rw [List.all_map] at head
    split
    · next more ok =>
      rw [ok] at head
      have yes : (ws.all fun w => quiet rules (b.subst.image w)) = true := head.symm
      rw [ih]
      simp [yes]
    · next more ok =>
      rw [ok] at head
      have no : ¬ (ws.all fun w => quiet rules (b.subst.image w)) = true := by
        rw [← show false = (ws.all fun w => quiet rules (b.subst.image w)) from head]
        simp
      rw [ih]
      simp [no]

/-- `numberedRoots` with the normality tests of the images looked up among
those made for the earlier branches of the same term. -/
def numberedRootsMemo (rules : List (Equation s)) (bound : ReferenceReduction.Bound rules)
    (t : Term s) (ws : List Variable) : List (RootNarrowing.Branch s) :=
  (keptS rules ws (Array.replicate 4096 []) (TableNarrowing.rootsAt bound t) #[]).map
    (TableNarrowing.freeze ws)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
omit [Interrupt] in
@[csimp] theorem numberedRoots_eq_memo :
    @TableNarrowing.numberedRoots = @numberedRootsMemo := by
  funext s _ _ _ _ _ rules bound t ws
  unfold TableNarrowing.numberedRoots numberedRootsMemo
  rw [keptS_eq bound]
  simp

/-- `every` with a state handed from one entry to the next. -/
def everyS {α σ : Type} (f : σ → α → σ × Option Bool) : σ → List α → σ × Option Bool
  | state, [] => (state,some true)
  | state, x :: xs =>
    match f state x with
    | (next,some true) => everyS f next xs
    | other => other

omit [Interrupt] in
theorem everyS_eq {α σ : Type} {f : σ → α → σ × Option Bool} {g : α → Option Bool}
    (h : ∀ state x, (f state x).2 = g x) (state : σ) (xs : List α) :
    (everyS f state xs).2 = every g xs := by
  induction xs generalizing state with
  | nil => rfl
  | cons x xs ih =>
    unfold everyS every
    have head := h state x
    split
    · next next ok =>
      rw [ok] at head
      rw [← head]
      exact ih next
    · next other differs =>
      rw [← head]
      generalize f state x = result at differs ⊢
      obtain ⟨next,value⟩ := result
      match value with
      | some true => exact absurd rfl (differs next)
      | some false => rfl
      | none => rfl

/-- `flatMap` with a state handed from one entry to the next. -/
def flatMapS {α β σ : Type} (f : σ → α → σ × List β) : σ → List α → σ × List β
  | state, [] => (state,[])
  | state, x :: xs =>
    let head := f state x
    let tail := flatMapS f head.1 xs
    (tail.1,head.2 ++ tail.2)

omit [Interrupt] in
theorem flatMapS_eq {α β σ : Type} {f : σ → α → σ × List β} {g : α → List β}
    (h : ∀ state x, (f state x).2 = g x) (state : σ) (xs : List α) :
    (flatMapS f state xs).2 = xs.flatMap g := by
  induction xs generalizing state with
  | nil => rfl
  | cons x xs ih =>
    unfold flatMapS
    simp only [List.flatMap_cons,h,ih]

open TableNarrowing in
/-- `positions` with a state handed from one root to the next. -/
def positionsS {σ : Type} (roots : σ → Term s → σ × List (RootNarrowing.Branch s)) :
    σ → Term s → σ × List (RootNarrowing.Branch s)
  | state, .var _ => (state,[])
  | state, .atom a => roots state (.atom a)
  | state, .free f xs =>
    let top := roots state (.free f xs)
    let rest := flatMapS (fun st i =>
      let found := positionsS roots st (xs i)
      (found.1,found.2.map (below (.free f xs i)))) top.1 (List.finRange (s.arity f))
    (rest.1,top.2 ++ rest.2)
  | state, .comm f a b =>
    let top := roots state (.comm f a b)
    let left := positionsS roots top.1 a
    let right := positionsS roots left.1 b
    (right.1,top.2 ++ (left.2.map (below (.comm f b)) ++ right.2.map (below (.comm f a))))
  | state, .ac f a b =>
    let top := roots state (.ac f a b)
    let left := positionsS roots top.1 a
    let right := positionsS roots left.1 b
    (right.1,top.2 ++ (left.2.map (below (.ac f (some b))) ++ right.2.map (below (.ac f (some a)))))

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] [Interrupt] in
theorem positionsS_eq {σ : Type} {roots : σ → Term s → σ × List (RootNarrowing.Branch s)}
    {plain : Term s → List (RootNarrowing.Branch s)} (h : ∀ state t, (roots state t).2 = plain t)
    (state : σ) (t : Term s) : (positionsS roots state t).2 = TableNarrowing.positions plain t := by
  induction t generalizing state with
  | var _ => rfl
  | atom a =>
    rw [positionsS,TableNarrowing.positions]
    exact h state _
  | free f xs ih =>
    rw [positionsS,TableNarrowing.positions]
    dsimp only
    rw [h,flatMapS_eq (g := fun i => (TableNarrowing.positions plain (xs i)).map
      (TableNarrowing.below (.free f xs i)))]
    intro st i
    dsimp only
    rw [ih i]
  | comm f a b iha ihb =>
    rw [positionsS,TableNarrowing.positions]
    dsimp only
    rw [h,iha,ihb]
  | ac f a b iha ihb =>
    rw [positionsS,TableNarrowing.positions]
    dsimp only
    rw [h,iha,ihb]

/-- Root branches of numbered terms that have been computed, each with its
term, in rows by the number of the term. Every entry carries the proof of its
own answer. -/
abbrev Roots (rules : List (Equation s)) (bound : ReferenceReduction.Bound rules) :=
  Array (List {e : (Term s × List Variable) × List (RootNarrowing.Branch s) //
    e.2 = TableNarrowing.numberedRoots rules bound e.1.1 e.1.2})

/-- The root branches of a numbered term, looked up among those computed so
far or computed now. -/
def numberedS (bound : ReferenceReduction.Bound rules) (made : Roots rules bound) (t : Term s)
    (ws : List Variable) : Roots rules bound × List (RootNarrowing.Branch s) :=
  let row := (code t).toNat % made.size
  match (made.getD row []).find? fun e => decide (e.val.1 = (t,ws)) with
  | some e => (made,e.val.2)
  | none =>
    let found := TableNarrowing.numberedRoots rules bound t ws
    (made.modify row (⟨((t,ws),found),rfl⟩ :: ·),found)

theorem numberedS_eq (bound : ReferenceReduction.Bound rules) (made : Roots rules bound) (t : Term s)
    (ws : List Variable) :
    (numberedS bound made t ws).2 = TableNarrowing.numberedRoots rules bound t ws := by
  unfold numberedS
  dsimp only
  split
  · next e found =>
    have hit := List.find?_some found
    simp only [decide_eq_true_eq] at hit
    have answer := e.property
    rw [hit] at answer
    exact answer
  · rfl

/-- `canonicalRoots` with the root branches of the numbered term looked up. -/
def rootsS (bound : ReferenceReduction.Bound rules) (avoid : List Variable) (made : Roots rules bound)
    (t : Term s) : Roots rules bound × List (RootNarrowing.Branch s) :=
  let vs := t.variables.eraseDups
  let found := numberedS bound made (TableNarrowing.number vs t) (vs.map (TableNarrowing.numbered vs))
  (found.1,found.2.map (TableNarrowing.place avoid vs))

theorem rootsS_eq (bound : ReferenceReduction.Bound rules) (anchors : List (Term s))
    (made : Roots rules bound) (t : Term s) :
    (rootsS bound (anchors.flatMap Term.variables) made t).2 =
      TableNarrowing.canonicalRoots bound anchors t := by
  unfold rootsS TableNarrowing.canonicalRoots
  dsimp only
  rw [numberedS_eq]

/-- Whether a substitution with this support keeps a term with these variables. -/
def untouched (support vars : List Variable) : Bool := vars.all fun v => decide (v ∉ support)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] [Interrupt] in
theorem apply_untouched (μ : Substitution s) (t : Term s)
    (h : untouched μ.support t.variables = true) : μ.apply t = t := by
  have same := Term.subst_eq_of_agree μ.image Term.var t fun v hv =>
    μ.outside v (by simpa using List.all_eq_true.mp h v ((t.mem_variables v).mpr hv))
  exact same.trans t.subst_id

/-- A term with its variables and the result of its normality test. -/
def keyCell (rules : List (Equation s)) (t : Term s) : Term s × List Variable × Bool :=
  (t,t.variables,quiet rules t)

/-- Whether the instances of the terms are normal. A term that the
substitution keeps has its stored answer; the others are looked up. -/
def quietCells (rules : List (Equation s)) (μ : Substitution s) :
    Quiets rules → List (Term s × List Variable × Bool) → Quiets rules × Bool
  | made, [] => (made,true)
  | made, c :: cs =>
    if untouched μ.support c.2.1 then
      if c.2.2 then quietCells rules μ made cs else (made,false)
    else
      match quietS rules made (μ.apply c.1) with
      | (more,true) => quietCells rules μ more cs
      | (more,false) => (more,false)

theorem quietCells_eq (bound : ReferenceReduction.Bound rules) (μ : Substitution s)
    (made : Quiets rules) (ts : List (Term s)) :
    (quietCells rules μ made (ts.map (keyCell rules))).2 = (ts.map μ.apply).all (quiet rules) := by
  induction ts generalizing made with
  | nil => rfl
  | cons t ts ih =>
    rw [List.map_cons,List.map_cons,List.all_cons]
    unfold quietCells
    dsimp only [keyCell]
    by_cases same : untouched μ.support t.variables = true
    · rw [apply_untouched μ t same]
      simp only [same,↓reduceIte]
      by_cases yes : quiet rules t = true
      · simp only [yes,↓reduceIte,Bool.true_and]
        exact ih made
      · simp only [yes,Bool.false_eq_true,↓reduceIte]
        simp
    · simp only [same,Bool.false_eq_true,↓reduceIte]
      have head := quietS_eq bound made (μ.apply t)
      split
      · next more ok =>
        rw [ok] at head
        rw [ih more,← head,Bool.true_and]
      · next more ok =>
        rw [ok] at head
        rw [← head,Bool.false_and]

/-- A slot with its value, the variables of the value and its normal form. -/
def valueCell (rules : List (Equation s)) (fuel : Nat) (value : Fin n → Term s) (i : Fin n) :
    Fin n × Term s × List Variable × Option (Term s) :=
  (i,value i,(value i).variables,ReferenceReduction.follow rules fuel (value i))

/-- The instances of the stored terms. -/
def imagesF (μ : Substitution s) (cells : List (Term s × List Variable × Bool)) : List (Term s) :=
  cells.map fun c => if untouched μ.support c.2.1 then c.1 else μ.apply c.1

theorem imagesF_eq (μ : Substitution s) (ts : List (Term s)) :
    imagesF μ (ts.map (keyCell rules)) = ts.map μ.apply := by
  unfold imagesF
  rw [List.map_map]
  apply List.map_congr_left
  intro t _
  dsimp only [Function.comp,keyCell]
  by_cases same : untouched μ.support t.variables = true
  · simp only [same,↓reduceIte]
    exact (apply_untouched μ t same).symm
  · simp only [same,Bool.false_eq_true,↓reduceIte]

/-- The normal form along the first rewrite path, read off for a term whose
normality test has been made and found no redex. -/
def followQ (rules : List (Equation s)) (fuel : Nat) (made : Quiets rules) (t : Term s) :
    Option (Term s) :=
  match fuel with
  | 0 => ReferenceReduction.follow rules 0 t
  | fuel + 1 =>
    match (made.getD ((code (numberedTerm t)).toNat % made.size) []).find? fun e =>
        decide (e.val.1 = numberedTerm t) with
    | some e => if e.val.2 then some t else ReferenceReduction.follow rules (fuel + 1) t
    | none => ReferenceReduction.follow rules (fuel + 1) t

theorem followQ_eq (bound : ReferenceReduction.Bound rules) (fuel : Nat) (made : Quiets rules)
    (t : Term s) :
    followQ rules fuel made t = ReferenceReduction.follow rules fuel t := by
  unfold followQ
  split
  · rfl
  · next fuel =>
    split
    · next e found =>
      by_cases yes : e.val.2 = true
      · simp only [yes,↓reduceIte]
        have hit := List.find?_some found
        simp only [decide_eq_true_eq] at hit
        have still : quiet rules t = true := by
          rw [← TableNarrowing.quiet_number bound t]
          change quiet rules (numberedTerm t) = true
          rw [← hit,← e.property]
          exact yes
        rw [quiet_eq,List.isEmpty_iff] at still
        rw [ReferenceReduction.follow_succ,still]
      · simp only [yes,Bool.false_eq_true,↓reduceIte]
    · rfl

/-- The normal forms of the successor's values. A value that the substitution
keeps has its stored normal form. -/
def settleF (rules : List (Equation s)) (fuel : Nat) (made : Quiets rules) (j : Fin n)
    (b : RootNarrowing.Branch s) (cells : List (Fin n × Term s × List Variable × Option (Term s))) :
    Option (List (Term s)) :=
  cells.mapM fun c =>
    if c.1 = j then ReferenceReduction.follow rules fuel b.value
    else if untouched b.subst.support c.2.2.1 then c.2.2.2
    else followQ rules fuel made (b.subst.apply c.2.1)

theorem settleF_eq (bound : ReferenceReduction.Bound rules) (fuel : Nat) (made : Quiets rules) (j : Fin n) (b : RootNarrowing.Branch s)
    (value : Fin n → Term s) :
    settleF rules fuel made j b ((List.finRange n).map (valueCell rules fuel value)) =
      settle rules fuel (replace (fun i => b.subst.apply (value i)) j b.value) := by
  unfold settleF settle
  simp only [followQ_eq bound]
  have listed : List.ofFn (replace (fun i => b.subst.apply (value i)) j b.value) =
      (List.finRange n).map (replace (fun i => b.subst.apply (value i)) j b.value) := by
    apply List.ext_getElem <;> simp
  rw [listed,List.mapM_map,List.mapM_map]
  congr 1
  funext i
  dsimp only [Function.comp,valueCell,replace]
  by_cases here : i = j
  · simp only [here,↓reduceIte]
  · simp only [here,↓reduceIte]
    by_cases same : untouched b.subst.support (value i).variables = true
    · simp only [same,↓reduceIte]
      rw [apply_untouched b.subst (value i) same]
    · simp only [same,Bool.false_eq_true,↓reduceIte]

/-- `childOk` with the unchanged images and values read from the member, and
the coverage test given as a function. -/
def childF (rules : List (Equation s)) (fuel : Nat) (cover : List (Term s) → Bool)
    (keyCells : List (Term s × List Variable × Bool))
    (valueCells : List (Fin n × Term s × List Variable × Option (Term s))) (j : Fin n)
    (made : Quiets rules) (b : RootNarrowing.Branch s) : Quiets rules × Option Bool :=
  -- The caller is asked before every successor.
  Interrupt.guard (made,none) fun _ =>
    match quietCells rules b.subst made keyCells with
    | (more,true) =>
      (more,(settleF rules fuel more j b valueCells).map fun values =>
        cover (imagesF b.subst keyCells ++ values))
    | (more,false) => (more,some true)

theorem childF_eq (bound : ReferenceReduction.Bound rules) (keys : List Variable) (fuel : Nat)
    {cover : List (Term s) → Bool} {rows : List (List (Term s))} (same : ∀ c, cover c = covered rows c)
    (p : Point s n) (j : Fin n) (made : Quiets rules) (b : RootNarrowing.Branch s) :
    (childF rules fuel cover ((keys.map p.assignment.image).map (keyCell rules))
      ((List.finRange n).map (valueCell rules fuel p.value)) j made b).2 =
      childOk rules keys fuel rows p j b := by
  unfold childF childOk
  dsimp only
  have images : keys.map (b.subst.compose p.assignment).image =
      (keys.map p.assignment.image).map b.subst.apply := by
    rw [List.map_map]
    rfl
  have quiet := quietCells_eq bound b.subst made (keys.map p.assignment.image)
  rw [images,imagesF_eq]
  simp only [settleF_eq bound,same]
  split
  · next more ok =>
    rw [ok] at quiet
    simp only [← quiet,↓reduceIte]
  · next more ok =>
    rw [ok] at quiet
    change false = _ at quiet
    rw [← quiet]
    rfl

/-- What the closure test keeps from one member to the next: the root
branches of the numbered terms and the normality tests. -/
abbrev Memo (rules : List (Equation s)) (bound : ReferenceReduction.Bound rules) :=
  Roots rules bound × Quiets rules

/-- `closedAt` for the narrower of the checker, with the root branches and
the normality tests looked up. -/
def strictAtF (rules : List (Equation s)) (bound : ReferenceReduction.Bound rules)
    (query : Fin n → Term s) (keys : List Variable) (fuel : Nat) (cover : List (Term s) → Bool)
    (state : Memo rules bound) (p : Point s n) : Memo rules bound × Option Bool :=
  let keyCells := (keys.map p.assignment.image).map (keyCell rules)
  let valueCells := (List.finRange n).map (valueCell rules fuel p.value)
  let avoid := (TableNarrowing.cells keys p).flatMap Term.variables
  everyS (fun (st : Memo rules bound) j =>
    if idle (query j) then (st,some true)
    else
      let found := positionsS (rootsS bound avoid) st.1 (p.value j)
      let done := everyS (childF rules fuel cover keyCells valueCells j) st.2 found.2
      ((found.1,done.1),done.2)) state (List.finRange n)

theorem strictAtF_eq (bound : ReferenceReduction.Bound rules)
    (vars : Normalized (ruleRoot rules) Substitution.identity) (fuel : Nat)
    {cover : List (Term s) → Bool} {rows : List (List (Term s))} (same : ∀ c, cover c = covered rows c)
    (state : Memo rules bound) (p : Point s n) :
    (strictAtF rules bound query (keysOf query) fuel cover state p).2 =
      strictAt rules query (keysOf query) (TableNarrowing.checking bound vars query).branches
        fuel rows p := by
  unfold strictAtF strictAt
  dsimp only
  apply everyS_eq
  intro st j
  split
  · rfl
  · dsimp only
    rw [everyS_eq (childF_eq bound (keysOf query) fuel same p j),
      positionsS_eq (rootsS_eq bound (TableNarrowing.cells (keysOf query) p))]
    rfl

/-- `closedAt` for the narrower of the checker. The ordered scan looks its
root branches and normality tests up; the whole layer is read again, without
them, only when the depth ended the scan. -/
def closedAtF (rules : List (Equation s)) (bound : ReferenceReduction.Bound rules)
    (query : Fin n → Term s) (keys : List Variable)
    (branches : Point s n → Fin n → List (RootNarrowing.Branch s)) (fuel : Nat)
    (cover : List (Term s) → Bool) (rows : List (List (Term s))) (state : Memo rules bound)
    (p : Point s n) : Memo rules bound × Option Bool :=
  match strictAtF rules bound query keys fuel cover state p with
  | (next,none) => (next,rescue rules query keys branches fuel rows p)
  | other => other

theorem closedAtF_eq (bound : ReferenceReduction.Bound rules)
    (vars : Normalized (ruleRoot rules) Substitution.identity) (fuel : Nat)
    {cover : List (Term s) → Bool} {rows : List (List (Term s))} (same : ∀ c, cover c = covered rows c)
    (state : Memo rules bound) (p : Point s n) :
    (closedAtF rules bound query (keysOf query) (TableNarrowing.checking bound vars query).branches
        fuel cover rows state p).2 =
      closedAt rules query (keysOf query) (TableNarrowing.checking bound vars query).branches
        fuel rows p := by
  unfold closedAtF closedAt
  have head := strictAtF_eq (query := query) bound vars fuel same state p
  generalize strictAtF rules bound query (keysOf query) fuel cover state p = result at head ⊢
  obtain ⟨next,value⟩ := result
  change value = _ at head
  rw [← head]
  cases value <;> rfl

/-- The number of positions of a term that are not variables. -/
def sites : Term s → Nat
  | .var _ => 0
  | .atom _ => 1
  | .free _ xs => 1 + (List.ofFn fun i => sites (xs i)).sum
  | .comm _ a b => 1 + sites a + sites b
  | .ac _ a b => 1 + sites a + sites b

/-- The number of positions at which the narrowing layer of a member looks
for root branches. -/
def charge (query : Fin n → Term s) (p : Point s n) : Nat :=
  ((List.finRange n).map fun j => if idle (query j) then 0 else sites (p.value j)).sum

/-- The number of leading entries whose charges, added to what is already
spent, stay within the work limit. -/
def admitted (work : Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | spent, c :: cs => if work < spent + c then 0 else 1 + admitted work (spent + c) cs

def closure (rules : List (Equation s)) (query : Fin n → Term s) (keys : List Variable)
    (branches : Point s n → Fin n → List (RootNarrowing.Branch s)) (fuel work limit : Nat)
    (rows : List (List (Term s))) : List (Point s n) → Nat → Verdict
  | [], _ => .accepted
  | p :: rest, index =>
    if work != 0 && decide (limit ≤ index) then .exhausted
    else
      match closedAt rules query keys branches fuel rows p with
      | none => .exhausted
      | some true => closure rules query keys branches fuel work limit rows rest (index + 1)
      | some false => .rejected 3 index

theorem closure_accepted {keys : List Variable}
    {branches : Point s n → Fin n → List (RootNarrowing.Branch s)}
    {fuel work limit : Nat} {rows : List (List (Term s))} {todo : List (Point s n)} {index : Nat}
    (h : closure rules query keys branches fuel work limit rows todo index = .accepted) :
    ∀ p ∈ todo, closedAt rules query keys branches fuel rows p = some true := by
  induction todo generalizing index with
  | nil => exact fun _ hp => nomatch hp
  | cons p rest ih =>
    simp only [closure] at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · next ok =>
        intro x hx
        rcases List.mem_cons.mp hx with rfl | later
        · exact ok
        · exact ih h x later
      · contradiction

/-- The closure test: the normalized query and every normalized narrowing
successor of a member are instances of a member. `fuel` bounds the length of
every rewrite path that is followed. `work`, when nonzero, bounds the number
of positions at which root branches are looked for, added up over the members
in their order: the member whose layer would exceed it is not narrowed and
the budget is reported as exhausted. Each position costs at most one
unification per rule or needed extension and view of the position. -/
def saturated (rules : List (Equation s)) (bound : ReferenceReduction.Bound rules)
    (vars : Normalized (ruleRoot rules) Substitution.identity) (query : Fin n → Term s)
    (fuel work : Nat) (members : List (Point s n)) : Verdict :=
  let keys := keysOf query
  let narrow := TableNarrowing.checking bound vars query
  match settle rules fuel query with
  | none => .exhausted
  | some first =>
    let rows := members.map (terms keys)
    if covered rows (keys.map (Substitution.identity (sig := s)).image ++ first) then
      closure rules query keys narrow.branches fuel work
        (admitted work 0 (members.map (charge query))) rows members 0
    else .rejected 2 0

/-- `closure` for the narrower of the checker, with what one member computed
handed to the next. -/
def closureF (rules : List (Equation s)) (bound : ReferenceReduction.Bound rules)
    (query : Fin n → Term s) (keys : List Variable)
    (branches : Point s n → Fin n → List (RootNarrowing.Branch s)) (fuel work limit : Nat)
    (cover : List (Term s) → Bool) (rows : List (List (Term s))) :
    Memo rules bound → List (Point s n) → Nat → Verdict
  | _, [], _ => .accepted
  | state, p :: rest, index =>
    if work != 0 && decide (limit ≤ index) then .exhausted
    else
      -- The caller is asked before every member. Its reply is `false` for
      -- every caller that is a function, so this is the plain computation.
      Interrupt.guard .exhausted fun _ =>
        match closedAtF rules bound query keys branches fuel cover rows state p with
        | (_,none) => .exhausted
        | (next,some true) =>
          closureF rules bound query keys branches fuel work limit cover rows next rest (index + 1)
        | (_,some false) => .rejected 3 index

theorem closureF_eq (bound : ReferenceReduction.Bound rules)
    (vars : Normalized (ruleRoot rules) Substitution.identity) (fuel work limit : Nat)
    {cover : List (Term s) → Bool} {rows : List (List (Term s))} (same : ∀ c, cover c = covered rows c)
    (state : Memo rules bound) (todo : List (Point s n)) (index : Nat) :
    closureF rules bound query (keysOf query) (TableNarrowing.checking bound vars query).branches
        fuel work limit cover rows state todo index =
      closure rules query (keysOf query) (TableNarrowing.checking bound vars query).branches
        fuel work limit rows todo index := by
  induction todo generalizing state index with
  | nil => rfl
  | cons p rest ih =>
    rw [closureF,closure]
    have head := closedAtF_eq (query := query) bound vars fuel same state p
    generalize closedAtF rules bound query (keysOf query)
      (TableNarrowing.checking bound vars query).branches fuel cover rows state p = result at head ⊢
    obtain ⟨next,value⟩ := result
    change value = _ at head
    rw [← head]
    by_cases stop : (work != 0 && decide (limit ≤ index)) = true
    · simp only [stop,↓reduceIte]
    · simp only [stop,Bool.false_eq_true,↓reduceIte]
      match value with
      | none => rfl
      | some true => exact ih next (index + 1)
      | some false => rfl

/-- The number of positions of a term, variables included. -/
def nodes : Term s → Nat
  | .var _ => 1
  | .atom _ => 1
  | .free _ xs => 1 + (List.ofFn fun i => nodes (xs i)).sum
  | .comm _ a b => 1 + nodes a + nodes b
  | .ac _ a b => 1 + nodes a + nodes b

/-- How far apart two lists of sizes are: the sum of the differences at each place. -/
def distance : List Nat → List Nat → Nat
  | a :: as, b :: bs => (if a ≤ b then b - a else a - b) + distance as bs
  | _, _ => 0

/-- The rows, each with the sizes of its entries, in order of their distance
from the sizes of the entries of the list of terms. -/
def nearest (table : List (List (Term s) × List Nat)) (child : List (Term s)) :
    List (List (Term s)) :=
  let sizes := child.map nodes
  ((table.map fun g => (distance g.2 sizes,g.1)).mergeSort fun a b => a.1 ≤ b.1).map (·.2)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] [Interrupt] in
theorem nearest_perm (table : List (List (Term s) × List Nat)) (child : List (Term s)) :
    (nearest table child).Perm (table.map (·.1)) := by
  unfold nearest
  dsimp only
  have sorted := List.mergeSort_perm (table.map fun g => (distance g.2 (child.map nodes),g.1))
    fun a b => decide (a.1 ≤ b.1)
  refine (sorted.map (·.2)).trans ?_
  rw [List.map_map]
  rfl

/-- `covered` with the guessed substitutions tried on the rows in order of
their distance from the list of terms. A row whose entries have the sizes of
those of the list is most often the one that subsumes it. The order is the
only difference, and `List.any` does not depend on it. -/
def coveredNear (table : List (List (Term s) × List Nat)) (child : List (Term s)) : Bool :=
  covered (nearest table child) child

theorem coveredNear_eq (table : List (List (Term s) × List Nat)) (child : List (Term s)) :
    coveredNear table child = covered (table.map (·.1)) child := by
  unfold coveredNear covered
  rw [(nearest_perm table child).any_eq,(nearest_perm table child).any_eq]

/-- A row with the sizes of its entries. -/
def withSizes (g : List (Term s)) : List (Term s) × List Nat := (g,g.map nodes)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] [Interrupt] in
theorem withSizes_rows (rows : List (List (Term s))) : (rows.map withSizes).map (·.1) = rows := by
  rw [List.map_map]
  exact List.map_id' rows

/-- `saturated` with the root branches and the normality tests kept from one
member to the next, and the rows tried in order of their distance from each
successor. -/
def saturatedFast (rules : List (Equation s)) (bound : ReferenceReduction.Bound rules)
    (vars : Normalized (ruleRoot rules) Substitution.identity) (query : Fin n → Term s)
    (fuel work : Nat) (members : List (Point s n)) : Verdict :=
  let keys := keysOf query
  match settle rules fuel query with
  | none => .exhausted
  | some first =>
    let table := (members.map (terms keys)).map withSizes
    if coveredNear table (keys.map (Substitution.identity (sig := s)).image ++ first) then
      closureF rules bound query keys (TableNarrowing.checking bound vars query).branches fuel work
        (admitted work 0 (members.map (charge query))) (coveredNear table) (table.map (·.1))
        (Array.replicate 4096 [],Array.replicate 4096 []) members 0
    else .rejected 2 0

omit [Interrupt] in
@[csimp] theorem saturated_fast : @saturated = @saturatedFast := by
  funext s n _ _ _ _ _ rules bound vars query fuel work members
  unfold saturated saturatedFast
  cases settle rules fuel query with
  | none => rfl
  | some first =>
    dsimp only
    rw [coveredNear_eq,closureF_eq bound vars (same := coveredNear_eq _),withSizes_rows]

omit [Interrupt] in
private theorem sum_strict {a b : Fin n → Nat} (le : ∀ i, a i ≤ b i) (j : Fin n) (lt : a j < b j) :
    (List.ofFn a).sum < (List.ofFn b).sum := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ (f := b),List.sum_cons,List.sum_cons]
    cases j using Fin.cases with
    | zero => exact Nat.add_lt_add_of_lt_of_le lt (FoldingNarrowing.sum_mono (fun i => le i.succ))
    | succ k => exact Nat.add_lt_add_of_le_of_lt (le 0) (ih (fun i => le i.succ) k lt)

omit [Interrupt] in
/-- Coverage from a list of members in which every admissible successor of a
member is an instance of a successor of that member whose normal form a
member subsumes. The descent is on the rewrite heights of the instantiated
values: an instance of the more general successor is one rewrite step below
the instance of the member. -/
theorem covers_layers (bound : ReferenceReduction.Bound rules)
    (canonical : CanonicalPresentation (ruleRoot rules))
    (narrow : FoldingNarrowing.Narrower rules query) (members : List (Point s n))
    (valid : ∀ p ∈ members, VariantSaturation.Sound rules query p)
    (closed : ∀ p ∈ members, ∀ c ∈ expand p (narrow.branches p),
      (∀ i : Key (keysOf query), Normal (ruleRoot rules) (c.assignment.image i.val)) →
      ∃ c0 ∈ expand p (narrow.branches p), (c0.row (keysOf query)).Subsumes (c.row (keysOf query)) ∧
        ∃ m ∈ members, (m.row (keysOf query)).Subsumes
          ((⟨c0.assignment,fun i => (ReferenceReduction.reducer rules bound canonical).reduce (c0.value i)⟩ :
            Point s n).row (keysOf query)))
    (start : ∃ m ∈ members, ∃ θ : Substitution s,
      ∀ i : Key (keysOf query), EquivB (.var i.val) (θ.apply (m.assignment.image i.val)))
    (ρ : Substitution s) (norm : Normalized (ruleRoot rules) ρ) (out : Fin n → Term s)
    (forms : ∀ i, NormalForm (ruleRoot rules) (ρ.apply (query i)) (out i)) :
    ∃ p, p ∈ members ∧ ∃ δ, Fits (p.row (keysOf query)) (fun i => ρ.image i.val) out δ := by
  classical
  let keys := keysOf query
  let r := ReferenceReduction.reducer rules bound canonical
  let height := ReductionHeight.height bound canonical.terminating
  have go (k : Nat) : ∀ p, p ∈ members → ∀ δ : Substitution s,
      (∀ i : Key keys, EquivB (ρ.image i.val) (δ.apply (p.assignment.image i.val))) →
      (List.ofFn fun i => height (δ.apply (p.value i))).sum = k →
      ∃ q, q ∈ members ∧ ∃ η, Fits (q.row keys) (fun i => ρ.image i.val) out η := by
    induction k using Nat.strongRecOn with
    | ind k smaller =>
      intro p hp δ inputs rank
      have hn (i : Key keys) : Normal (ruleRoot rules) (δ.apply (p.assignment.image i.val)) :=
        (normal_equiv _ (inputs i)).mp (norm i.val)
      by_cases done : ∀ i, Normal (ruleRoot rules) (δ.apply (p.value i))
      · exact ⟨p,hp,δ,inputs,
          VariantSaturation.endpoint canonical p (valid p hp) ρ δ out forms inputs done⟩
      · obtain ⟨j,u,step⟩ : ∃ j u, StepModulo (ruleRoot rules) (δ.apply (p.value j)) u := by
          simpa only [Normal,Classical.not_forall,Classical.not_not] using done
        obtain ⟨_,hm,η,fit⟩ := expand_covers keys p (narrow.branches p) (narrow.lifts p (valid p hp))
          δ hn j u step
        obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hm
        obtain ⟨c0,_,⟨θ0,sub0⟩,m,hm,θ,sub⟩ := closed p hp c hc fun i =>
          normal_of_instance ((normal_equiv _ (fit.inputs i)).mp (hn i))
        let δ' := (η.compose θ0).compose θ
        have each (i) : height (δ'.apply (m.value i)) ≤
            height (replace (fun k => δ.apply (p.value k)) j u i) := by
          have a : EquivB (δ'.apply (m.value i)) ((η.compose θ0).apply (r.reduce (c0.value i))) := by
            rw [Substitution.apply_compose]
            exact ((sub.values i).subst (η.compose θ0).image).symm
          have b : height ((η.compose θ0).apply (r.reduce (c0.value i))) ≤
              height ((η.compose θ0).apply (c0.value i)) :=
            ReductionHeight.reduces bound canonical.terminating
              (SpecializedFresh.reduces_subst rules _ (r.correct (c0.value i)).normalForm.1)
          have c' : EquivB ((η.compose θ0).apply (c0.value i)) (η.apply (c.value i)) := by
            rw [Substitution.apply_compose]
            exact ((sub0.values i).subst η.image).symm
          exact Nat.le_trans (Nat.le_of_eq (ReductionHeight.equiv bound canonical.terminating a))
            (Nat.le_trans b (Nat.le_of_eq ((ReductionHeight.equiv bound canonical.terminating c').trans
              (ReductionHeight.equiv bound canonical.terminating (fit.values i)).symm)))
        have strict : height (δ'.apply (m.value j)) < height (δ.apply (p.value j)) :=
          Nat.lt_of_le_of_lt (by simpa [replace] using each j) (ReductionHeight.step bound _ step)
        have less : (List.ofFn fun i => height (δ'.apply (m.value i))).sum <
            (List.ofFn fun i => height (δ.apply (p.value i))).sum := by
          apply sum_strict _ j strict
          intro i
          by_cases same : i = j
          · exact same ▸ Nat.le_of_lt strict
          · simpa [replace,same] using each i
        apply smaller _ (rank ▸ less) m hm δ' _ rfl
        intro i
        change EquivB _ (((η.compose θ0).compose θ).apply _)
        rw [Substitution.apply_compose,Substitution.apply_compose]
        exact (inputs i).trans ((fit.inputs i).trans
          (((sub0.inputs i).trans ((sub.inputs i).subst θ0.image)).subst η.image))
  obtain ⟨first,hfirst,θ,image⟩ := start
  apply go _ first hfirst (ρ.compose θ) _ rfl
  intro i
  rw [Substitution.apply_compose]
  exact (image i).subst ρ.image

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] [Interrupt] in
/-- A successor at a slot whose query term is a variable makes the image of
that variable reducible. -/
theorem idle_reducible (vars : Normalized (ruleRoot rules) Substitution.identity)
    (narrow : FoldingNarrowing.Narrower rules query) {p : Point s n} (formed : Formed rules query p)
    {j : Fin n} (still : idle (query j) = true) {b : RootNarrowing.Branch s}
    (hb : b ∈ narrow.branches p j) :
    ¬∀ i : Key (keysOf query), Normal (ruleRoot rules) ((successor p j b).assignment.image i.val) := by
  intro live
  cases at_j : query j with
  | var v =>
    have key : v ∈ keysOf query := (observed query v).mpr
      ⟨_,List.mem_ofFn.mpr ⟨j,rfl⟩,by rw [at_j]; rfl⟩
    have reply := formed.2 j
    rw [at_j] at reply
    have same : EquivB (p.assignment.image v) (p.value j) :=
      normal_reduces_equiv reply.1 (formed.1 ⟨v,key⟩)
    have step := narrow.genuine p (sound_member vars p formed) j b hb
    exact ((normal_equiv _ (same.subst b.subst.image)).mp (live ⟨v,key⟩)) _ step
  | atom _ => rw [at_j] at still; cases still
  | free _ _ => rw [at_j] at still; cases still
  | comm _ _ _ => rw [at_j] at still; cases still
  | ac _ _ _ => rw [at_j] at still; cases still

/-- A successor that was normalized and found to be an instance of a row is
subsumed by a member, with the reference normal forms as its values. -/
theorem childOk_hit (bound : ReferenceReduction.Bound rules)
    (canonical : CanonicalPresentation (ruleRoot rules)) {fuel : Nat} {members : List (Point s n)}
    {p : Point s n} {j : Fin n} {b : RootNarrowing.Branch s}
    (child : childOk rules (keysOf query) fuel (members.map (terms (keysOf query))) p j b = some true)
    (live : ((keysOf query).map (b.subst.compose p.assignment).image).all (quiet rules) = true) :
    ∃ m, m ∈ members ∧ (m.row (keysOf query)).Subsumes
      ((⟨(successor p j b).assignment,fun i =>
        (ReferenceReduction.reducer rules bound canonical).reduce ((successor p j b).value i)⟩ :
          Point s n).row (keysOf query)) := by
  unfold childOk at child
  dsimp only at child
  simp only [live,↓reduceIte] at child
  obtain ⟨values,made,sub⟩ := Option.map_eq_some_iff.mp child
  obtain ⟨k,rfl,each⟩ := mapM_ofFn _ made
  obtain ⟨m,hm,θ,fit⟩ := covered_sound (c := ⟨b.subst.compose p.assignment,k⟩) sub
  refine ⟨m,hm,θ,fit.inputs,fun i => ?_⟩
  have value := fit.values i
  change EquivB (k i) _ at value
  rw [follow_reduce bound canonical (each i)] at value
  exact value

/-- On a canonical presentation the members of a list that passes the closure
test cover every normal substitution: its images on the keys and the normal
forms of the instantiated query are an instance of a member. -/
theorem saturated_hits (bound : ReferenceReduction.Bound rules)
    (canonical : CanonicalPresentation (ruleRoot rules))
    (vars : Normalized (ruleRoot rules) Substitution.identity) {fuel work : Nat}
    {members : List (Point s n)} (formed : ∀ p ∈ members, Formed rules query p)
    (h : saturated rules bound vars query fuel work members = .accepted)
    (ρ : Substitution s) (norm : Normalized (ruleRoot rules) ρ) (out : Fin n → Term s)
    (forms : ∀ i, NormalForm (ruleRoot rules) (ρ.apply (query i)) (out i)) :
    ∃ p, p ∈ members ∧ ∃ δ, Fits (p.row (keysOf query)) (fun i => ρ.image i.val) out δ := by
  unfold saturated at h
  dsimp only at h
  let narrow := TableNarrowing.checking bound vars query
  let keys := keysOf query
  let r := ReferenceReduction.reducer rules bound canonical
  split at h
  · contradiction
  · next first seeded =>
    split at h
    · next start_ =>
      have sound (p) (hp : p ∈ members) : VariantSaturation.Sound rules query p :=
        sound_member vars p (formed p hp)
      have quietKeys {τ : Substitution s}
          (live : ∀ i : Key keys, Normal (ruleRoot rules) (τ.image i.val)) :
          (keys.map τ.image).all (quiet rules) = true := by
        have ok := (admissible_iff (query := query) bound ⟨τ,query⟩).mpr live
        rw [← normalOn_eq (rules := rules) (query := query) ⟨τ,query⟩] at ok
        simpa [normalOn,List.all_map] using ok
      have closed (p) (hp : p ∈ members) (c) (hc : c ∈ expand p (narrow.branches p))
          (live : ∀ i : Key keys, Normal (ruleRoot rules) (c.assignment.image i.val)) :
          ∃ c0 ∈ expand p (narrow.branches p), (c0.row keys).Subsumes (c.row keys) ∧
            ∃ m ∈ members, (m.row keys).Subsumes
              ((⟨c0.assignment,fun i => r.reduce (c0.value i)⟩ : Point s n).row keys) := by
        have layer_ := closure_accepted h p hp
        obtain ⟨j,_,hj⟩ := List.mem_flatMap.mp hc
        obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hj
        have moving : idle (query j) = false := by
          cases still : idle (query j) with
          | false => rfl
          | true => exact absurd live (idle_reducible vars narrow (formed p hp) still hb)
        rcases closedAt_true layer_ j moving b hb with child | ⟨j0,b0,_,hb0,child,live0,inst⟩
        · exact ⟨_,hc,Row.Subsumes.refl _,childOk_hit bound canonical child (quietKeys live)⟩
        · exact ⟨successor p j0 b0,
            List.mem_flatMap.mpr ⟨j0,List.mem_finRange j0,List.mem_map_of_mem hb0⟩,
            instanceOf_sound inst,childOk_hit bound canonical child live0⟩
      have start : ∃ m ∈ members, ∃ θ : Substitution s,
          ∀ i : Key keys, EquivB (.var i.val) (θ.apply (m.assignment.image i.val)) := by
        obtain ⟨k,rfl,_⟩ := mapM_ofFn _ seeded
        obtain ⟨m,hm,θ,fit⟩ := covered_sound (c := ⟨Substitution.identity,k⟩) start_
        exact ⟨m,hm,θ,fit.inputs⟩
      exact covers_layers bound canonical narrow members sound closed start ρ norm out forms
    · contradiction

end
end Tamarin.VariantCertificate
