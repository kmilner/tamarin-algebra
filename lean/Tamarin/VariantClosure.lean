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

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
/-- The terms of two points side by side: the images of each key, then the
values of each slot. -/
theorem zip_terms (keys : List Variable) (g t : Point s n) : (terms keys g).zip (terms keys t) =
    keys.map (fun v => (g.assignment.image v,t.assignment.image v)) ++
      List.ofFn (fun i => (g.value i,t.value i)) := by
  simp [terms,List.zip_eq_zipWith,List.zipWith_append,List.zipWith_map,List.zipWith_self,zipWith_ofFn]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
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

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
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

/-- One member's narrowing layer: every admissible successor, normalized, must
be an instance of a row. -/
def closedAt (rules : List (Equation s)) (query : Fin n → Term s) (keys : List Variable)
    (branches : Point s n → Fin n → List (RootNarrowing.Branch s)) (fuel : Nat)
    (rows : List (List (Term s))) (p : Point s n) : Option Bool :=
  every (fun j => if idle (query j) then some true
    else every (childOk rules keys fuel rows p j) (branches p j)) (List.finRange n)

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

/-- `every` with a state handed from one entry to the next. -/
def everyS {α σ : Type} (f : σ → α → σ × Option Bool) : σ → List α → σ × Option Bool
  | state, [] => (state,some true)
  | state, x :: xs =>
    match f state x with
    | (next,some true) => everyS f next xs
    | other => other

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

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
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

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
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

/-- `childOk` with the unchanged images and values read from the member. -/
def childF (rules : List (Equation s)) (fuel : Nat) (rows : List (List (Term s)))
    (keyCells : List (Term s × List Variable × Bool))
    (valueCells : List (Fin n × Term s × List Variable × Option (Term s))) (j : Fin n)
    (made : Quiets rules) (b : RootNarrowing.Branch s) : Quiets rules × Option Bool :=
  match quietCells rules b.subst made keyCells with
  | (more,true) =>
    (more,(settleF rules fuel more j b valueCells).map fun values =>
      covered rows (imagesF b.subst keyCells ++ values))
  | (more,false) => (more,some true)

theorem childF_eq (bound : ReferenceReduction.Bound rules) (keys : List Variable) (fuel : Nat) (rows : List (List (Term s))) (p : Point s n)
    (j : Fin n) (made : Quiets rules) (b : RootNarrowing.Branch s) :
    (childF rules fuel rows ((keys.map p.assignment.image).map (keyCell rules))
      ((List.finRange n).map (valueCell rules fuel p.value)) j made b).2 =
      childOk rules keys fuel rows p j b := by
  unfold childF childOk
  dsimp only
  have images : keys.map (b.subst.compose p.assignment).image =
      (keys.map p.assignment.image).map b.subst.apply := by
    rw [List.map_map]
    rfl
  have same := quietCells_eq bound b.subst made (keys.map p.assignment.image)
  rw [images,imagesF_eq]
  simp only [settleF_eq bound]
  split
  · next more ok =>
    rw [ok] at same
    simp only [← same,↓reduceIte]
  · next more ok =>
    rw [ok] at same
    change false = _ at same
    rw [← same]
    rfl

/-- What the closure test keeps from one member to the next: the root
branches of the numbered terms and the normality tests. -/
abbrev Memo (rules : List (Equation s)) (bound : ReferenceReduction.Bound rules) :=
  Roots rules bound × Quiets rules

/-- `closedAt` for the narrower of the checker, with the root branches and
the normality tests looked up. -/
def closedAtF (rules : List (Equation s)) (bound : ReferenceReduction.Bound rules)
    (query : Fin n → Term s) (keys : List Variable) (fuel : Nat) (rows : List (List (Term s)))
    (state : Memo rules bound) (p : Point s n) : Memo rules bound × Option Bool :=
  let keyCells := (keys.map p.assignment.image).map (keyCell rules)
  let valueCells := (List.finRange n).map (valueCell rules fuel p.value)
  let avoid := (TableNarrowing.cells keys p).flatMap Term.variables
  everyS (fun (st : Memo rules bound) j =>
    if idle (query j) then (st,some true)
    else
      let found := positionsS (rootsS bound avoid) st.1 (p.value j)
      let done := everyS (childF rules fuel rows keyCells valueCells j) st.2 found.2
      ((found.1,done.1),done.2)) state (List.finRange n)

theorem closedAtF_eq (bound : ReferenceReduction.Bound rules)
    (vars : Normalized (ruleRoot rules) Substitution.identity) (fuel : Nat)
    (rows : List (List (Term s))) (state : Memo rules bound) (p : Point s n) :
    (closedAtF rules bound query (keysOf query) fuel rows state p).2 =
      closedAt rules query (keysOf query) (TableNarrowing.checking bound vars query).branches
        fuel rows p := by
  unfold closedAtF closedAt
  dsimp only
  apply everyS_eq
  intro st j
  split
  · rfl
  · dsimp only
    rw [everyS_eq (childF_eq bound (keysOf query) fuel rows p j),
      positionsS_eq (rootsS_eq bound (TableNarrowing.cells (keysOf query) p))]
    rfl

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
    (query : Fin n → Term s) (keys : List Variable) (fuel work limit : Nat)
    (rows : List (List (Term s))) : Memo rules bound → List (Point s n) → Nat → Verdict
  | _, [], _ => .accepted
  | state, p :: rest, index =>
    if work != 0 && decide (limit ≤ index) then .exhausted
    else
      match closedAtF rules bound query keys fuel rows state p with
      | (_,none) => .exhausted
      | (next,some true) => closureF rules bound query keys fuel work limit rows next rest (index + 1)
      | (_,some false) => .rejected 3 index

theorem closureF_eq (bound : ReferenceReduction.Bound rules)
    (vars : Normalized (ruleRoot rules) Substitution.identity) (fuel work limit : Nat)
    (rows : List (List (Term s))) (state : Memo rules bound) (todo : List (Point s n)) (index : Nat) :
    closureF rules bound query (keysOf query) fuel work limit rows state todo index =
      closure rules query (keysOf query) (TableNarrowing.checking bound vars query).branches
        fuel work limit rows todo index := by
  induction todo generalizing state index with
  | nil => rfl
  | cons p rest ih =>
    rw [closureF,closure]
    have head := closedAtF_eq (query := query) bound vars fuel rows state p
    generalize closedAtF rules bound query (keysOf query) fuel rows state p = result at head ⊢
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

/-- `saturated` with the root branches and the normality tests kept from one
member to the next. -/
def saturatedFast (rules : List (Equation s)) (bound : ReferenceReduction.Bound rules)
    (_ : Normalized (ruleRoot rules) Substitution.identity) (query : Fin n → Term s)
    (fuel work : Nat) (members : List (Point s n)) : Verdict :=
  let keys := keysOf query
  match settle rules fuel query with
  | none => .exhausted
  | some first =>
    let rows := members.map (terms keys)
    if covered rows (keys.map (Substitution.identity (sig := s)).image ++ first) then
      closureF rules bound query keys fuel work (admitted work 0 (members.map (charge query))) rows
        (Array.replicate 4096 [],Array.replicate 4096 []) members 0
    else .rejected 2 0

@[csimp] theorem saturated_fast : @saturated = @saturatedFast := by
  funext s n _ _ _ _ rules bound vars query fuel work members
  unfold saturated saturatedFast
  simp only [closureF_eq bound vars]

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
  let g := FoldingNarrowing.expansion bound canonical vars r narrow
  split at h
  · contradiction
  · next first seeded =>
    split at h
    · next start_ =>
      have sound (p) (hp : p ∈ members) : VariantSaturation.Sound rules query p :=
        sound_member vars p (formed p hp)
      have settled {raw : Fin n → Term s} {values : List (Term s)}
          (made : settle rules fuel raw = some values) (τ : Substitution s)
          (sub : covered (members.map (terms keys)) (keys.map τ.image ++ values) = true) :
          ∃ m, m ∈ members ∧ (m.row keys).Subsumes
            ((⟨τ,fun i => r.reduce (raw i)⟩ : Point s n).row keys) := by
        obtain ⟨k,rfl,each⟩ := mapM_ofFn _ made
        obtain ⟨m,hm,θ,fit⟩ := covered_sound (c := ⟨τ,k⟩) sub
        refine ⟨m,hm,θ,fit.inputs,fun i => ?_⟩
        have value := fit.values i
        change EquivB (k i) _ at value
        rw [follow_reduce bound canonical (each i)] at value
        exact value
      have closed (p) (hp : p ∈ members) (c) (hc : c ∈ g.next p) :
          ∃ m, m ∈ members ∧ (m.row keys).Subsumes (c.row keys) := by
        have layer := closure_accepted h p hp
        obtain ⟨raw,hraw,rfl⟩ := List.mem_map.mp
          (show c ∈ ((expand p (narrow.branches p)).filter
            (FoldingNarrowing.admissible rules query)).map _ from hc)
        obtain ⟨inside,live⟩ := List.mem_filter.mp hraw
        obtain ⟨j,_,hj⟩ := List.mem_flatMap.mp inside
        obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hj
        have slot := every_true layer j (List.mem_finRange j)
        split at slot
        · next still =>
          exfalso
          cases at_j : query j with
          | var v =>
            have key : v ∈ keys := (observed query v).mpr
              ⟨_,List.mem_ofFn.mpr ⟨j,rfl⟩,by rw [at_j]; rfl⟩
            have reply := (formed p hp).2 j
            rw [at_j] at reply
            have same : EquivB (p.assignment.image v) (p.value j) :=
              normal_reduces_equiv reply.1 ((formed p hp).1 ⟨v,key⟩)
            have step := narrow.genuine p (sound p hp) j b hb
            exact ((normal_equiv _ (same.subst b.subst.image)).mp
              ((admissible_iff bound _).mp live ⟨v,key⟩)) _ step
          | atom _ => rw [at_j] at still; cases still
          | free _ _ => rw [at_j] at still; cases still
          | comm _ _ _ => rw [at_j] at still; cases still
          | ac _ _ _ => rw [at_j] at still; cases still
        · have child := every_true slot b hb
          unfold childOk at child
          dsimp only at child
          split at child
          · obtain ⟨values,made,sub⟩ := Option.map_eq_some_iff.mp child
            exact settled made _ sub
          · next bad =>
            have := (normalOn_eq (rules := rules) (query := query)
              ⟨b.subst.compose p.assignment,replace (fun i => b.subst.apply (p.value i)) j b.value⟩).trans live
            exact absurd (by simpa [normalOn,List.all_map] using this) bad
      have start : ∃ m, m ∈ members ∧ (m.row keys).Subsumes (g.seed.row keys) :=
        settled seeded _ start_
      exact covers g canonical (· ∈ members) sound closed start ρ norm out forms
    · contradiction

end
end Tamarin.VariantCertificate
