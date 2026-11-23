import Tamarin.BagSearch

/-! Finite structural reference for whole-term matching. A branch records an
image requirement at each pattern-variable occurrence. Distinct occurrences
may constrain the same variable, even across different equations.

`branches` splits an AC subject in every possible way and is the plain
specification. Equality and the matcher run on `BagMatching.rows`, which
lists each distinct assignment once. -/
namespace Tamarin.ReferenceMatching
open Matching
variable {s : Signature}

section
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

def branches : Term s → Term s → List (Requirements s)
  | .var v, t => [[(v,t)]]
  | .atom a, .atom b => if a = b then [[]] else []
  | .free f xs, .free g ys =>
    if h : f = g then together (List.ofFn fun i => branches (xs i) (ys (h ▸ i))) else []
  | .comm f a b, .comm g l r =>
    if f = g then
      combine (branches a l) (branches b r) ++ combine (branches a r) (branches b l)
    else []
  | .ac f a b, t =>
    (ACSplits.splits f t).flatMap fun (l,r) => combine (branches a l) (branches b r)
  | _, _ => []

private theorem branches_iff (σ : Substitution s) (pattern subject : Term s) :
    accepts σ (branches pattern subject) ↔ EquivB (σ.apply pattern) subject := by
  induction pattern generalizing subject with
  | var v => simp [branches, accepts, holds, Substitution.apply, Term.subst]
  | atom a =>
    cases subject with
    | atom b =>
      by_cases same : a = b
      · subst b; simp [branches, accepts, holds, Substitution.apply, Term.subst, EquivB.refl]
      · simp [branches, same, accepts]
        exact mismatch (fun h => same (Head.atom.inj h))
    | _ => simp [branches, accepts]; exact mismatch (fun h => nomatch h)
  | free f xs ih =>
    cases subject with
    | free g ys =>
      by_cases same : f = g
      · subst g
        simp only [branches, ↓reduceDIte, together_iff]
        change _ ↔ EquivB (.free f (fun i => σ.apply (xs i))) (.free f ys)
        rw [free_equiv_iff]
        constructor
        · exact fun hs i => (ih i (ys i)).mp (hs _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
        · rintro hs _ hm
          obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
          exact (ih i (ys i)).mpr (hs i)
      · simp [branches, same, accepts]
        exact mismatch (fun h => same (Head.free.inj h))
    | _ => simp [branches, accepts]; exact mismatch (fun h => nomatch h)
  | comm f a b ia ib =>
    cases subject with
    | comm g l r =>
      by_cases same : f = g
      · subst g
        have append (xs ys : List (Requirements s)) :
            accepts σ (xs ++ ys) ↔ accepts σ xs ∨ accepts σ ys := by
          simp [accepts, List.mem_append, or_and_right, exists_or]
        simp only [branches, ite_true, append, combine_iff, ia, ib]
        exact (Commutative.equiv_iff ..).symm
      · simp [branches, same, accepts]
        exact mismatch (fun h => same (Head.comm.inj h))
    | _ => simp [branches, accepts]; exact mismatch (fun h => nomatch h)
  | ac f a b ia ib =>
    constructor
    · rintro ⟨row,member,sat⟩
      obtain ⟨⟨l,r⟩,split,br⟩ := List.mem_flatMap.mp member
      obtain ⟨hl,hr⟩ := (combine_iff σ _ _).mp ⟨row,br,sat⟩
      exact (EquivB.ac_congr f ((ia l).mp hl) ((ib r).mp hr)).trans (ACSplits.sound f _ split).symm
    · intro eq
      obtain ⟨l,r,split,hl,hr⟩ := ACSplits.complete f eq.symm
      obtain ⟨row,member,sat⟩ := (combine_iff σ _ _).mpr ⟨(ia l).mpr hl,(ib r).mpr hr⟩
      exact ⟨row,List.mem_flatMap.mpr ⟨(l,r),split,member⟩,sat⟩

private theorem mentions (p t : Term s) {row} (hr : row ∈ branches p t)
    {v} (hv : p.Occurs v) : ∃ u, (v,u) ∈ row := by
  induction p generalizing t row with
  | var w =>
    obtain rfl := hv
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_singleton_self _⟩
  | atom => contradiction
  | free f xs ih =>
    cases t <;> simp only [branches, List.not_mem_nil] at hr
    split at hr
    · obtain ⟨i,occ⟩ := hv
      obtain ⟨part,hp,sub⟩ := part_of_together _ hr (List.mem_ofFn.mpr ⟨i,rfl⟩)
      obtain ⟨u,hu⟩ := ih i _ hp occ
      exact ⟨u,sub hu⟩
    · contradiction
  | comm f a b ia ib =>
    cases t <;> simp only [branches, List.not_mem_nil] at hr
    split at hr
    · rcases List.mem_append.mp hr with member | member <;>
        exact mentions_combine member (hv.imp (fun av _ hit => ia _ hit av) (fun bv _ hit => ib _ hit bv))
    · contradiction
  | ac f a b ia ib =>
    obtain ⟨⟨l, r⟩, _, member⟩ := List.mem_flatMap.mp hr
    exact mentions_combine member (hv.imp (fun av _ hit => ia l hit av) (fun bv _ hit => ib r hit bv))

/-- When the left-hand variables are rigid, their required images must be
the same variables. The same decomposition thus decides ordinary B-equality.
This is the specification used to justify `equal`; it is never run. -/
private def equalRef (a b : Term s) : Bool :=
  (branches a b).any fun row => row.all fun (v,t) => isVariable v t

private theorem equalRef_iff (a b : Term s) : equalRef a b = true ↔ EquivB a b := by
  apply Iff.trans _ (by simpa using branches_iff (Substitution.identity : Substitution s) a b)
  simp [equalRef, accepts, holds, isVariable_iff, Substitution.identity, Prod.forall]

/-- Ordinary B-equality: every variable of the left term is rigid, so each of
its operands removes one equal operand of the right term. No bindable variable
occurs, hence the comparison passed to the bag matcher is never consulted. -/
def equal (a b : Term s) : Bool :=
  (BagMatching.rows [] (fun _ => false) equalRef a b).any fun row => row.all fun (v,t) => isVariable v t

theorem equal_iff (a b : Term s) : equal a b = true ↔ EquivB a b := by
  have rows := BagMatching.rows_iff (tab := []) (bind := fun _ => false) equalRef_iff
    (Substitution.identity : Substitution s) a b (fun _ _ _ => rfl) (BagMatching.fits_nil _)
  apply Iff.trans _ (by simpa using rows)
  simp [equal, accepts, holds, isVariable_iff, Substitution.identity, Prod.forall]

/-- Occurrences of a variable as a direct operand of an application of `g`. -/
private def direct (g : s.ACSym) (v : Variable) : Term s → Nat
  | .ac f a b => if f = g then direct g v a + direct g v b else 0
  | .var w => if w = v then 1 else 0
  | _ => 0

/-- The variables that are direct operands of an application of `g`. -/
private def operandVariables (g : s.ACSym) : Term s → List Variable
  | .ac f a b => if f = g then operandVariables g a ++ operandVariables g b else []
  | .var w => [w]
  | _ => []

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] in
open Classical in
private theorem direct_le (g : s.ACSym) (v : Variable) (σ : Substitution s) (t : Term s)
    (c : Cancellation.Class s) :
    direct g v t * (Cancellation.flatten g (σ.image v)).count c ≤
      (Cancellation.flatten g (σ.apply t)).count c := by
  induction t with
  | var w =>
    by_cases same : w = v
    · subst same
      simp only [direct, ite_true, Nat.one_mul]
      exact Nat.le_refl _
    · simp [direct, same]
  | ac f a b ia ib =>
    by_cases same : f = g
    · subst same
      have shape : σ.apply (.ac f a b) = .ac f (σ.apply a) (σ.apply b) := rfl
      simp only [direct, ite_true, shape, Cancellation.flatten_ac, List.count_append, Nat.add_mul]
      omega
    · simp [direct, same]
  | _ => simp [direct]

/-- Each equation between an AC application and its subject bounds the image
of every bindable variable that is a direct operand of the application. -/
private def recorded (bind : Variable → Bool) (p : Problem s) : List (BagMatching.Bound s) :=
  p.flatMap fun e =>
    match e.lhs with
    | .ac g _ _ =>
      let bag := ACRepresentation.flatten g e.rhs
      ((operandVariables g e.lhs).filter bind).eraseDups.map fun v =>
        ⟨g, v, direct g v e.lhs, bag⟩
    | _ => []

/-- The bounds that tie one variable to several equations. A single equation
tells the search nothing beyond its own operands. -/
private def bounds (bind : Variable → Bool) (p : Problem s) : List (BagMatching.Bound s) :=
  match p with
  | [] | [_] => []
  | _ =>
    let all := recorded bind p
    all.filter fun b => 2 ≤ all.countP fun c => c.g = b.g && c.v == b.v

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] in
open Classical in
private theorem bounds_fit (bind : Variable → Bool) (p : Problem s) (σ : Substitution s)
    (matched : Matches p σ) : BagMatching.Fits (bounds bind p) σ := by
  have all : BagMatching.Fits (recorded bind p) σ := by
    intro b hb c
    obtain ⟨e, he, inside⟩ := List.mem_flatMap.mp hb
    split at inside
    · next g l r shape =>
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp inside
      have same := (Cancellation.flatten_equiv g (matched e he)).count_eq c
      rw [BagMatching.cls_flatten]
      exact same ▸ direct_le g v σ e.lhs c
    · contradiction
  unfold bounds
  split
  · exact BagMatching.fits_nil σ
  · exact BagMatching.fits_nil σ
  · exact fun b hb => all b (List.mem_filter.mp hb).1

private def queryBranches (bind : Variable → Bool) (p : Problem s) :=
  BagMatching.joined equal (p.map fun e => BagMatching.rows (bounds bind p) bind equal e.lhs e.rhs)

private theorem query_complete (bind : Variable → Bool) (p : Problem s) (σ : Substitution s)
    (matched : Matches p σ)
    (fixed : ∀ e ∈ p, ∀ v, e.lhs.Occurs v → bind v = false → σ.image v = .var v) :
    accepts σ (queryBranches bind p) := by
  apply (BagMatching.joined_iff (fun a b => (equal_iff a b).mpr) σ _).mpr
  intro rows member
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp member
  exact (BagMatching.rows_iff equal_iff σ e.lhs e.rhs (fixed e he) (bounds_fit bind p σ matched)).mpr
    (matched e he)

private theorem query_mentions (bind : Variable → Bool) (p : Problem s) {row}
    (member : row ∈ queryBranches bind p) {v} (obs : Observed p v) (hb : bind v = true) :
    ∃ t, (v,t) ∈ row := by
  obtain ⟨e,he,occ⟩ := obs
  obtain ⟨part,hp,sub⟩ := BagMatching.part_of_joined _ member (List.mem_map_of_mem he)
  obtain ⟨t,ht⟩ := BagMatching.rows_mentions hp occ hb
  exact ⟨t,sub ht⟩

private def keys (p : Problem s) (bindable : List Variable) : List Variable :=
  (MaudeOperations.patternVariables p).filter (fun v => bindable.contains v)

private def imageAt (row : Requirements s) (domain : List Variable) (v : Variable) : Term s :=
  let t := (row.lookup v).getD (.var v)
  if v ∈ domain ∧ t.checkSort v.sort = true then t else .var v

private def assignment (row : Requirements s) (domain : List Variable) : Substitution s where
  image := imageAt row domain
  support := domain
  outside v hv := by simp [imageAt,hv]
  sorted v := by
    simp only [imageAt]
    split
    · next h => exact Term.checkSort_sound _ _ h.2
    · exact .var v

/-- A branch of the whole query already satisfies its own requirements: the
requirements on one variable agree, each concerns a bindable pattern variable,
and each image fits the sort of its variable. -/
private theorem query_holds (p : Problem s) (bindable : List Variable) {row}
    (member : row ∈ queryBranches (fun v => bindable.contains v) p) :
    holds (assignment row (keys p bindable)) row := by
  have entry {v t} (h : (v,t) ∈ row) : v ∈ keys p bindable ∧ t.checkSort v.sort = true := by
    obtain ⟨rows,hrows,part,hp,hit⟩ := BagMatching.entry_of_joined _ member h
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hrows
    obtain ⟨occ,allowed,ok⟩ := BagMatching.rows_entries hp hit
    exact ⟨by simpa [keys] using ⟨⟨e,he,occ⟩,by simpa using allowed⟩,ok⟩
  intro v t h
  obtain ⟨u,lookup,hit⟩ := lookup_requirement row ⟨t,h⟩
  have same := BagMatching.consistent_pairs (fun a b => (equal_iff a b).mp)
    (BagMatching.joined_consistent _ member) hit h
  simpa [assignment,imageAt,lookup,(entry hit).1,(entry hit).2] using same

/-- Each branch of the bag matcher determines one answer. No candidate is
checked again on the equations. -/
def solve (p : Problem s) (bindable : List Variable) : List (Substitution s) :=
  let domain := keys p bindable
  (queryBranches (fun v => bindable.contains v) p).map fun row => assignment row domain

variable [Interrupt]

/-- The first answer of `solve`, found without listing the others. -/
def first (p : Problem s) (bindable : List Variable) : Option (Substitution s) :=
  let domain := keys p bindable
  let tab := bounds (fun v => bindable.contains v) p
  BagMatching.joinedF equal
    (p.map fun e => BagMatching.rowsF tab (fun v => bindable.contains v) equal e.lhs e.rhs)
    fun row => some (assignment row domain)

theorem first_eq (p : Problem s) (bindable : List Variable) :
    first p bindable = (solve p bindable).head? := by
  unfold first solve queryBranches
  rw [BagMatching.joinedF_eq equal p _
    (fun e => BagMatching.rows (bounds (fun v => bindable.contains v) p)
      (fun v => bindable.contains v) equal e.lhs e.rhs)
    (fun e _ k => BagMatching.rowsF_eq _ (fun v => bindable.contains v) equal e.lhs e.rhs k),
    List.head?_map, BagMatching.findSome_some]

omit [Interrupt] in
private theorem around_holds (f : s.ACSym) (pattern subject : Term s)
    {out : Requirements s × List (Term s)}
    (member : out ∈ BagMatching.around (fun _ => true) equal f pattern subject) :
    holds (assignment out.1 pattern.variables) out.1 := by
  intro v t h
  obtain ⟨u,lookup,hit⟩ := lookup_requirement out.1 ⟨t,h⟩
  obtain ⟨occ,_,ok⟩ := BagMatching.around_entries member hit
  have key : v ∈ pattern.variables := (Term.mem_variables ..).mpr occ
  have same := BagMatching.consistent_pairs (fun a b => (equal_iff a b).mp)
    (BagMatching.around_consistent member) hit h
  simpa [assignment,imageAt,lookup,key,ok] using same

/-- Instances of a pattern as a proper sub-product of an application of `f`,
each with the product of the operands outside the instance. The subject is
read once as a bag; no partition of its operands is enumerated. -/
def subproducts (f : s.ACSym) (pattern subject : Term s) : List (Substitution s × Term s) :=
  match BagMatching.around (fun _ => true) equal f pattern subject with
  | [] => []
  | found =>
    let domain := pattern.variables
    found.filterMap fun out =>
      (ACRepresentation.decode f out.2).map fun rest => (assignment out.1 domain, rest)

omit [Interrupt] in
private theorem subproducts_eq (f : s.ACSym) (pattern subject : Term s) :
    subproducts f pattern subject =
      (BagMatching.around (fun _ => true) equal f pattern subject).filterMap fun out =>
        (ACRepresentation.decode f out.2).map fun rest => (assignment out.1 pattern.variables, rest) := by
  unfold subproducts
  split
  · next none_ => rw [none_]; rfl
  · rfl

omit [Interrupt] in
theorem subproducts_sound (f : s.ACSym) (pattern subject : Term s) {θ : Substitution s} {rest : Term s}
    (member : (θ,rest) ∈ subproducts f pattern subject) :
    EquivB subject (.ac f (θ.apply pattern) rest) := by
  rw [subproducts_eq] at member
  obtain ⟨out,hout,made⟩ := List.mem_filterMap.mp member
  obtain ⟨r,dec,eq⟩ := Option.map_eq_some_iff.mp made
  cases eq
  have bags := (BagMatching.around_sound (bind := fun _ => true) equal_iff _ f pattern subject
    (fun _ _ hb => absurd hb (by simp)) hout (around_holds f pattern subject hout)).1
  have e := Cancellation.fold_perm f bags
  rw [Cancellation.fold_flatten,Cancellation.fold_append,Cancellation.fold_flatten,
    BagMatching.fold_cls,dec] at e
  exact Quotient.exact (Option.some.inj e)

omit [Interrupt] in
theorem subproducts_complete (f : s.ACSym) (pattern subject : Term s) (σ : Substitution s)
    {rem : Term s} (h : EquivB subject (.ac f (σ.apply pattern) rem)) :
    ∃ θ rest, (θ,rest) ∈ subproducts f pattern subject ∧
      Substitution.AgreesOn pattern.Occurs σ θ ∧ EquivB rem rest := by
  have bags := Cancellation.flatten_equiv f h
  rw [Cancellation.flatten_ac] at bags
  have some_ : Cancellation.flatten f rem ≠ [] := fun e => by
    have folded := Cancellation.fold_flatten f rem
    rw [e] at folded
    cases folded
  obtain ⟨out,hout,sat,left⟩ := BagMatching.around_complete (bind := fun _ => true) equal_iff σ f
    pattern subject (fun _ _ hb => absurd hb (by simp)) bags some_
  obtain ⟨r,dec,same⟩ := BagMatching.decode_of_perm f left
  refine ⟨assignment out.1 pattern.variables,r,
    (subproducts_eq f pattern subject).symm ▸ List.mem_filterMap.mpr ⟨out,hout,by simp [dec]⟩,
    fun v occ => ?_,same⟩
  have key : v ∈ pattern.variables := (Term.mem_variables ..).mpr occ
  obtain ⟨u,lookup,hit⟩ := lookup_requirement out.1 (BagMatching.around_mentions hout occ rfl)
  have image := sat v u hit
  have sorted := SortClash.check_equiv image v.sort ▸ Term.checkSort_complete (σ.sorted v)
  simpa [assignment,imageAt,lookup,key,sorted] using image

/-- The first entry of `subproducts`, found without listing the others. -/
def subproductF (f : s.ACSym) (pattern subject : Term s) : Option (Substitution s × Term s) :=
  BagMatching.aroundF (fun _ => true) equal f pattern subject fun out =>
    (ACRepresentation.decode f out.2).map fun rest => (assignment out.1 pattern.variables, rest)

theorem subproductF_eq (f : s.ACSym) (pattern subject : Term s) :
    subproductF f pattern subject = (subproducts f pattern subject).head? := by
  rw [subproducts_eq, List.head?_filterMap, subproductF, BagMatching.aroundF_eq]

end

/-- Full scoped matching, including rigid subject variables, requires equality
on symbol identities alone. There is no restriction on input sorts or size. -/
def matcher (s : Signature) [DecidableEq s.FreeSym] [DecidableEq s.CSym]
    [DecidableEq s.ACSym] [DecidableEq s.Atom] : VerifiedMatcher s (fun _ => True) where
  run p _ bindable := solve p bindable
  correct p _ bindable := by
    constructor
    · intro σ mem
      obtain ⟨row,member,rfl⟩ := List.mem_map.mp mem
      have frozen (v : Variable) (off : ¬ (Observed p v ∧ v ∈ bindable)) :
          (assignment row (keys p bindable)).image v = .var v := by
        apply Substitution.outside
        simpa [assignment,keys] using off
      refine ⟨fun e he => ?_,frozen⟩
      obtain ⟨part,hp,sub⟩ := BagMatching.part_of_joined _ member (List.mem_map_of_mem he)
      exact BagMatching.rows_sound equal_iff _ e.lhs e.rhs
        (fun v _ hb => frozen v (fun h => by simp [h.2] at hb))
        ⟨part,hp,fun v t m => query_holds p bindable member v t (sub m)⟩
    · intro ρ matched scope
      obtain ⟨row,member,sat⟩ := query_complete (fun v => bindable.contains v) p ρ matched
        (fun e he v occ hb => scope v (fun h => by simp [h.2] at hb))
      let out := assignment row (keys p bindable)
      have agree : Substitution.AgreesOn (Observed p) ρ out := by
        intro v obs
        by_cases allowed : v ∈ bindable
        · have key : v ∈ keys p bindable := by simp [keys,obs,allowed]
          obtain ⟨u, lookup, hit⟩ := lookup_requirement row
            (query_mentions _ p member obs (by simpa using allowed))
          have same := sat v u hit
          have sorted := SortClash.check_equiv same v.sort ▸ Term.checkSort_complete (ρ.sorted v)
          simpa [out, assignment, imageAt, lookup, key, sorted] using same
        · have off : v ∉ keys p bindable := by simp [keys,allowed]
          rw [scope v (fun h => allowed h.2), out.outside v off]
          exact .refl _
      exact ⟨out,List.mem_map.mpr ⟨row,member,rfl⟩,agree⟩

end Tamarin.ReferenceMatching
