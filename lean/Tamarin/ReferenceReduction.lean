import Tamarin.ReferenceMatching
import Tamarin.ReduceViaSteps
import Tamarin.NarrowingPositions

/-! Complete ordinary one-step rewriting for the active equation table. At an
AC head Maude can replace a matched subproduct and retain its complement.
Here each rule is matched against the bag of operands with the complement
left over, so every such extension is found without splitting the operands. -/
namespace Tamarin.ReferenceReduction
open Rewriting MaudeOperations
open ACSubproductReduction ContextualReduction
variable {s : Signature}

def Bound (rules : List (Equation s)) : Prop :=
  ∀ r ∈ rules, ∀ v, r.rhs.Occurs v → r.lhs.Occurs v

private def Represents (rows : List (Term s)) (t : Term s) : Prop :=
  ∃ u ∈ rows, EquivB u t

private theorem append_iff (xs ys : List (Term s)) (b : Term s) :
    Represents (xs ++ ys) b ↔ Represents xs b ∨ Represents ys b := by
  simp [Represents,List.mem_append,or_and_right,exists_or]

private theorem lift_iff {R : Root s} {a : Term s} {rows : List (Term s)}
    (ih : ∀ u, Represents rows u ↔ StepModulo R a u)
    (build : Term s → Term s) (congruent : ∀ {u v}, EquivB u v → EquivB (build u) (build v))
    (b : Term s) :
    Represents (rows.map build) b ↔ ∃ v, StepModulo R a v ∧ EquivB (build v) b := by
  constructor
  · rintro ⟨_,member,eq⟩
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp member
    exact ⟨u,(ih _).mp ⟨_,hu,.refl _⟩,eq⟩
  · rintro ⟨v,step,out⟩
    obtain ⟨u,hu,eq⟩ := (ih _).mpr step
    exact ⟨_,List.mem_map_of_mem hu,(congruent eq).trans out⟩

private theorem atRoot_step {R : Root s} {a b : Term s} :
    AtRoot R a b → StepModulo R a b := fun ⟨p,q,l,hit,r⟩ => ⟨p,q,l,.root hit,r⟩

section
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

/-- A left side can match at the root only when it is a variable or carries
the head symbol of the subject. -/
private def sameHead : Term s → Term s → Bool
  | .var _, _ => true
  | .atom a, .atom b => a == b
  | .free f _, .free g _ => f == g
  | .comm f _ _, .comm g _ _ => f == g
  | .ac f _ _, .ac g _ _ => f == g
  | _, _ => false

private theorem sameHead_of_match {p t : Term s} (σ : Substitution s) (h : EquivB (σ.apply p) t) :
    sameHead p t = true := by
  cases p <;> cases t <;> first | rfl | (cases h.head_eq <;> simp [sameHead])

/-- A left side can be a proper sub-product of an application of `f` only
when it is a variable or itself an application of `f`. -/
private def groups (f : s.ACSym) : Term s → Bool
  | .var _ => true
  | .ac g _ _ => f == g
  | _ => false

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] in
private theorem groups_of_head {f : s.ACSym} {p : Term s} (σ : Substitution s)
    (h : ConstructorVariants.head (σ.apply p) = .ac f) : groups f p = true := by
  cases p <;> first | rfl | (cases h <;> simp [groups])

/-- One representative of each term modulo B, in order of first appearance. -/
private def distinct : List (Term s) → List (Term s)
  | [] => []
  | x :: xs => x :: (distinct xs).filter fun y => !ReferenceMatching.equal x y

private theorem distinct_iff (xs : List (Term s)) (b : Term s) :
    Represents (distinct xs) b ↔ Represents xs b := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    constructor
    · rintro ⟨u,member,out⟩
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_,List.mem_cons_self,out⟩
      · obtain ⟨v,hv,same⟩ := ih.mp ⟨u,(List.mem_filter.mp later).1,out⟩
        exact ⟨v,List.mem_cons_of_mem _ hv,same⟩
    · rintro ⟨u,member,out⟩
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_,List.mem_cons_self,out⟩
      · obtain ⟨v,hv,same⟩ := ih.mpr ⟨u,later,out⟩
        by_cases dup : ReferenceMatching.equal x v = true
        · exact ⟨x,List.mem_cons_self,((ReferenceMatching.equal_iff ..).mp dup).trans same⟩
        · exact ⟨v,List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hv,by simpa using dup⟩),same⟩

def roots (rules : List (Equation s)) (t : Term s) : List (Term s) :=
  rules.flatMap fun r =>
    if sameHead r.lhs t then
      let p : Problem s := [⟨r.lhs,t⟩]
      ((ReferenceMatching.matcher s).run p trivial (patternVariables p)).map (fun σ => σ.apply r.rhs)
    else []

theorem roots_iff (rules : List (Equation s)) (bound : Bound rules) (a b : Term s) :
    Represents (roots rules a) b ↔ AtRoot (ruleRoot rules) a b := by
  constructor
  · rintro ⟨_,member,out⟩
    obtain ⟨r,hr,arm⟩ := List.mem_flatMap.mp member
    split at arm
    · obtain ⟨θ,ht,rfl⟩ := List.mem_map.mp arm
      have hit := (RuleMatches.of_complete (r := r) (plain_match (ReferenceMatching.matcher s) _ trivial)).sound θ ht
      exact ⟨_,_,hit.symm,⟨r,hr,θ,rfl,rfl⟩,out⟩
    · contradiction
  · rintro ⟨_,_,before,⟨r,hr,σ,rfl,rfl⟩,after⟩
    obtain ⟨θ,ht,agree⟩ := (RuleMatches.of_complete (r := r)
      (plain_match (ReferenceMatching.matcher s) _ trivial)).complete σ before.symm
    have image := r.rhs.subst_equiv σ.image θ.image (fun v hv => agree v (bound r hr v hv))
    refine ⟨_,List.mem_flatMap.mpr ⟨r,hr,?_⟩,image.symm.trans after⟩
    rw [sameHead_of_match σ before.symm]
    exact List.mem_map.mpr ⟨θ,ht,rfl⟩

private def extensions (rules : List (Equation s)) (f : s.ACSym) (t : Term s) :=
  rules.flatMap fun r =>
    if groups f r.lhs then
      (ReferenceMatching.subproducts f r.lhs t).map fun (θ,rest) => Term.ac f (θ.apply r.rhs) rest
    else []

/-- Every one-step result, possibly several times modulo B. -/
private def steps (rules : List (Equation s)) (t : Term s) : List (Term s) :=
  roots rules t ++ match t with
  | .var _ | .atom _ => []
  | .free f xs => (List.finRange (s.arity f)).flatMap fun i =>
      (steps rules (xs i)).map fun u => .free f (fun j => if j = i then u else xs j)
  | .comm f a b =>
      (steps rules a).map (fun u => .comm f u b) ++ (steps rules b).map (.comm f a)
  | .ac f a b => extensions rules f (.ac f a b) ++
      ((steps rules a).map (fun u => .ac f u b) ++ (steps rules b).map (.ac f a))

/-- The one-step results, each listed once modulo B. -/
def successors (rules : List (Equation s)) (t : Term s) : List (Term s) :=
  distinct (steps rules t)

private theorem extension_sound (rules : List (Equation s))
    (f : s.ACSym) {a b} (hit : Represents (extensions rules f a) b) :
    StepModulo (ruleRoot rules) a b := by
  obtain ⟨_,member,out⟩ := hit
  obtain ⟨r,hr,arm⟩ := List.mem_flatMap.mp member
  split at arm
  · obtain ⟨⟨θ,rest⟩,found,rfl⟩ := List.mem_map.mp arm
    exact ⟨_,_,ReferenceMatching.subproducts_sound f r.lhs a found,
      .ac_left f rest (.root ⟨r,hr,θ,rfl,rfl⟩),out⟩
  · contradiction

private theorem extensions_cover (rules : List (Equation s)) (bound : Bound rules)
    (f : s.ACSym) {a b} (hit : Occurrence (ruleRoot rules) f a b) :
    Represents (roots rules a) b ∨ Represents (extensions rules f a) b := by
  obtain ⟨p,q,rest,group,rule,before,after⟩ := hit
  cases rest with
  | none => exact .inl ((roots_iff rules bound _ _).mpr ⟨p,q,before,rule,after⟩)
  | some rem =>
    obtain ⟨r,hr,σ,rfl,rfl⟩ := rule
    obtain ⟨θ,left,found,agree,same⟩ := ReferenceMatching.subproducts_complete f r.lhs a σ before
    have image := r.rhs.subst_equiv σ.image θ.image (fun v hv => agree v (bound r hr v hv))
    refine .inr ⟨_,List.mem_flatMap.mpr ⟨r,hr,?_⟩,
      (EquivB.ac_congr f image.symm same.symm).trans after⟩
    rw [groups_of_head σ group]
    exact List.mem_map.mpr ⟨(θ,left),found,rfl⟩

private theorem exactRaw (rules : List (Equation s)) (bound : Bound rules) (a b : Term s) :
    Represents (steps rules a) b ↔ StepModulo (ruleRoot rules) a b := by
  induction a generalizing b with
  | var v =>
    simp only [steps,List.append_nil,roots_iff rules bound]
    refine ⟨atRoot_step, ?_⟩
    rintro ⟨p,q,l,fire,r⟩
    cases p <;> cases l.head_eq
    cases fire with | root h => exact ⟨_,_,l,h,r⟩
  | atom a =>
    simp only [steps,List.append_nil,roots_iff rules bound]
    refine ⟨atRoot_step, ?_⟩
    rintro ⟨p,q,l,fire,r⟩
    cases p <;> cases l.head_eq
    cases fire with | root h => exact ⟨_,_,l,h,r⟩
  | free f xs ih =>
    rw [steps,append_iff,roots_iff rules bound,free_iff]
    apply or_congr_right
    constructor
    · rintro ⟨_,member,out⟩
      obtain ⟨i,_,member⟩ := List.mem_flatMap.mp member
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp member
      exact ⟨i,u,(ih i u).mp ⟨_,hu,.refl _⟩,out⟩
    · rintro ⟨i,v,step,out⟩
      obtain ⟨u,hu,eq⟩ := (ih i v).mpr step
      refine ⟨_,List.mem_flatMap.mpr ⟨i,List.mem_finRange _,List.mem_map.mpr ⟨u,hu,rfl⟩⟩,
        (EquivB.free f _ _ ?_).trans out⟩
      intro j
      by_cases e : j = i
      · simpa [e] using eq
      · simp [e,EquivB.refl]
  | comm f x y il ir =>
    rw [steps,append_iff,roots_iff rules bound,append_iff,comm_iff]
    rw [lift_iff il _ (fun eq => EquivB.comm_congr f eq (.refl _)),
      lift_iff ir _ (fun eq => EquivB.comm_congr f (.refl _) eq)]
  | ac f x y il ir =>
    rw [steps,append_iff,append_iff,append_iff,
      lift_iff il _ (fun eq => EquivB.ac_congr f eq (.refl _)),
      lift_iff ir _ (fun eq => EquivB.ac_congr f (.refl _) eq)]
    constructor
    · rintro (top|ext|child)
      · exact atRoot_step ((roots_iff rules bound _ _).mp top)
      · exact extension_sound rules f ext
      · exact (NarrowingPositions.ac_children_iff ..).mpr (.inr child)
    · intro step
      rcases (NarrowingPositions.ac_children_iff ..).mp step with group|child
      · exact (extensions_cover rules bound f group).elim Or.inl (Or.inr ∘ Or.inl)
      · exact .inr (.inr child)

theorem exactSteps (rules : List (Equation s)) (bound : Bound rules) (a b : Term s) :
    (∃ u ∈ successors rules a, EquivB u b) ↔ StepModulo (ruleRoot rules) a b :=
  (distinct_iff ..).trans (exactRaw rules bound a b)

private theorem distinct_head (xs : List (Term s)) : (distinct xs).head? = xs.head? := by
  cases xs <;> rfl

variable [Interrupt]

/-- The first root rewrite in the order of `roots`. -/
private def rootF (rules : List (Equation s)) (t : Term s) : Option (Term s) :=
  rules.findSome? fun r =>
    if sameHead r.lhs t then
      let p : Problem s := [⟨r.lhs,t⟩]
      (ReferenceMatching.first p (patternVariables p)).map fun σ => σ.apply r.rhs
    else none

private theorem rootF_eq (rules : List (Equation s)) (t : Term s) :
    rootF rules t = (roots rules t).head? := by
  rw [roots, BagMatching.head_flatMap, rootF]
  apply BagMatching.findSome_congr
  intro r
  split
  · rw [List.head?_map]
    dsimp only
    rw [ReferenceMatching.first_eq]
    rfl
  · rfl

/-- The first extended rewrite in the order of `extensions`. -/
private def extensionF (rules : List (Equation s)) (f : s.ACSym) (t : Term s) : Option (Term s) :=
  rules.findSome? fun r =>
    if groups f r.lhs then
      (ReferenceMatching.subproductF f r.lhs t).map fun (θ,rest) => Term.ac f (θ.apply r.rhs) rest
    else none

private theorem extensionF_eq (rules : List (Equation s)) (f : s.ACSym) (t : Term s) :
    extensionF rules f t = (extensions rules f t).head? := by
  rw [extensions, BagMatching.head_flatMap, extensionF]
  apply BagMatching.findSome_congr
  intro r
  split
  · rw [List.head?_map, ReferenceMatching.subproductF_eq]
  · rfl

/-- The first one-step result, found without listing the others. -/
private def stepF (rules : List (Equation s)) (t : Term s) : Option (Term s) :=
  BagMatching.orLater (rootF rules t) fun _ =>
    match t with
    | .var _ | .atom _ => none
    | .free f xs => (List.finRange (s.arity f)).findSome? fun i =>
        (stepF rules (xs i)).map fun u => .free f (fun j => if j = i then u else xs j)
    | .comm f a b =>
        BagMatching.orLater ((stepF rules a).map fun u => .comm f u b) fun _ =>
          (stepF rules b).map (.comm f a)
    | .ac f a b =>
        BagMatching.orLater (extensionF rules f (.ac f a b)) fun _ =>
          BagMatching.orLater ((stepF rules a).map fun u => .ac f u b) fun _ =>
            (stepF rules b).map (.ac f a)

private theorem stepF_eq (rules : List (Equation s)) (t : Term s) :
    stepF rules t = (steps rules t).head? := by
  induction t with
  | var v => simp [stepF, steps, BagMatching.orLater_eq, rootF_eq]
  | atom a => simp [stepF, steps, BagMatching.orLater_eq, rootF_eq]
  | free f xs ih =>
    rw [stepF, steps, BagMatching.orLater_eq, rootF_eq, List.head?_append, BagMatching.head_flatMap]
    congr 1
    apply BagMatching.findSome_congr
    intro i
    rw [ih i, List.head?_map]
  | comm f a b ia ib =>
    rw [stepF, steps, BagMatching.orLater_eq, rootF_eq, List.head?_append, BagMatching.orLater_eq,
      List.head?_append, List.head?_map, List.head?_map, ia, ib]
  | ac f a b ia ib =>
    rw [stepF, steps, BagMatching.orLater_eq, rootF_eq, List.head?_append, BagMatching.orLater_eq,
      BagMatching.orLater_eq, extensionF_eq, List.head?_append, List.head?_append, List.head?_map,
      List.head?_map, ia, ib]

/-- Follow first steps until none applies, for at most the given number of
steps. Each step stops at the first redex instead of listing all successors. -/
def follow (rules : List (Equation s)) : Nat → Term s → Option (Term s)
  | 0, _ => none
  | n+1, t =>
    match stepF rules t with
    | none => some t
    | some u => follow rules n u

theorem follow_succ (rules : List (Equation s)) (n : Nat) (t : Term s) :
    follow rules (n+1) t = match successors rules t with
      | [] => some t
      | u :: _ => follow rules n u := by
  have head : stepF rules t = (successors rules t).head? := by
    rw [stepF_eq, successors, distinct_head]
  rw [follow, head]
  cases successors rules t <;> rfl

/-- A rewrite at this node: at its root or, in an AC application, on one of
its proper sub-products. Rewrites inside the arguments are not looked for. -/
private def stepHere (rules : List (Equation s)) (t : Term s) : Option (Term s) :=
  BagMatching.orLater (rootF rules t) fun _ =>
    match t with
    | .ac f _ _ => extensionF rules f t
    | _ => none

/-- Rewrite at the root of a term until no rule applies there. Nothing below
the root is looked at. -/
private def chain (rules : List (Equation s)) : Nat → Term s → Option (Term s)
  | 0, _ => none
  | n+1, t =>
    match stepHere rules t with
    | none => some t
    | some u => chain rules n u

/-- Look again at a node after its arguments changed. The last flag records
whether the result is known to be irreducible: an unchanged node is exactly as
sure as its arguments, and a rewritten one is only rewritten further at its
root, so nothing is known about it. -/
private def resettle (rules : List (Equation s)) (after : Term s → Option (Term s))
    (t : Term s) (sure : Bool) : Option (Term s × Bool × Bool) :=
  match stepHere rules t with
  | none => some (t,true,sure)
  | some u => (after u).map fun v => (v,true,false)

/-- Visit a node. The result carries two flags: whether it differs from the
node, and whether it is known to be irreducible. A rewrite at the node itself
is taken first and its result handed to `again`. Otherwise the arguments are
visited, and the node is looked at again only when one of them changed.
Matching never restarts at the root of the whole term, an irreducible term is
traversed once, and a cascade of rewrites up a path does not revisit the
arguments at every level. -/
private def descend (rules : List (Equation s)) (again : Term s → Option (Term s × Bool))
    (after : Term s → Option (Term s)) : Term s → Option (Term s × Bool × Bool)
  | .var v =>
    match stepHere rules (.var v) with
    | some u => (again u).map fun p => (p.1,true,p.2)
    | none => some (.var v,false,true)
  | .atom a =>
    match stepHere rules (.atom a) with
    | some u => (again u).map fun p => (p.1,true,p.2)
    | none => some (.atom a,false,true)
  | .free f xs =>
    match stepHere rules (.free f xs) with
    | some u => (again u).map fun p => (p.1,true,p.2)
    | none =>
      let ys := List.ofFn fun i => descend rules again after (xs i)
      if ys.all Option.isSome then
        if ys.all fun y => y.elim false fun r => !r.2.1 && r.2.2 then some (.free f xs,false,true)
        else resettle rules after (.free f fun i => ((ys[i.val]?).getD none).elim (xs i) (·.1))
          (ys.all fun y => y.elim false (·.2.2))
      else none
  | .comm f a b =>
    match stepHere rules (.comm f a b) with
    | some u => (again u).map fun p => (p.1,true,p.2)
    | none =>
      match descend rules again after a, descend rules again after b with
      | some (x,p,sx), some (y,q,sy) =>
        if (!p && sx) && (!q && sy) then some (.comm f a b,false,true)
        else resettle rules after (.comm f x y) (sx && sy)
      | _, _ => none
  | .ac f a b =>
    match stepHere rules (.ac f a b) with
    | some u => (again u).map fun p => (p.1,true,p.2)
    | none =>
      match descend rules again after a, descend rules again after b with
      | some (x,p,sx), some (y,q,sy) =>
        if (!p && sx) && (!q && sy) then some (.ac f a b,false,true)
        else resettle rules after (.ac f x y) (sx && sy)
      | _, _ => none

/-- Local rewriting, with whether the result is known to be irreducible. -/
private def search (rules : List (Equation s)) : Nat → Term s → Option (Term s × Bool)
  | 0, _ => none
  | n+1, t => (descend rules (search rules n) (chain rules n) t).map fun r => (r.1,r.2.2)

/-- Normalization by local rewriting. When the local pass cannot vouch for its
result, the outermost path finishes from there: it confirms an irreducible
term in one traversal and otherwise keeps rewriting. The first argument bounds
the nesting of rewritten nodes and the length of each path. -/
def normalize (rules : List (Equation s)) (n : Nat) (t : Term s) : Option (Term s) :=
  match search rules n t with
  | some (u,true) => some u
  | some (u,false) => follow rules n u
  | none => none

omit [Interrupt] in
private theorem head_nil {α : Type} {xs : List α} (h : xs.head? = none) : xs = [] :=
  List.head?_eq_none_iff.mp h

/-- The one-step results found at a node itself. -/
private def atNode (rules : List (Equation s)) (t : Term s) : List (Term s) :=
  roots rules t ++ match t with
    | .ac f _ _ => extensions rules f t
    | _ => []

private theorem stepHere_eq (rules : List (Equation s)) (t : Term s) :
    stepHere rules t = (atNode rules t).head? := by
  cases t with
  | ac f a b =>
    simp only [stepHere, atNode, BagMatching.orLater_eq, rootF_eq, extensionF_eq, List.head?_append]
  | _ => simp [stepHere, atNode, BagMatching.orLater_eq, rootF_eq]

omit [Interrupt] in
private theorem atNode_steps (rules : List (Equation s)) {t w : Term s} (h : w ∈ atNode rules t) :
    w ∈ steps rules t := by
  cases t with
  | ac f a b =>
    rw [steps]
    rcases List.mem_append.mp h with r|e
    · exact List.mem_append_left _ r
    · exact List.mem_append_right _ (List.mem_append_left _ e)
  | _ =>
    rw [steps]
    rcases List.mem_append.mp h with r|e
    · exact List.mem_append_left _ r
    · exact (List.not_mem_nil e).elim

private theorem quiet {rules : List (Equation s)} {t : Term s} (h : stepHere rules t = none) :
    atNode rules t = [] :=
  head_nil (stepHere_eq rules t ▸ h)

private theorem fire {rules : List (Equation s)} (bound : Bound rules) {t w : Term s}
    (h : stepHere rules t = some w) : StepModulo (ruleRoot rules) t w :=
  (exactRaw rules bound t w).mp
    ⟨w,atNode_steps rules (List.mem_of_mem_head? (stepHere_eq rules t ▸ h)),.refl _⟩

private theorem follow_later {rules : List (Equation s)} (bound : Bound rules) :
    ∀ n t u, follow rules n t = some u → Reduces (ruleRoot rules) t u ∧ steps rules u = []
  | 0 => fun _ _ h => nomatch h
  | n+1 => by
    intro t u h
    rw [follow] at h
    split at h
    · next none_ =>
      cases h
      exact ⟨.basis (.refl _),head_nil (stepF_eq rules t ▸ none_)⟩
    · next v fired =>
      obtain ⟨more,normal⟩ := follow_later bound n v u h
      have member : v ∈ steps rules t := List.mem_of_mem_head? (stepF_eq rules t ▸ fired)
      exact ⟨(Reduces.step ((exactRaw rules bound t v).mp ⟨v,member,.refl _⟩)).trans more,normal⟩

private theorem chain_sound {rules : List (Equation s)} (bound : Bound rules) :
    ∀ n t u, chain rules n t = some u → Reduces (ruleRoot rules) t u
  | 0 => fun _ _ h => nomatch h
  | n+1 => by
    intro t u h
    rw [chain] at h
    split at h
    · cases h
      exact .basis (.refl _)
    · next v fired => exact (Reduces.step (fire bound fired)).trans (chain_sound bound n v u h)

/-- A sure result of `again` is irreducible. Every result is a reduct. -/
private abbrev Later (rules : List (Equation s)) (again : Term s → Option (Term s × Bool)) : Prop :=
  ∀ t u sure, again t = some (u,sure) → Reduces (ruleRoot rules) t u ∧ (sure = true → steps rules u = [])

/-- What a visit establishes: a reduct, irreducible when flagged as sure and
equal to the node when flagged as unchanged. -/
private abbrev Settled (rules : List (Equation s)) (t : Term s) (r : Term s × Bool × Bool) : Prop :=
  Reduces (ruleRoot rules) t r.1 ∧ (r.2.2 = true → steps rules r.1 = []) ∧ (r.2.1 = false → r.1 = t)

private theorem resettle_sound {rules : List (Equation s)} (bound : Bound rules)
    {after : Term s → Option (Term s)}
    (sound : ∀ a b, after a = some b → Reduces (ruleRoot rules) a b)
    {t t' : Term s} {sure : Bool} {r : Term s × Bool × Bool} (red : Reduces (ruleRoot rules) t t')
    (below : sure = true → steps rules t' = atNode rules t')
    (h : resettle rules after t' sure = some r) : Settled rules t r := by
  unfold resettle at h
  split at h
  · next none_ =>
    cases h
    exact ⟨red,fun ok => (below ok).trans (quiet none_),fun flag => nomatch flag⟩
  · next w fired =>
    obtain ⟨v,hv,rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨red.trans ((Reduces.step (fire bound fired)).trans (sound w v hv)),
      (fun flag => nomatch flag),fun flag => nomatch flag⟩

private theorem entry_sound {rules : List (Equation s)} (bound : Bound rules)
    {again : Term s → Option (Term s × Bool)} (later : Later rules again) {t w : Term s}
    {r : Term s × Bool × Bool} (fired : stepHere rules t = some w)
    (h : ((again w).map fun p => (p.1,true,p.2)) = some r) : Settled rules t r := by
  obtain ⟨p,hp,rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨red,normal⟩ := later w p.1 p.2 hp
  exact ⟨(Reduces.step (fire bound fired)).trans red,normal,fun flag => nomatch flag⟩

private theorem descend_sound {rules : List (Equation s)} (bound : Bound rules)
    {again : Term s → Option (Term s × Bool)} {after : Term s → Option (Term s)}
    (later : Later rules again) (sound : ∀ a b, after a = some b → Reduces (ruleRoot rules) a b)
    (t : Term s) (r : Term s × Bool × Bool) (h : descend rules again after t = some r) :
    Settled rules t r := by
  induction t generalizing r with
  | var v =>
    simp only [descend] at h
    split at h
    · next w fired => exact entry_sound bound later fired h
    · next none_ =>
      cases h
      exact ⟨.basis (.refl _),fun _ => by simpa [steps,atNode] using quiet none_,fun _ => rfl⟩
  | atom a =>
    simp only [descend] at h
    split at h
    · next w fired => exact entry_sound bound later fired h
    · next none_ =>
      cases h
      exact ⟨.basis (.refl _),fun _ => by simpa [steps,atNode] using quiet none_,fun _ => rfl⟩
  | free f xs ih =>
    simp only [descend] at h
    split at h
    · next w fired => exact entry_sound bound later fired h
    · next none_ =>
      have top : roots rules (.free f xs) = [] := by simpa [atNode] using quiet none_
      split at h
      · next all =>
        have child (i : Fin (s.arity f)) : ∃ y, descend rules again after (xs i) = some y ∧
            (((List.ofFn fun i => descend rules again after (xs i))[i.val]?).getD none).elim (xs i) (·.1) =
              y.1 := by
          have present := List.all_eq_true.mp all _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
          obtain ⟨y,hy⟩ := Option.isSome_iff_exists.mp present
          exact ⟨y,hy,by simp [hy]⟩
        split at h
        · next same =>
          cases h
          refine ⟨.basis (.refl _),fun _ => ?_,fun _ => rfl⟩
          rw [steps, top, List.nil_append]
          apply List.flatMap_eq_nil_iff.mpr
          intro i _
          obtain ⟨y,hy,_⟩ := child i
          have flag := List.all_eq_true.mp same _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
          rw [hy] at flag
          have both : y.2.1 = false ∧ y.2.2 = true := by simpa using flag
          obtain ⟨_,normal,here⟩ := ih i y hy
          rw [← here both.1, normal both.2]
          rfl
        · refine resettle_sound bound sound ?_ (fun sure => ?_) h
          · apply Reduces.free
            intro i
            obtain ⟨y,hy,pick⟩ := child i
            rw [pick]
            exact (ih i y hy).1
          · simp only [steps, atNode, List.append_nil]
            have none_ : ((List.finRange (s.arity f)).flatMap fun i =>
                (steps rules ((((List.ofFn fun i => descend rules again after (xs i))[i.val]?).getD none).elim
                  (xs i) (·.1))).map
                  fun u => Term.free f (fun j => if j = i then u else
                    (((List.ofFn fun i => descend rules again after (xs i))[j.val]?).getD none).elim
                      (xs j) (·.1))) = [] := by
              apply List.flatMap_eq_nil_iff.mpr
              intro i _
              obtain ⟨y,hy,pick⟩ := child i
              have flag := List.all_eq_true.mp sure _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
              rw [hy] at flag
              rw [pick, (ih i y hy).2.1 (by simpa using flag)]
              rfl
            rw [none_, List.append_nil]
      · contradiction
  | comm f a b ia ib =>
    simp only [descend] at h
    split at h
    · next w fired => exact entry_sound bound later fired h
    · next none_ =>
      have top : roots rules (.comm f a b) = [] := by simpa [atNode] using quiet none_
      split at h
      · next x p sx y q sy hx hy =>
        obtain ⟨ra,na,sa⟩ := ia _ hx
        obtain ⟨rb,nb,sb⟩ := ib _ hy
        split at h
        · next flags =>
          cases h
          have all : (p = false ∧ sx = true) ∧ q = false ∧ sy = true := by simpa using flags
          have ea : x = a := sa all.1.1
          have eb : y = b := sb all.2.1
          subst ea eb
          exact ⟨.basis (.refl _),fun _ => by simp [steps,top,na all.1.2,nb all.2.2],fun _ => rfl⟩
        · refine resettle_sound bound sound (.comm f ra rb) (fun sure => ?_) h
          have both : sx = true ∧ sy = true := by simpa using sure
          simp [steps,atNode,na both.1,nb both.2]
      · contradiction
  | ac f a b ia ib =>
    simp only [descend] at h
    split at h
    · next w fired => exact entry_sound bound later fired h
    · next none_ =>
      have top : atNode rules (.ac f a b) = [] := quiet none_
      split at h
      · next x p sx y q sy hx hy =>
        obtain ⟨ra,na,sa⟩ := ia _ hx
        obtain ⟨rb,nb,sb⟩ := ib _ hy
        split at h
        · next flags =>
          cases h
          have all : (p = false ∧ sx = true) ∧ q = false ∧ sy = true := by simpa using flags
          have ea : x = a := sa all.1.1
          have eb : y = b := sb all.2.1
          subst ea eb
          refine ⟨.basis (.refl _),fun _ => ?_,fun _ => rfl⟩
          have whole : steps rules (.ac f x y) = atNode rules (.ac f x y) := by
            simp [steps,atNode,na all.1.2,nb all.2.2]
          rw [whole, top]
        · refine resettle_sound bound sound (.ac f ra rb) (fun sure => ?_) h
          have both : sx = true ∧ sy = true := by simpa using sure
          simp [steps,atNode,na both.1,nb both.2]
      · contradiction

private theorem search_later {rules : List (Equation s)} (bound : Bound rules) :
    ∀ n, Later rules (search rules n)
  | 0 => fun _ _ _ h => nomatch h
  | n+1 => by
    intro t u sure h
    obtain ⟨r,hr,eq⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    obtain ⟨red,normal,_⟩ := descend_sound bound (search_later bound n) (chain_sound bound n) t r hr
    exact ⟨red,normal⟩

/-- Local normalization ends in an irreducible reduct of its input. No
property of the table beyond range restriction is used. -/
theorem normalize_sound {rules : List (Equation s)} (bound : Bound rules) (n : Nat) (t u : Term s)
    (h : normalize rules n t = some u) :
    Reduces (ruleRoot rules) t u ∧ Normal (ruleRoot rules) u := by
  have raw : Reduces (ruleRoot rules) t u ∧ steps rules u = [] := by
    unfold normalize at h
    split at h
    · next v found =>
      cases h
      obtain ⟨red,normal⟩ := search_later bound n t _ true found
      exact ⟨red,normal rfl⟩
    · next v found =>
      obtain ⟨red,_⟩ := search_later bound n t v false found
      obtain ⟨more,normal⟩ := follow_later bound n v u h
      exact ⟨red.trans more,normal⟩
    · contradiction
  obtain ⟨red,none_⟩ := raw
  refine ⟨red,fun w step => ?_⟩
  obtain ⟨v,hv,_⟩ := (exactRaw rules bound u w).mpr step
  rw [none_] at hv
  exact List.not_mem_nil hv

/-- The reference step finder needs no bound on the number or size of redexes.
Termination of the complete reducer is a separate property of the presentation. -/
def finder (rules : List (Equation s)) (bound : Bound rules) : StepFinder (ruleRoot rules) where
  next t := (successors rules t).head?
  stoppedAtNormal t stop u step := by
    obtain ⟨v,hv,_⟩ := (exactSteps rules bound t u).mpr step
    rw [List.head?_eq_none_iff.mp stop] at hv
    exact List.not_mem_nil hv
  step t u hit := (exactSteps rules bound t u).mp ⟨u,List.mem_of_mem_head? hit,.refl _⟩

def reducer (rules : List (Equation s)) (bound : Bound rules)
    (canonical : CanonicalPresentation (ruleRoot rules)) : VerifiedReducer (ruleRoot rules) :=
  reducerOfSteps canonical (finder rules bound)

end
end Tamarin.ReferenceReduction
