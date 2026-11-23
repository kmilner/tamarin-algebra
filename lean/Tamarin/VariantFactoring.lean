import Tamarin.VariantClosure

/-! A family that is a product. The slots of a query are split into groups.
Each group has a list of representative members that passes the closure test
on the slots of the group alone. For every choice of one representative per
group, some member of the family restricts on each group to a row that
subsumes the chosen representative, and the variables it shares between two
groups are images of keys common to both. Every normal substitution is then
an instance of a member of the family: the instances found group by group
agree on the shared variables, so they join into one.

How the groups and their representatives are chosen is not part of any proof.
A family for which the choice fails is checked by the closure test on all of
its members. -/
namespace Tamarin.VariantCertificate
open Rewriting VariantJoin MaudeOperations ReferenceVariantFrontier TupleNarrowingFrontier
variable {s : Signature} {n : Nat} {rules : List (Equation s)} {query : Fin n → Term s}

/-- The slots of a group, the keys of those slots, and its representatives.
`shapes` lists the representatives up to renaming and is only used to find
the member for a choice. -/
structure Group (s : Signature) (n : Nat) where
  slots : List (Fin n)
  keys : List Variable
  reps : List (Point s n)
  shapes : List (List (Term s))

/-- The query on the slots of a group. -/
def restrict (query : Fin n → Term s) (slots : List (Fin n)) : Fin slots.length → Term s :=
  fun i => query slots[i]

/-- The point on the slots of a group. -/
def pick (p : Point s n) (slots : List (Fin n)) : Point s slots.length :=
  ⟨p.assignment,fun i => p.value slots[i]⟩

theorem keys_restrict {slots : List (Fin n)} {v : Variable} (h : v ∈ keysOf (restrict query slots)) :
    v ∈ keysOf query := by
  obtain ⟨t,ht,occ⟩ := (observed _ v).mp h
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
  exact (observed query v).mpr ⟨_,List.mem_ofFn.mpr ⟨slots[i],rfl⟩,occ⟩

theorem keys_slot {slots : List (Fin n)} {i : Fin n} (hi : i ∈ slots) {v : Variable}
    (occ : (query i).Occurs v) : v ∈ keysOf (restrict query slots) := by
  obtain ⟨k,hk,rfl⟩ := List.getElem_of_mem hi
  exact (observed _ v).mpr ⟨_,List.mem_ofFn.mpr ⟨⟨k,hk⟩,rfl⟩,occ⟩

theorem formed_pick {p : Point s n} (formed : Formed rules query p) (slots : List (Fin n)) :
    Formed rules (restrict query slots) (pick p slots) :=
  ⟨fun i => formed.1 ⟨i.val,keys_restrict i.property⟩,fun i => formed.2 slots[i]⟩

section
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

/-- Whether one substitution turns the first list into the second, by a
guessed substitution or else by the complete matcher. -/
def matched (general specific : List (Term s)) : Bool :=
  guessedInstance general specific || instanceOf general specific

theorem matched_sound {keys : List Variable} {g t : Point s n}
    (h : matched (terms keys g) (terms keys t) = true) : (g.row keys).Subsumes (t.row keys) := by
  rcases Bool.or_eq_true_iff.mp h with quick | slow
  · exact guessedInstance_sound quick
  · exact instanceOf_sound slow

/-- Every variable of the terms that was seen in an earlier group is the
image of a key of this group that is also a key of an earlier group. -/
def pinned (keys seenKeys seenVars : List Variable) (m : Point s n) (mine : List (Term s)) : Bool :=
  (mine.flatMap Term.variables).all fun w =>
    !seenVars.contains w ||
      keys.any fun v => seenKeys.contains v && decide (m.assignment.image v = .var w)

/-- The member restricts on every group to a row that subsumes the chosen
representative, and shares between groups only images of common keys. -/
def joins (m : Point s n) : List (Group s n × Point s n) → List Variable → List Variable → Bool
  | [], _, _ => true
  | (g,rep) :: rest, seenKeys, seenVars =>
    let mine := terms g.keys (pick m g.slots)
    matched mine (terms g.keys (pick rep g.slots)) && pinned g.keys seenKeys seenVars m mine &&
      joins m rest (g.keys ++ seenKeys) (mine.flatMap Term.variables ++ seenVars)

/-- The instances found for the chosen representatives join into one
instance of the member. -/
theorem joins_fits {m : Point s n} {ρ : Substitution s} {out : Fin n → Term s}
    (pairs : List (Group s n × Point s n)) (seenKeys seenVars : List Variable) (δ0 : Substitution s)
    (ok : joins m pairs seenKeys seenVars = true)
    (each : ∀ e ∈ pairs, ∃ δ, Fits ((pick e.2 e.1.slots).row e.1.keys)
      (fun k => ρ.image k.val) (fun i => out e.1.slots[i]) δ)
    (tracked : ∀ v ∈ seenKeys, ∀ w, (m.assignment.image v).Occurs w → w ∈ seenVars)
    (inputs : ∀ v ∈ seenKeys, EquivB (ρ.image v) (δ0.apply (m.assignment.image v))) :
    ∃ δ : Substitution s, (∀ w ∈ seenVars, δ.image w = δ0.image w) ∧
      ∀ e ∈ pairs, (∀ v ∈ e.1.keys, EquivB (ρ.image v) (δ.apply (m.assignment.image v))) ∧
        ∀ i ∈ e.1.slots, EquivB (out i) (δ.apply (m.value i)) := by
  induction pairs generalizing seenKeys seenVars δ0 with
  | nil => exact ⟨δ0,fun _ _ => rfl,fun _ h => nomatch h⟩
  | cons e rest ih =>
    obtain ⟨g,rep⟩ := e
    simp only [joins,Bool.and_eq_true] at ok
    obtain ⟨⟨inst,pin⟩,later⟩ := ok
    let mine := terms g.keys (pick m g.slots)
    obtain ⟨θ,sub⟩ := matched_sound inst
    obtain ⟨δg,fit⟩ := each (g,rep) List.mem_cons_self
    let η := δg.compose θ
    have hin (v) (hv : v ∈ g.keys) : EquivB (ρ.image v) (η.apply (m.assignment.image v)) := by
      rw [Substitution.apply_compose]
      exact (fit.inputs ⟨v,hv⟩).trans ((sub.inputs ⟨v,hv⟩).subst δg.image)
    have hval (i : Fin g.slots.length) : EquivB (out g.slots[i]) (η.apply (m.value g.slots[i])) := by
      rw [Substitution.apply_compose]
      exact (fit.values i).trans ((sub.values i).subst δg.image)
    let δ1 := VariantJoin.choose (· ∈ seenVars) δ0 η
    have image (w : Variable) : δ1.image w = if w ∈ seenVars then δ0.image w else η.image w := by
      simp [δ1,VariantJoin.choose]
    have agree (t : Term s) (ht : t ∈ mine) : EquivB (δ1.apply t) (η.apply t) := by
      apply t.subst_equiv
      intro w hw
      rw [image]
      split
      · next seen =>
        have here := List.all_eq_true.mp pin w (List.mem_flatMap.mpr ⟨t,ht,(t.mem_variables w).mpr hw⟩)
        simp only [List.contains_eq_mem,seen,decide_true,Bool.not_true,Bool.false_or,
          List.any_eq_true,Bool.and_eq_true,decide_eq_true_eq] at here
        obtain ⟨v,hv,hs,eq⟩ := here
        have a := inputs v hs
        have b := hin v hv
        rw [eq] at a b
        exact a.symm.trans b
      · exact .refl _
    have key_mine (v) (hv : v ∈ g.keys) : m.assignment.image v ∈ mine :=
      List.mem_append_left _ (List.mem_map_of_mem (f := m.assignment.image) hv)
    have slot_mine (i : Fin g.slots.length) : m.value g.slots[i] ∈ mine :=
      List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    have tracked' : ∀ v ∈ g.keys ++ seenKeys, ∀ w, (m.assignment.image v).Occurs w →
        w ∈ mine.flatMap Term.variables ++ seenVars := by
      intro v hv w hw
      rcases List.mem_append.mp hv with new | old
      · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨_,key_mine v new,(Term.mem_variables _ w).mpr hw⟩)
      · exact List.mem_append_right _ (tracked v old w hw)
    have inputs' : ∀ v ∈ g.keys ++ seenKeys, EquivB (ρ.image v) (δ1.apply (m.assignment.image v)) := by
      intro v hv
      rcases List.mem_append.mp hv with new | old
      · exact (hin v new).trans (agree _ (key_mine v new)).symm
      · rw [(VariantJoin.choose_apply (· ∈ seenVars) δ0 η _).1 (tracked v old)]
        exact inputs v old
    obtain ⟨δ,same,others⟩ := ih (g.keys ++ seenKeys) (mine.flatMap Term.variables ++ seenVars) δ1
      later (fun e he => each e (List.mem_cons_of_mem _ he)) tracked' inputs'
    have kept (t : Term s) (ht : t ∈ mine) : δ.apply t = δ1.apply t :=
      Term.subst_eq_of_agree _ _ t fun w hw =>
        same w (List.mem_append_left _ (List.mem_flatMap.mpr ⟨t,ht,(t.mem_variables w).mpr hw⟩))
    refine ⟨δ,fun w hw => ?_,fun e he => ?_⟩
    · simp [same w (List.mem_append_right _ hw),image,hw]
    · rcases List.mem_cons.mp he with rfl | tail
      · refine ⟨fun v hv => ?_,fun i hi => ?_⟩
        · rw [kept _ (key_mine v hv)]
          exact (hin v hv).trans (agree _ (key_mine v hv)).symm
        · obtain ⟨k,hk,rfl⟩ := List.getElem_of_mem hi
          have moved := kept _ (slot_mine ⟨k,hk⟩)
          have fit := (hval ⟨k,hk⟩).trans (agree _ (slot_mine ⟨k,hk⟩)).symm
          exact moved ▸ fit
      · exact others e tail

/-- The terms with their variables numbered in order of first occurrence. -/
def canon (ts : List (Term s)) : List (Term s) :=
  let vs := (ts.flatMap Term.variables).eraseDups
  ts.map fun t => t.subst fun v => .var ⟨vs.idxOf v,v.sort⟩

/-- The shape of a point on a group: its terms up to renaming. -/
def shape (g : Group s n) (p : Point s n) : List (Term s) :=
  canon (terms g.keys (pick p g.slots))

def codes (shapes : List (List (Term s))) : UInt64 :=
  shapes.foldl (fun h ts => ts.foldl (fun h t => mixHash h (code t)) (mixHash h 7)) 11

/-- The members with their shapes on the groups, for finding the member of a
choice. -/
abbrev Index (s : Signature) (n : Nat) := List (UInt64 × List (List (Term s)) × Point s n)

/-- For every choice of one representative per group, the member listed for
the shapes of the choice joins the chosen representatives. -/
def allJoined (index : Index s n) : List (Group s n) → List (Group s n × Point s n) → Bool
  | [], acc =>
    let wanted := acc.map fun e => shape e.1 e.2
    let number := codes wanted
    match index.find? fun e => e.1 == number && e.2.1 == wanted with
    | some e => joins e.2.2 acc [] []
    | none => false
  | g :: gs, acc => g.reps.all fun rep => allJoined index gs ((g,rep) :: acc)

theorem allJoined_spec {members : List (Point s n)} {index : Index s n}
    (inside : ∀ e ∈ index, e.2.2 ∈ members) (R : Group s n → Point s n → Prop)
    (gs : List (Group s n)) (acc : List (Group s n × Point s n))
    (h : allJoined index gs acc = true) (found : ∀ g ∈ gs, ∃ rep ∈ g.reps, R g rep)
    (before : ∀ e ∈ acc, R e.1 e.2) :
    ∃ pairs m, m ∈ members ∧ joins m pairs [] [] = true ∧ (∀ e ∈ pairs, R e.1 e.2) ∧
      (∀ g ∈ gs, ∃ e ∈ pairs, e.1 = g) ∧ ∀ e ∈ acc, e ∈ pairs := by
  induction gs generalizing acc with
  | nil =>
    unfold allJoined at h
    dsimp only at h
    split at h
    · next e hit =>
      refine ⟨acc,e.2.2,inside e (List.mem_of_find?_eq_some hit),h,before,?_,fun _ he => he⟩
      intro g hg
      cases hg
    · contradiction
  | cons g gs ih =>
    obtain ⟨rep,hrep,ok⟩ := found g List.mem_cons_self
    have next := List.all_eq_true.mp h rep hrep
    obtain ⟨pairs,m,hm,joined,all,cover,kept⟩ := ih ((g,rep) :: acc) next
      (fun g' hg' => found g' (List.mem_cons_of_mem _ hg'))
      (fun e he => by
        rcases List.mem_cons.mp he with rfl | old
        · exact ok
        · exact before e old)
    refine ⟨pairs,m,hm,joined,all,fun g' hg' => ?_,fun e he => kept e (List.mem_cons_of_mem _ he)⟩
    rcases List.mem_cons.mp hg' with rfl | later
    · exact ⟨_,kept _ List.mem_cons_self,rfl⟩
    · exact cover g' later

/-- A proposed split: the slots of each group and the positions of its
representatives in the list of members. -/
structure Plan (n : Nat) where
  slots : List (Fin n)
  reps : List Nat

def isVariable : Term s → Bool
  | .var _ => true
  | _ => false

/-- The position of the first occurrence of each distinct entry. -/
def firsts {α : Type} [BEq α] (xs : List α) : List Nat :=
  ((xs.zipIdx.foldl (fun (acc : List α × List Nat) e =>
    if acc.1.contains e.1 then acc else (e.1 :: acc.1,e.2 :: acc.2)) ([],[])).2).reverse

/-- Propose a split. A key is fixed when every member sends it to a variable.
Slots that share a key that is not fixed go to one group. A slot with fixed
keys only goes to the first group whose keys include every fixed key that
some member identifies with one of its own, and otherwise to one last group.
The representatives of a group are the first members of each shape. -/
def split (query : Fin n → Term s) (keys : List Variable) (members : List (Point s n)) : List (Plan n) :=
  let fixed := keys.filter fun v => members.all fun m => isVariable (m.assignment.image v)
  let tied (v : Variable) := fixed.filter fun u =>
    u != v && members.any fun m => decide (m.assignment.image u = m.assignment.image v)
  let loose (i : Fin n) := (query i).variables.filter fun v => !fixed.contains v
  let merged : List (List (Fin n) × List Variable) := (List.finRange n).foldl (fun acc i =>
    let vs := loose i
    let (hit,miss) := acc.partition fun g => g.2.any vs.contains
    (hit.flatMap (·.1) ++ [i],vs ++ hit.flatMap (·.2)) :: miss) []
  let (still,moving) := merged.partition fun g => g.2.isEmpty
  let moving := moving.reverse.map fun g => (g.1,keysOf (restrict query g.1))
  let placed := (still.reverse.flatMap (·.1)).map fun i =>
    let own := (query i).variables.filter fun v => !(tied v).isEmpty
    let needed := own ++ own.flatMap tied
    (i,if needed.isEmpty then none else moving.findIdx? fun g => needed.all g.2.contains)
  let grown := moving.zipIdx.map fun (g,k) =>
    g.1 ++ (placed.filter fun e => e.2 == some k).map (·.1)
  let rest := (placed.filter fun e => e.2.isNone).map (·.1)
  let slotLists := grown ++ (if rest.isEmpty then [] else [rest])
  slotLists.map fun slots =>
    let ks := keysOf (restrict query slots)
    ⟨slots,firsts (members.map fun m => canon (terms ks (pick m slots)))⟩

/-- The groups of a plan, with representatives taken from the members. -/
def resolve (query : Fin n → Term s) (members : List (Point s n)) (plans : List (Plan n)) :
    List (Group s n) :=
  let table := members.toArray
  plans.map fun plan =>
    let keys := keysOf (restrict query plan.slots)
    let reps := plan.reps.filterMap fun i => table[i]?
    ⟨plan.slots,keys,reps,reps.map fun p => canon (terms keys (pick p plan.slots))⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem resolve_spec {members : List (Point s n)} {plans : List (Plan n)} {g : Group s n}
    (h : g ∈ resolve query members plans) :
    g.keys = keysOf (restrict query g.slots) ∧ ∀ p ∈ g.reps, p ∈ members := by
  obtain ⟨plan,_,rfl⟩ := List.mem_map.mp h
  refine ⟨rfl,fun p hp => ?_⟩
  obtain ⟨i,_,hit⟩ := List.mem_filterMap.mp hp
  simpa using Array.mem_of_getElem? hit

def accepted : Verdict → Bool
  | .accepted => true
  | _ => false

/-- The family is a product of at least two groups, each group passes the
closure test on its representatives, and every choice of representatives is
joined by a member. -/
def factored (rules : List (Equation s)) (bound : ReferenceReduction.Bound rules)
    (vars : Normalized (ruleRoot rules) Substitution.identity) (query : Fin n → Term s)
    (fuel work : Nat) (members : List (Point s n)) : Bool :=
  let groups := resolve query members (split query (keysOf query) members)
  let index : Index s n := members.map fun m =>
    let shapes := groups.reverse.map fun g => shape g m
    (codes shapes,shapes,m)
  decide (1 < groups.length) &&
    (groups.all fun g => decide (g.reps.length < members.length)) &&
    ((List.finRange n).all fun i => groups.any fun g => g.slots.contains i) &&
    (groups.all fun g => accepted (saturated rules bound vars (restrict query g.slots) fuel work
      (g.reps.map (pick · g.slots)))) &&
    allJoined index groups []

/-- On a canonical presentation the members of a product cover every normal
substitution. -/
theorem factored_hits (bound : ReferenceReduction.Bound rules)
    (canonical : CanonicalPresentation (ruleRoot rules))
    (vars : Normalized (ruleRoot rules) Substitution.identity) {fuel work : Nat}
    {members : List (Point s n)} (formed : ∀ p ∈ members, Formed rules query p)
    (h : factored rules bound vars query fuel work members = true)
    (ρ : Substitution s) (norm : Normalized (ruleRoot rules) ρ) (out : Fin n → Term s)
    (forms : ∀ i, NormalForm (ruleRoot rules) (ρ.apply (query i)) (out i)) :
    ∃ p, p ∈ members ∧ ∃ δ, Fits (p.row (keysOf query)) (fun i => ρ.image i.val) out δ := by
  unfold factored at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨_,_⟩,cover⟩,each⟩,joined⟩ := h
  let groups := resolve query members (split query (keysOf query) members)
  let R (g : Group s n) (rep : Point s n) : Prop :=
    ∃ δ, Fits ((pick rep g.slots).row g.keys) (fun k => ρ.image k.val) (fun i => out g.slots[i]) δ
  have found (g) (hg : g ∈ groups) : ∃ rep ∈ g.reps, R g rep := by
    obtain ⟨keys_eq,inside⟩ := resolve_spec hg
    have ok := List.all_eq_true.mp each g hg
    have pass : saturated rules bound vars (restrict query g.slots) fuel work
        (g.reps.map (pick · g.slots)) = .accepted := by
      revert ok
      cases saturated rules bound vars (restrict query g.slots) fuel work (g.reps.map (pick · g.slots)) <;>
        simp [accepted]
    obtain ⟨p,hp,δ,fit⟩ := saturated_hits bound canonical vars
      (fun p hp => by
        obtain ⟨rep,hrep,rfl⟩ := List.mem_map.mp hp
        exact formed_pick (formed rep (inside rep hrep)) g.slots)
      pass ρ norm (fun i => out g.slots[i]) (fun i => forms g.slots[i])
    obtain ⟨rep,hrep,rfl⟩ := List.mem_map.mp hp
    exact ⟨rep,hrep,δ,keys_eq ▸ fit⟩
  obtain ⟨pairs,m,hm,joint,all,covered_,_⟩ := allJoined_spec (members := members)
    (fun e he => by
      obtain ⟨m,hm,rfl⟩ := List.mem_map.mp he
      exact hm) R groups [] joined found (fun _ he => nomatch he)
  obtain ⟨δ,_,fits⟩ := joins_fits pairs [] [] Substitution.identity joint all
    (fun _ hv => nomatch hv) (fun _ hv => nomatch hv)
  have slot (i : Fin n) : ∃ e ∈ pairs, i ∈ e.1.slots ∧ e.1.keys = keysOf (restrict query e.1.slots) := by
    obtain ⟨g,hg,has⟩ := List.any_eq_true.mp (List.all_eq_true.mp cover i (List.mem_finRange i))
    obtain ⟨e,he,rfl⟩ := covered_ g hg
    exact ⟨e,he,by simpa using has,(resolve_spec hg).1⟩
  refine ⟨m,hm,δ,fun k => ?_,fun i => ?_⟩
  · obtain ⟨t,ht,occ⟩ := (observed query k.val).mp k.property
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
    obtain ⟨e,he,hi,keys_eq⟩ := slot i
    exact (fits e he).1 k.val (keys_eq ▸ keys_slot hi occ)
  · obtain ⟨e,he,hi,_⟩ := slot i
    exact (fits e he).2 i hi

end
end Tamarin.VariantCertificate
