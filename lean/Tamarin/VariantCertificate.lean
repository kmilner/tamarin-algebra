import Tamarin.VariantFactoring

/-! Check a proposed family of variants instead of searching for one. Each
proposed substitution is completed with the normal forms of the instantiated
query. The family is accepted when every member is normal and either the
family is a product whose factors pass the closure test, or the family itself
passes it: some member subsumes the normalized query, and every normalized
one-step narrowing successor of a member is subsumed by a member. On a
canonical presentation an accepted family is a complete set of variants. -/
namespace Tamarin.VariantCertificate
open Rewriting VariantJoin MaudeOperations ReferenceVariantFrontier TupleNarrowingFrontier
variable {s : Signature} {n : Nat} {rules : List (Equation s)} {query : Fin n → Term s}
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

/-- The checker. `fuel` bounds the length of every rewrite path that is
followed; `work`, when nonzero, bounds the number of positions at which the
closure test looks for narrowing steps, added up over the members. -/
def check (rules : List (Equation s)) (q : List (Term s)) (family : List (Substitution s))
    (fuel work : Nat) : Verdict :=
  if hb : CheckedReduction.rangeBound rules then
    if hv : rules.all (fun r => CheckedVariants.nonvar r.lhs) then
      let bound := (CheckedReduction.rangeBound_iff rules).mp hb
      let vars := CheckedVariants.varsNormal rules hv
      let query := fun i : Fin q.length => q[i.val]
      match family.mapM (member rules query fuel) with
      | none => .exhausted
      | some members =>
        match members.findIdx? (fun p => !normalOn rules (keysOf query) p.assignment) with
        | some index => .rejected 1 index
        | none =>
          if factored rules bound vars query fuel work members then .accepted
          else saturated rules bound vars query fuel work members
    else .rejected 4 0
  else .rejected 4 0

/-- The members of an accepted family: one per proposed substitution, each
normal on the keys with normal forms as values, and together covering every
normal substitution. -/
theorem accepted_cover (canonical : CanonicalPresentation (ruleRoot rules)) {q : List (Term s)}
    {family : List (Substitution s)} {fuel work : Nat}
    (h : check rules q family fuel work = .accepted) :
    ∃ members : List (Point s q.length),
      family.mapM (member rules (fun i : Fin q.length => q[i.val]) fuel) = some members ∧
      Normalized (ruleRoot rules) Substitution.identity ∧
      (∀ p ∈ members, Formed rules (fun i : Fin q.length => q[i.val]) p) ∧
      ∀ ρ : Substitution s, Normalized (ruleRoot rules) ρ → ∀ out : Fin q.length → Term s,
        (∀ i, NormalForm (ruleRoot rules) (ρ.apply q[i.val]) (out i)) →
        ∃ p ∈ members, ∃ δ, Fits (p.row (keysOf (fun i : Fin q.length => q[i.val])))
          (fun i => ρ.image i.val) out δ := by
  unfold check at h
  split at h
  · next hb =>
    split at h
    · next hv =>
      dsimp only at h
      let bound := (CheckedReduction.rangeBound_iff rules).mp hb
      let vars := CheckedVariants.varsNormal rules hv
      let query := fun i : Fin q.length => q[i.val]
      let r := ReferenceReduction.reducer rules bound canonical
      split at h
      · contradiction
      · next members built =>
        split at h
        · contradiction
        · next normal =>
          have formed (p) (hp : p ∈ members) : Formed rules query p := by
            obtain ⟨σ,_,made⟩ := mapM_some_source _ built p hp
            obtain ⟨rfl,values⟩ := member_form made
            have none_ := List.findIdx?_eq_none_iff.mp normal p hp
            rw [normalOn_eq (query := query)] at none_
            exact ⟨(admissible_iff bound p).mp (by simpa using none_),
              fun i => follow_reduce bound canonical (values i) ▸ (r.correct _).normalForm⟩
          refine ⟨members,built,vars,formed,?_⟩
          split at h
          · next product => exact factored_hits bound canonical vars formed product
          · exact saturated_hits bound canonical vars formed h
    · contradiction
  · contradiction

/-- On a canonical presentation an accepted family is a complete set of
variants. Each returned variant carries the proposed substitution on the
variables of the query and the normal forms of the instantiated query. -/
theorem accepted_reply (canonical : CanonicalPresentation (ruleRoot rules)) {q : List (Term s)}
    {family : List (Substitution s)} {fuel work : Nat}
    (h : check rules q family fuel work = .accepted) :
    ∃ rows, VariantReply (ruleRoot rules) q [] rows ∧ rows.length = family.length ∧
      ∀ pair ∈ family.zip rows, ∀ v, Observed q v → pair.2.subst.image v = pair.1.image v := by
  obtain ⟨members,built,vars,formed,hits⟩ := accepted_cover canonical h
  let query := fun i : Fin q.length => q[i.val]
  let keys := keysOf query
  have bound : ReferenceReduction.Bound rules := by
    unfold check at h
    split at h
    · next hb => exact (CheckedReduction.rangeBound_iff rules).mp hb
    · contradiction
  let r := ReferenceReduction.reducer rules bound canonical
  have complete := VariantSaturation.complete_of_points vars members
    (fun p hp => sound_member vars p (formed p hp)) hits
  have reply : VariantReply (ruleRoot rules) (List.ofFn query) []
      (members.map (Point.answer · keys)) :=
    VariantReply.ofCanonical r vars complete (by
      intro a ha
      obtain ⟨p,_,rfl⟩ := List.mem_map.mp ha
      exact ⟨fun v hv => (p.answer keys).subst.outside v
        (fun hm => hv ((observed query v).mp hm)),by simp,by simp⟩)
  obtain ⟨len,each⟩ := mapM_some_zip _ built
  refine ⟨members.map (Point.answer · keys),
    by simpa only [query,List.ofFn_getElem] using reply,by simp [len],?_⟩
  rintro ⟨σ,a⟩ hpair v hv
  rw [List.zip_map_right] at hpair
  obtain ⟨⟨σ',p⟩,hzip,eq⟩ := List.mem_map.mp hpair
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
  have at_p := (member_form (each _ hzip)).1
  have live : Observed (List.ofFn query) v := by simpa only [query,List.ofFn_getElem] using hv
  have key : v ∈ keys := (observed query v).mpr live
  change ((p.row keys).project (fun k => p.assignment.sorted k.val)).image v = _
  rw [(p.row keys).project_key (fun k => p.assignment.sorted k.val) ⟨v,key⟩]
  exact congrArg (fun τ : Substitution s => τ.image v) at_p

end Tamarin.VariantCertificate
