import Tamarin.SessionTableWire
import Tamarin.VariantClosed

/-! Which families the exported variant checkers accept. On a canonical
presentation a family accepted with status 1 is closed. A reply with status 2
names a clause of closedness that fails, and the member that violates it when
the clause concerns one member. A reply with status 3 is given only when a
term the check has to normalize has a rewrite path as long as the depth, or
when the work limit is below the positions of the narrowing layers. On a
range-restricted canonical presentation those terms have bounded rewrite
paths, so there is a depth from which a call without a work limit never
replies with status 3 and accepts every closed family. -/
namespace Tamarin.VariantCheckWire
open Rewriting MaudeOperations VariantCertificate
variable [Interrupt]

/-- The replies of a checker on one table, query and family, as a function
of the depth and the work limit. -/
structure Decision {s : Signature} (rules : List (Equation s)) (q : List (Term s))
    (family : List (Substitution s)) (reply : UInt64 → UInt64 → Array (Array UInt64)) : Prop where
  closed : ∀ fuel work, CanonicalPresentation (ruleRoot rules) → reply fuel work = #[#[1]] →
    Closed (ruleRoot rules) q family
  accepts : ReferenceReduction.Bound rules → CanonicalPresentation (ruleRoot rules) →
    ∃ k : Nat, ∀ fuel : UInt64, k ≤ fuel.toNat → reply fuel 0 ≠ #[#[3]] ∧
      (Closed (ruleRoot rules) q family → reply fuel 0 = #[#[1]])
  exhausts : ∀ fuel work, CanonicalPresentation (ruleRoot rules) → reply fuel work = #[#[3]] →
    (∃ t, Demand (ruleRoot rules) q family t ∧ ¬CheckedReduction.Within rules fuel.toNat t) ∨
      (work ≠ 0 ∧ Overcharged (ruleRoot rules) q family work.toNat)
  rejects : ∀ fuel work reason index, CanonicalPresentation (ruleRoot rules) →
    reply fuel work = #[#[2,reason,index]] → ∃ i : Nat, index = UInt64.ofNat i ∧
      ((reason = 1 ∧ ∃ σ, family[i]? = some σ ∧ ¬NormalMember (ruleRoot rules) q σ) ∨
        (reason = 2 ∧ ¬Starts (ruleRoot rules) q family) ∨
        (reason = 3 ∧ ∃ σ, family[i]? = some σ ∧ ¬Folds (ruleRoot rules) q family σ) ∨
        (reason = 4 ∧ ¬(ReferenceReduction.Bound rules ∧ ∀ r ∈ rules, ∀ v, r.lhs ≠ .var v)))

omit [Interrupt] in
theorem reply_exhausted {v : Verdict} (h : reply v = #[#[3]]) : v = .exhausted := by
  cases v with
  | accepted => simp [reply] at h
  | rejected reason index => simp [reply] at h
  | exhausted => rfl

omit [Interrupt] in
theorem reply_rejected {v : Verdict} {reason index : UInt64} (h : reply v = #[#[2,reason,index]]) :
    ∃ r i, v = .rejected r i ∧ reason = UInt64.ofNat r ∧ index = UInt64.ofNat i := by
  cases v with
  | accepted => simp [reply] at h
  | rejected r i =>
    simp [reply] at h
    exact ⟨r,i,rfl,h.1.symm,h.2.symm⟩
  | exhausted => simp [reply] at h

theorem decision {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym]
    [DecidableEq s.Atom] (rules : List (Equation s)) (q : List (Term s))
    (family : List (Substitution s)) :
    Decision rules q family fun fuel work => reply (check rules q family fuel.toNat work.toNat) where
  closed := fun _ _ canonical ok => accepted_closed canonical (reply_accepted ok)
  accepts := by
    intro bound canonical
    obtain ⟨k,enough⟩ := decides bound canonical q family
    refine ⟨k,fun fuel large => ⟨fun out => (enough fuel.toNat large).1 (reply_exhausted out),
      fun closed => ?_⟩⟩
    change reply (check rules q family fuel.toNat 0) = _
    rw [(enough fuel.toNat large).2.mpr closed]
    rfl
  exhausts := by
    intro fuel work canonical out
    rcases exhausted_cases canonical (reply_exhausted out) with long | ⟨limited,short⟩
    · exact .inl long
    · exact .inr ⟨fun zero => limited (by rw [zero]; rfl),short⟩
  rejects := by
    intro fuel work reason index canonical out
    obtain ⟨r,i,verdict,rfl,rfl⟩ := reply_rejected out
    refine ⟨i,rfl,?_⟩
    rcases rejected_cases canonical verdict with ⟨rfl,h⟩ | ⟨rfl,h⟩ | ⟨rfl,h⟩ | ⟨rfl,h⟩
    · exact .inl ⟨rfl,h⟩
    · exact .inr (.inl ⟨rfl,h⟩)
    · exact .inr (.inr (.inl ⟨rfl,h⟩))
    · exact .inr (.inr (.inr ⟨rfl,h⟩))

/-- The replies of the packet checker decide closedness of the decoded
family over all ambient names. -/
def Decides (kernel : Kernel) : Prop :=
  ∀ ds ns es roots family d rs q members, input ds ns es roots family = some ⟨d,rs,q,members⟩ →
    Decision (TableAmbient.liftRules rs) (q.map TableAmbient.liftTerm)
      (members.map (SignatureExtension.liftSubst TableAmbient.atoms))
      fun fuel work => kernel ds ns es roots family fuel work

theorem decides : Decides run := by
  intro ds ns es roots family d rs q members decoded
  have same : (fun fuel work => run ds ns es roots family fuel work) = fun fuel work =>
      reply (check (TableAmbient.liftRules rs) (q.map TableAmbient.liftTerm)
        (members.map (SignatureExtension.liftSubst TableAmbient.atoms)) fuel.toNat work.toNat) := by
    funext fuel work
    simp only [run,decoded]
  rw [same]
  exact decision _ _ _

end Tamarin.VariantCheckWire

namespace Tamarin.SessionVariantCheckWire
open Rewriting MaudeOperations VariantCertificate TableAmbient
variable [Interrupt]

/-- The replies of the session checker decide closedness of the family that
the further rows denote. -/
def Decides (kernel : Kernel) : Prop :=
  ∀ ds ns es extra roots family d rs q members,
    input ds ns es extra roots family = some ⟨d,rs,q,members⟩ →
    VariantCheckWire.Decision (liftRules rs) q members
      fun fuel work => kernel ds ns es extra roots family fuel work

theorem decides : Decides run := by
  intro ds ns es extra roots family d rs q members decoded
  have same : (fun fuel work => run ds ns es extra roots family fuel work) = fun fuel work =>
      VariantCheckWire.reply (check (liftRules rs) q members fuel.toNat work.toNat) := by
    funext fuel work
    simp only [run,decoded]
  rw [same]
  exact VariantCheckWire.decision _ _ _

end Tamarin.SessionVariantCheckWire
