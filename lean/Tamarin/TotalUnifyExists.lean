import Tamarin.TotalUnifyWire

/-! The decision entry point for ordinary unification. It reads the packet of
the listing entry point and replies with one byte. -/
namespace Tamarin.TotalUnifyWire

abbrev Decision := Array UInt64 → Array (Array UInt64) → Array UInt64 → UInt8

variable [Interrupt]

/-- 1: a unifier exists; 2: none exists; 0: malformed packet. -/
def runExists (decls : Array UInt64) (nodes : Array (Array UInt64)) (roots : Array UInt64) : UInt8 :=
  match input decls nodes roots with
  | none => 0
  | some ⟨d,p⟩ => if UnifyExists.decide (s := d.sig) p then 1 else 2

/-- The decision entry point reports exactly whether a unifier exists. -/
structure ExistsCorrect (kernel : Decision) : Prop where
  malformed : ∀ ds ns es, input ds ns es = none → kernel ds ns es = 0
  valid : ∀ ds ns es d p, input ds ns es = some ⟨d,p⟩ →
    (kernel ds ns es = 1 ∧ ∃ σ, p.Solves σ) ∨ (kernel ds ns es = 2 ∧ ¬ ∃ σ, p.Solves σ)

theorem existsCorrect : ExistsCorrect runExists where
  malformed := fun ds ns es h => by simp [runExists,h]
  valid := by
    intro ds ns es d p hi
    cases verdict : UnifyExists.decide (s := d.sig) p with
    | true => exact .inl ⟨by simp [runExists,hi,verdict],(UnifyExists.decide_iff p).mp verdict⟩
    | false =>
      refine .inr ⟨by simp [runExists,hi,verdict],fun yes => ?_⟩
      have := (UnifyExists.decide_iff p).mpr yes
      rw [verdict] at this
      cases this

end Tamarin.TotalUnifyWire
