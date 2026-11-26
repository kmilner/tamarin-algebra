import Tamarin.MaudeUnifySolvedFormProofs

/-!
# The solved-form steps

Soundness, completeness and well-formedness of `csf` (Maude's
`computeSolvedForm`) and of the functions it calls. Every statement holds
for all ranks `r` and all fuel `k`.
-/
namespace Tamarin.MaudeUnify
open Cancellation

variable {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]
variable (r : Ranks s)

/-- Well-formedness: a successful step keeps the state bounded and only adds slots. -/
theorem csf_wf (k : Nat) {st st' : St s} {l rt : Dag s} (b : Bounded st)
    (hl : l.Fit st.vals.size) (hr : rt.Fit st.vals.size) (h : csf r k st l rt = .ok st') :
    Bounded st' ∧ Grows st st' :=
  ⟨(wfK r k).csf b hl hr h, ((extK r k).csf h).1, fun i _ => ((extK r k).csf h).2 i⟩

/-- Soundness: a valuation of the result models the start and solves the equation. -/
theorem csf_sound (k : Nat) {st st' : St s} {l rt : Dag s} (b : Bounded st)
    (hl : l.Fit st.vals.size) (hr : rt.Fit st.vals.size) (h : csf r k st l rt = .ok st')
    {ρ : Nat → Term s} (m : Models st' ρ) :
    Models st ρ ∧ EquivB (Dag.eval ρ l) (Dag.eval ρ rt) :=
  (soundK r k).csf b hl hr h m

/-- Completeness: a model of the start that solves the equation extends to a
model of the result; the step does not fail. -/
theorem csf_complete (k : Nat) {st : St s} {l rt : Dag s} (b : Bounded st)
    (hl : l.Fit st.vals.size) (hr : rt.Fit st.vals.size) {ρ : Nat → Term s} (m : Models st ρ)
    (e : EquivB (Dag.eval ρ l) (Dag.eval ρ rt)) :
    Promise st ρ (csf r k st l rt) :=
  promise_iff.mpr ((compK r k).csf b hl hr m e)

/-- Sorts only grow by `none` entries, which `St.sortOf` also reads out of bounds. -/
theorem csf_sorts (k : Nat) {st st' : St s} {l rt : Dag s} (h : csf r k st l rt = .ok st') :
    ∀ i, st'.sortOf i = st.sortOf i :=
  ((extK r k).csf h).2

end Tamarin.MaudeUnify
