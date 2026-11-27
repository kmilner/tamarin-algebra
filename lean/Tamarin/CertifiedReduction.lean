import Tamarin.CertifiedTableWire
import Tamarin.CheckedReductionPacket

namespace Tamarin.GeneralReductionWire

/-- The certifier checks the ambient signature; the staged reducer executes in
the query dictionary. A hit makes the table canonical in the query dictionary
too, and every depth beyond the height of the rewrite tree of an observation
then returns its normal form, including names not appearing in the rules. -/
theorem Correct.completes_certified {kernel : CheckedReductionWire.Kernel} (ok : Correct kernel)
    {check} (spec : CertifiedTableWire.Correct check) {ds ns es root d t rs budget}
    (decoded : TableWire.input ds ns es #[root] = some ⟨d,rs,[t]⟩) (hit : check ds ns es budget = true) :
    ∃ (bound : ReferenceReduction.Bound rs)
      (can : MaudeOperations.CanonicalPresentation (Rewriting.ruleRoot rs)), ∀ n : UInt64,
      ReductionHeight.height bound can.terminating t < n.toNat →
      Answer d rs t (kernel ds ns es root n) := by
  obtain ⟨scope,can,_⟩ := CertifiedTableWire.sound spec decoded hit
  obtain ⟨bound,localCan⟩ := SignatureExtension.reflect_canonical TableAmbient.atoms rs scope can
  exact ⟨bound,localCan,fun n enough => ok.completes decoded bound localCan n enough⟩

end Tamarin.GeneralReductionWire
