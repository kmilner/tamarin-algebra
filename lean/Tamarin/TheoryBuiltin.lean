import Tamarin.Theory
import Tamarin.CertifiedTableWire

/-! Every combination of builtins without user symbols or rules is certified
at every budget: each of the 24 valid tables is accepted at budget zero by
components that claim all of its rows (kernel evaluation), and such a table is
accepted at every budget (`CertifiedTable.admits_of_budgetFree`). -/
namespace Tamarin.Theory

/-! ## Certification of the builtins -/

private def budgetFreePacket (P : Packet) : Bool :=
  match TableWire.input P.ds P.ns P.es #[] with
  | some ⟨_, rs, _⟩ => CertifiedTable.budgetFree rs
  | none => false

private theorem run_of_budgetFree {P : Packet} (h : budgetFreePacket P) (fuel : UInt64) :
    CertifiedTableWire.run P.ds P.ns P.es fuel = true := by
  unfold budgetFreePacket at h
  unfold CertifiedTableWire.run
  split at h
  · rename_i decoded
    rw [decoded]
    exact CertifiedTable.admits_of_budgetFree h _
  · cases h

set_option maxHeartbeats 8000000 in
/-- Every valid combination of builtins, without user symbols or rules, is
certified at every budget. -/
theorem builtin_certified (sig : Signature) (valid : sig.valid) (noFree : sig.free = #[])
    (noAC : sig.ac = 0) (fuel : UInt64) :
    CertifiedTableWire.run ({ sig with nodes := #[], rules := #[] } : Table).packet.ds
      ({ sig with nodes := #[], rules := #[] } : Table).packet.ns
      ({ sig with nodes := #[], rules := #[] } : Table).packet.es fuel = true := by
  obtain ⟨dh, xor, bp, mset, nat, free, ac⟩ := sig
  cases noFree
  cases noAC
  apply run_of_budgetFree
  revert valid
  cases dh <;> cases xor <;> cases bp <;> cases mset <;> cases nat <;> decide +kernel

end Tamarin.Theory
