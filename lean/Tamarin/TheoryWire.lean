import Tamarin.Theory

/-! How the `tamarin_theory_*` exports turn their arguments into the packet of
an existing export. Arguments that are not those of a valid signature become a
packet whose declarations do not decode. -/
namespace Tamarin.Theory

/-- Declaration words that do not decode. -/
def undecodable : Array UInt64 := #[0]

def wireDeclarations (flags : UInt64) (free : Array UInt64) (ac : UInt64) : Array UInt64 :=
  match Signature.ofWire flags free ac with
  | some sig => sig.declarations
  | none => undecodable

def wirePacket (flags : UInt64) (free : Array UInt64) (ac : UInt64) (nodes : Array (Array UInt64))
    (rules : Array UInt64) : Packet :=
  match Signature.ofWire flags free ac with
  | some sig => ({ sig with nodes, rules } : Table).packet
  | none => ⟨undecodable, #[], #[]⟩

end Tamarin.Theory
