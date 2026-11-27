import Tamarin.TotalUnifyWire
import Tamarin.ReferenceMatching

/-! Directional matching uses the same term dictionary and postfix answer
rows as ordinary unification. Variables in match images retain their input
identities. The scope selects bindable variables by their dictionary IDs. -/
namespace Tamarin.TotalMatchWire
open TotalUnifyWire

def domain {s : Signature} (p : Problem s) (ids : Array UInt64) : List Variable :=
  p.variables.filter fun v => ids.any fun i => i.toNat == v.id

def run (decls : Array UInt64) (nodes : Array (Array UInt64)) (roots ids : Array UInt64) :
    Array (Array UInt64) :=
  (do
    let ⟨d,p⟩ ← input decls nodes roots
    pack p ((ReferenceMatching.matcher d.sig).run p trivial (domain p ids))).getD #[#[0]]

/-- The head of the enumeration behind `run`, found without listing the rest. -/
def runFirst (decls : Array UInt64) (nodes : Array (Array UInt64)) (roots ids : Array UInt64) :
    Array (Array UInt64) :=
  (do
    let ⟨_,p⟩ ← input decls nodes roots
    pack p (ReferenceMatching.first p (domain p ids)).toList).getD #[#[0]]

/-- Status 1 when the conjunction has a match, 2 when it has none, and 0 for a
malformed packet. No answer beyond the first is computed. -/
def runExists (decls : Array UInt64) (nodes : Array (Array UInt64)) (roots ids : Array UInt64) :
    UInt8 :=
  match input decls nodes roots with
  | none => 0
  | some ⟨_,p⟩ => if (ReferenceMatching.first p (domain p ids)).isSome then 1 else 2

end Tamarin.TotalMatchWire
