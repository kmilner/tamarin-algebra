import TamarinRuntime
import Tamarin.TotalUnifyPacket

namespace Tamarin.TotalUnifyWireTests

private abbrev kernel := Executable.totalUnify
private def decls : Array UInt64 := #[4,7,2,2,2,2,2,8,1,2,2]
private def nested : Array (Array UInt64) :=
  #[#[0,0,2],#[1,0,0],#[1,1,0],#[4,7,1,2],#[2,8,3]]

-- X = h(a*b) retains both atom identities and the outer free symbol.
#guard kernel decls nested #[0,4] == #[#[1],#[],#[0,2,1,0,0,1,1,0,4,7,2,2,8,1]]
#guard kernel #[] #[] #[] == #[#[1],#[]]
#guard kernel #[] #[#[1,0,0],#[1,1,0]] #[0,1] == #[#[1]]
#guard kernel decls #[#[2,8,1]] #[0,0] == #[#[0]]
#guard kernel decls nested #[0] == #[#[0]]

-- A Msg variable cannot bind to an ill-sorted h(Node). The same kind-level
-- subtree on both sides is nevertheless a legal ordinary unification query.
private def kindTerms : Array (Array UInt64) := #[#[0,0,2],#[1,0,3],#[2,8,1]]
#guard kernel decls kindTerms #[0,2] == #[#[1]]
#guard kernel decls kindTerms #[2,2] == #[#[1],#[]]

-- One disjoint factor rules out this kind-level equation before AC enumeration.
private def natNodes : Array (Array UInt64) := #[#[0,0,1],#[1,1,4],#[0,2,4],
  #[4,7,0] ++ Array.replicate 64 1, #[4,7,2] ++ Array.replicate 64 1]
#guard kernel #[4,7,2,4,4,4] natNodes #[3,4] == #[#[1]]

-- Each slot takes its principal sort: one arm for x = y, one per alignment of a
-- commutative pair, and the seven minimal unifiers of x+y = z+w.
private def arms (r : Array (Array UInt64)) : Nat := (r.toList.filter (·.isEmpty)).length
private def four : Array (Array UInt64) := #[#[0,0,2],#[0,1,2],#[0,2,2],#[0,3,2]]
#guard arms (kernel #[] #[#[0,0,2],#[0,1,2]] #[0,1]) == 1
#guard arms (kernel #[3,9,2,2,2,2] (four ++ #[#[3,9,0,1],#[3,9,2,3]]) #[4,5]) == 2
#guard arms (kernel #[4,7,2,2,2,2] (four ++ #[#[4,7,0,1],#[4,7,2,3]]) #[4,5]) == 7
-- Fresh and Msg meet at Fresh. Pub and Fresh have no common instance.
#guard kernel #[] #[#[0,0,1],#[0,1,2]] #[0,1] == #[#[1],#[],#[0,1,0,0,1],#[1,2,0,0,1]]
#guard kernel #[] #[#[0,0,0],#[0,1,1]] #[0,1] == #[#[1]]

-- Replay preserves aliases through free decomposition and under AC terms.
-- A commutative or AC alignment cannot be rejected by positional decomposition.
private abbrev refutes := Executable.factorRefutes
private def aliases : Array (Array UInt64) := #[#[0,0,2],#[0,1,2],#[2,8,0],#[2,8,1],#[4,7,1,0]]
#guard refutes decls aliases #[2,3,1,4]  -- x=y, y=y+x
#guard !refutes decls aliases #[2,3,0,1]
-- A Fresh = Msg alias binds the broader variable. It cannot subsequently be a Pub atom.
#guard refutes #[] #[#[0,0,1],#[0,1,2],#[1,2,0]] #[0,1,1,2]
#guard !refutes decls (aliases.push #[4,7,0,1]) #[4,5]
#guard !refutes decls aliases #[0,99]
-- A checker may settle the late clash or leave it to the total unifier.
private def lateClash := (Array.replicate 256 (#[0,0] : Array UInt64)).flatten ++ #[1,4]
#guard refutes decls aliases lateClash || kernel decls aliases lateClash == #[#[1]]
#guard refutes decls kindTerms #[0,2]

-- The decision entry point agrees with the listing: 1 for a unifier, 2 for
-- none, 0 for a malformed packet.
private abbrev existsKernel := Executable.totalUnifyExists
#guard existsKernel decls nested #[0,4] == 1
#guard existsKernel #[] #[] #[] == 1
#guard existsKernel #[] #[#[1,0,0],#[1,1,0]] #[0,1] == 2
#guard existsKernel decls #[#[2,8,1]] #[0,0] == 0
#guard existsKernel decls nested #[0] == 0
#guard existsKernel decls kindTerms #[0,2] == 2
#guard existsKernel decls kindTerms #[2,2] == 1
#guard existsKernel #[4,7,2,4,4,4] natNodes #[3,4] == 2

-- Sums of variables are decided by a positive solution of the linear system,
-- without listing: x+y+z+w = u+v+s+t, 131x+y = 137z beside x = y, and that
-- system beside 131x+2y = 137z, which leaves y no factor.
private def ac : Array UInt64 := #[4,0,2,2,2,2]
private def wide : Array (Array UInt64) :=
  #[#[0,0,2],#[0,1,2],#[0,2,2],#[0,3,2],#[4,0,0,1,2,3],#[0,4,2],#[0,5,2],#[0,6,2],#[0,7,2],#[4,0,5,6,7,8]]
#guard existsKernel ac wide #[4,9] == 1
private def heavy : Array (Array UInt64) :=
  #[#[0,0,2],#[0,1,2],#[0,2,2],#[4,0] ++ Array.replicate 131 0 ++ #[1],#[4,0] ++ Array.replicate 137 2,
    #[4,0] ++ Array.replicate 131 0 ++ #[1,1]]
#guard existsKernel ac heavy #[3,4,0,1] == 1
#guard existsKernel ac heavy #[3,4,5,4] == 2

end Tamarin.TotalUnifyWireTests
