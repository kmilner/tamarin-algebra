import TamarinRuntime
import Tamarin.BilinearWireData

/-! The `tamarin_theory_*` exports against the existing exports on the same
packets written out by hand. -/
namespace Tamarin.TheoryTests
open Theory

private def quiet : Unit → Bool := fun _ => false

/-! ## Declarations -/

-- DH, one user free symbol of arity 2 (id 16) and one user AC symbol (id 16).
private def dhSig : Theory.Signature := ⟨true, false, false, false, false, #[2], 1⟩
private def dhWords : Array UInt64 :=
  #[2,0,2,2,2,2, 2,1,1,2,2, 2,2,0,2, 2,3,0,2, 4,0,2,2,2,2, 2,16,2,2,2,2, 4,16,2,2,2,2]
#guard dhSig.declarations == dhWords
#guard dhSig.flags == 1
-- All builtins: the natural-number symbols have sort nat.
private def allSig : Theory.Signature := ⟨true, true, true, true, true, #[], 0⟩
#guard allSig.declarations ==
  #[2,0,2,2,2,2, 2,1,1,2,2, 2,2,0,2, 2,3,0,2, 4,0,2,2,2,2, 4,1,2,2,2,2, 2,4,0,2,
    2,5,2,2,2,2, 3,0,2,2,2,2, 4,2,2,2,2,2, 4,3,2,4,4,4, 2,6,0,4]
#guard allSig.flags == 31
-- The flags are read back exactly; bilinear pairing without DH, unknown bits
-- and counts above the limit are not a signature.
#guard (Theory.Signature.ofWire 31 #[] 0).isSome
#guard (List.range 32).filter (fun f => (Theory.Signature.ofWire f.toUInt64 #[] 0).isSome) ==
  [0,1,2,3,5,7,8,9,10,11,13,15,16,17,18,19,21,23,24,25,26,27,29,31]
#guard (Theory.Signature.ofWire 4 #[] 0).isNone
#guard (Theory.Signature.ofWire 33 #[] 0).isNone
#guard (Theory.Signature.ofWire 0 #[4097] 0).isNone
#guard (Theory.Signature.ofWire 0 #[] 4097).isNone
#guard (Theory.Signature.ofWire 0 #[4096] 4096).isSome

/-! ## Unification and matching -/

-- f(x, one) = f(inv(y), z), and u(x, y) = u(a, b) with u the user AC symbol.
private def unifyRows : Array (Array UInt64) :=
  #[#[0,0,2], #[0,1,2], #[0,2,2], #[2,2], #[2,16,0,3], #[2,1,1], #[2,16,5,2],
    #[1,7,2], #[1,8,2], #[4,16,0,1], #[4,16,7,8]]
#guard Executable.theoryUnify quiet 1 #[2] 1 unifyRows #[4,6] ==
  Executable.totalUnify quiet dhWords unifyRows #[4,6]
#guard (Executable.theoryUnify quiet 1 #[2] 1 unifyRows #[4,6])[0]? == some #[1]
#guard Executable.theoryUnify quiet 1 #[2] 1 unifyRows #[9,10] ==
  Executable.totalUnify quiet dhWords unifyRows #[9,10]
#guard (Executable.theoryUnify quiet 1 #[2] 1 unifyRows #[9,10])[0]? == some #[1]
#guard Executable.theoryUnifyExists quiet 1 #[2] 1 unifyRows #[4,6] ==
  Executable.totalUnifyExists quiet dhWords unifyRows #[4,6]
#guard Executable.theoryUnifyExists quiet 1 #[2] 1 unifyRows #[4,9] == 2
-- Without DH the symbol one is not declared; the query does not decode.
#guard Executable.theoryUnify quiet 0 #[2] 1 unifyRows #[4,6] == #[#[0]]
-- Invalid flags and interruption.
#guard Executable.theoryUnify quiet 4 #[2] 1 unifyRows #[4,6] == #[#[0]]
#guard Executable.theoryUnify quiet 33 #[2] 1 unifyRows #[4,6] == #[#[0]]
#guard Executable.theoryUnifyExists quiet 4 #[2] 1 unifyRows #[4,6] == 0
#guard Executable.theoryUnify (fun _ => true) 1 #[2] 1 unifyRows #[4,6] == #[#[4]]
#guard Executable.theoryUnifyExists (fun _ => true) 1 #[2] 1 unifyRows #[4,6] == 4

-- Pattern f(x, one), subject f(inv(a), one), x bindable.
private def matchRows : Array (Array UInt64) :=
  #[#[0,0,2], #[2,2], #[2,16,0,1], #[1,7,2], #[2,1,3], #[2,16,4,1]]
#guard Executable.theoryMatch 1 #[2] 1 matchRows #[2,5] #[0] ==
  Executable.totalMatch dhWords matchRows #[2,5] #[0]
#guard (Executable.theoryMatch 1 #[2] 1 matchRows #[2,5] #[0]).size == 3
#guard Executable.theoryMatchExists 1 #[2] 1 matchRows #[2,5] #[0] ==
  Executable.totalMatchExists dhWords matchRows #[2,5] #[0]
#guard Executable.theoryMatchExists 1 #[2] 1 matchRows #[5,2] #[0] == 2
#guard Executable.theoryMatch 6 #[2] 1 matchRows #[2,5] #[0] == #[#[0]]
#guard Executable.theoryMatchExists 6 #[2] 1 matchRows #[2,5] #[0] == 0

/-! ## Tables -/

-- XOR alone: the rows of its three rules, written out.
private def xorTable : Table := ⟨⟨false, true, false, false, false, #[], 0⟩, #[], #[]⟩
private def xorWords : Array UInt64 := #[4,1,2,2,2,2, 2,4,0,2]
private def xorRows : Array (Array UInt64) :=
  #[#[0,1,2], #[0,1,2], #[4,1,0,1], #[2,4],
    #[0,1,2], #[0,1,2], #[0,2,2], #[4,1,5,6], #[4,1,4,7], #[0,2,2],
    #[0,1,2], #[2,4], #[4,1,10,11], #[0,1,2]]
private def xorRoots : Array UInt64 := #[2,3, 8,9, 12,13]
#guard xorTable.packet.ds == xorWords
#guard xorTable.packet.ns == xorRows
#guard xorTable.packet.es == xorRoots
#guard Executable.theoryCertify 2 #[] 0 #[] #[] 0
#guard Executable.certifyTable xorWords xorRows xorRoots 0

-- xor(a, xor(b, a)) reduces to b. The term rows are numbered from 0; the
-- packet of the old export has them after the 14 rule rows.
private def xorTerm : Array (Array UInt64) := #[#[1,7,2], #[1,8,2], #[4,1,1,0], #[4,1,0,2]]
private def xorTermMoved : Array (Array UInt64) := #[#[1,7,2], #[1,8,2], #[4,1,15,14], #[4,1,14,16]]
#guard Executable.theoryReduce quiet 2 #[] 0 #[] #[] xorTerm 3 16 ==
  Executable.sessionReduce quiet xorWords xorRows xorRoots xorTermMoved 17 16
#guard Executable.theoryReduce quiet 2 #[] 0 #[] #[] xorTerm 3 16 == #[#[1], #[1,8,2]]
#guard Executable.theoryPathReduce quiet 2 #[] 0 #[] #[] xorTerm 3 16 ==
  Executable.pathReduce quiet xorWords (xorRows ++ xorTermMoved) xorRoots 17 16
#guard Executable.theoryPathReduce quiet 2 #[] 0 #[] #[] xorTerm 3 16 == #[#[1], #[1,8,2]]
-- A root or child index outside the term rows names no row.
#guard Executable.theoryReduce quiet 2 #[] 0 #[] #[] xorTerm 4 16 == #[#[0]]
#guard Executable.theoryReduce quiet 2 #[] 0 #[] #[] #[#[1,7,2], #[4,1,0,1]] 1 16 == #[#[0]]
#guard Executable.theoryReduce quiet 2 #[] 0 #[] #[] #[#[4,1,0,1]] 0 16 == #[#[0]]
#guard Executable.theoryReduce (fun _ => true) 2 #[] 0 #[] #[] xorTerm 3 16 == #[#[4]]

-- Pairing as user rules: pair 16, fst 17, snd 18; fst(pair(x,y)) = x and
-- snd(pair(x,y)) = y. Without equational builtins the packet is the user's.
private def pairFree : Array UInt64 := #[2,1,1]
private def pairWords : Array UInt64 := #[2,16,2,2,2,2, 2,17,1,2,2, 2,18,1,2,2]
private def pairRows : Array (Array UInt64) :=
  #[#[0,0,2], #[0,1,2], #[2,16,0,1], #[2,17,2], #[2,18,2]]
private def pairRules : Array UInt64 := #[3,0,4,1]
private def pairTable : Table := ⟨⟨false, false, false, false, false, pairFree, 0⟩, pairRows, pairRules⟩
#guard pairTable.packet.ds == pairWords
#guard pairTable.packet.ns == pairRows
#guard pairTable.packet.es == pairRules
#guard Executable.theoryCertify 0 pairFree 0 pairRows pairRules 0 ==
  Executable.certifyTable pairWords pairRows pairRules 0
#guard Executable.theoryCertify 0 pairFree 0 pairRows pairRules 0
-- A user row may name only earlier user rows.
#guard !Executable.theoryCertify 0 pairFree 0 #[#[0,0,2], #[2,17,5]] #[1,0] 0
#guard !Executable.theoryCertify 0 pairFree 0 pairRows #[3,0,4,5] 0
#guard !Executable.theoryCertify 4 pairFree 0 pairRows pairRules 0

-- The variant check on fst(z), z with the family z ↦ z, z ↦ pair(x', y').
private def pairExtra : Array (Array UInt64) :=
  #[#[0,2,2], #[2,17,0], #[0,3,2], #[0,4,2], #[2,16,2,3]]
private def pairExtraMoved : Array (Array UInt64) :=
  #[#[0,2,2], #[2,17,5], #[0,3,2], #[0,4,2], #[2,16,7,8]]
#guard Executable.theoryVariantCheck quiet 0 pairFree 0 pairRows pairRules pairExtra #[1,0]
    #[#[0,0], #[0,4]] 16 0 ==
  Executable.sessionVariantCheck quiet pairWords pairRows pairRules pairExtraMoved #[6,5]
    #[#[5,5], #[5,9]] 16 0
#guard Executable.theoryVariantCheck quiet 0 pairFree 0 pairRows pairRules pairExtra #[1,0]
    #[#[0,0], #[0,4]] 16 0 == #[#[1]]
#guard Executable.theoryVariantCheck quiet 0 pairFree 0 pairRows pairRules pairExtra #[1,0]
    #[#[0,0]] 16 0 == #[#[2,3,0]]
#guard Executable.theoryVariantCheck quiet 0 pairFree 0 pairRows pairRules pairExtra #[1,0]
    #[#[0,0], #[0,5]] 16 0 == #[#[0]]
#guard Executable.theoryVariantCheck quiet 4 pairFree 0 pairRows pairRules pairExtra #[1,0]
    #[#[0,0], #[0,4]] 16 0 == #[#[0]]
#guard Executable.theoryVariantCheck (fun _ => true) 0 pairFree 0 pairRows pairRules pairExtra #[1,0]
    #[#[0,0], #[0,4]] 16 0 == #[#[4]]
#guard Executable.theoryReduce quiet 0 pairFree 0 pairRows pairRules pairExtra 1 16 ==
  Executable.sessionReduce quiet pairWords pairRows pairRules pairExtraMoved 6 16

-- DH, bilinear pairing and XOR with pairing as user rules: the production
-- table of `BilinearWire`, with the theory's symbol ids, is certified like it.
private def bilinearTable : Table :=
  ⟨⟨true, true, true, false, false, #[2,1,1], 0⟩,
    #[#[0,0,2], #[0,1,2], #[2,16,0,1], #[2,17,2], #[2,18,2]], #[3,0,4,1]⟩
#guard Executable.certifyTable BilinearWire.declarations BilinearWire.nodes BilinearWire.ruleRoots 0
#guard Executable.theoryCertify 7 #[2,1,1] 0 bilinearTable.nodes bilinearTable.rules 0
#guard Executable.certifyTable bilinearTable.packet.ds bilinearTable.packet.ns bilinearTable.packet.es 0
-- Every valid combination of builtins alone is certified at every budget
-- (`theoryCertify_builtin`); invalid flags are refused (`theoryCertify_foreign`).
#guard Executable.theoryCertify 31 #[] 0 #[] #[] 0
#guard !Executable.theoryCertify 6 #[] 0 #[] #[] 0

end Tamarin.TheoryTests
