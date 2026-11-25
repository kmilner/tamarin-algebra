import Tamarin.CertifiedTableWire
import Tamarin.TheoryWire
import Tamarin.CertifiedReductionWire
import Tamarin.VariantCheckWire
import Tamarin.VariantFold
import Tamarin.SessionTableWire
import TamarinRuntime.Candidates.Table
import Tamarin.CheckedReductionWire
import Tamarin.FactorRefutation
import Tamarin.TotalMatchWire
import Tamarin.TotalUnifyExists
import Tamarin.TotalUnifyFast
import Tamarin.TheoryWireFast
import Tamarin.UnifierNames
import Tamarin.PackedConjunction
import TamarinRuntime.Candidate
import TamarinRuntime.BinaryCancellation
import TamarinRuntime.XorMatchings
import TamarinRuntime.Whole
import TamarinRuntime.MixedSizeGraph
import TamarinRuntime.ACSpanOverlap
import TamarinRuntime.FactorCheck
import TamarinRuntime.ResidualVariable
import TamarinRuntime.ResidualRigid
import TamarinRuntime.GraphUnification
import TamarinRuntime.ACMatchPacket
import TamarinRuntime.ACBagSearch
import TamarinRuntime.ACBagAnswers
import TamarinRuntime.ACPagePacket
import TamarinRuntime.ACSortedBagPacket
import TamarinRuntime.ACFeasibility
import TamarinRuntime.AnswerProjection
import TamarinRuntime.SortedMatch
import TamarinRuntime.OpenMatchSelect
import TamarinRuntime.CollectorMultiplicity
import TamarinRuntime.ACPivot
import TamarinRuntime.VariantJoin
import TamarinRuntime.DHPeer
import TamarinRuntime.DHExponent
import TamarinRuntime.SignedGraph
import TamarinRuntime.DHTower
import TamarinRuntime.ACSubgroups
import TamarinRuntime.ReductionGraph
import TamarinRuntime.OperandUnification
import TamarinRuntime.ForcedOperandClasses
import TamarinRuntime.MaskedOperands
import TamarinRuntime.OperandRefinement
import TamarinRuntime.UnifierSelfNames

/-!
Fixed native export wrapper. Cargo builds this target without the proof/audit
harness. TamarinCI separately verifies these exact entry points before merge.
-/
namespace Tamarin.Executable

@[export tamarin_ac_bag_match]
def acBagMatch (packet : Matching.ACMatchPacket.Packet) : UInt8 :=
  Matching.ACMatchPacket.runWith Matching.ACBagSearch.run packet

@[export tamarin_ac_bag_typed_match]
def acBagTypedMatch (rows limits : Matching.ACMatchPacket.Packet) : UInt8 :=
  Matching.ACSortedBagPacket.runWith Matching.ACSortedBagSearch.run rows limits

@[export tamarin_match_size_excludes]
def matchSizeExcludes (pattern subject : UInt64) : Bool := decide (subject < pattern)

@[export tamarin_flat_ac_equal]
def flatACEqual (lhs rhs : Array UInt64) : UInt8 :=
  RuntimeCandidate.backend.equal lhs rhs

@[export tamarin_flat_ac_residual]
def flatACResidual (tail rhs : Array UInt64) : Array UInt64 :=
  RuntimeCandidate.backend.residual tail rhs

@[export tamarin_pairing_variants]
def pairingVariants (hasProjection : Bool) : UInt8 :=
  RuntimeCandidate.pairing.variants hasProjection

@[export tamarin_flat_ac_match]
def flatACMatch (n : UInt64) (occurrences tail rhs : Array UInt64) : Array (Array (Array UInt64)) :=
  (RuntimeCandidate.flatMatcher.run n.toNat (occurrences.toList.map UInt64.toNat)
    tail.toList rhs.toList).toArray.map (fun answer => answer.toArray.map List.toArray)

@[export tamarin_ac_pivot]
def acPivot (size : UInt64) : Option (Array (Array UInt64)) := ACPivotCandidate.run size

@[export tamarin_select_joined_variants]
def selectJoinedVariants (rows : Array (Array UInt64)) : Option (Array UInt64) :=
  VariantJoinCandidate.run rows

@[export tamarin_dh_peer_images]
def dhPeerImages (power : Bool) : Option (Array (Array UInt64)) := DHPeerCandidate.images power

@[export tamarin_dh_exponent_images]
def dhExponentImages (u : Unit) : Array (Array UInt64) := DHExponentCandidate.images u

@[export tamarin_dh_tower_images]
def dhTowerImages (width : UInt64) : Option (Array (Array UInt64)) := DHTowerCandidate.images width

@[export tamarin_signed_graph_variants]
def signedGraphVariants (inputs : UInt64) (obs : Array (Array UInt64)) : Array UInt64 :=
  SignedGraph.run inputs obs

@[export tamarin_reduction_graph]
def reductionGraph (rows : Array (Array UInt64)) : Bool := ReductionGraph.run rows

@[export tamarin_ac_subgroups]
def acSubgroups (n : UInt64) : Option (Array (Array UInt64)) := ACSubgroups.run n

@[export tamarin_collector_possible]
def collectorPossible (occ residual : Array UInt64) : Bool := CollectorMultiplicity.run occ residual

@[export tamarin_open_match_select]
def openMatchSelect (rigid subject : UInt64) : Option (Array (Array UInt64)) :=
  OpenMatchSelect.run rigid subject

@[export tamarin_sorted_ac_match]
def sortedACMatch (acSort : UInt64) (varSort atomSort occ tail rhs : Array UInt64) :
    Option (Array (Array (Array UInt64))) :=
  SortedMatch.runWith flatACMatch acSort varSort atomSort occ tail rhs

@[export tamarin_comm_orientations]
def commOrientations (a b c d : UInt64) (priority : UInt8) : UInt8 :=
  RuntimeCandidate.commOrientations a b c d priority

@[export tamarin_residual_rigid]
def residualRigid (lk : UInt8) (lh : UInt64) (ls : Array UInt64)
    (rk : UInt8) (rh : UInt64) (rs : Array UInt64) : UInt8 :=
  ResidualRigid.run lk lh ls rk rh rs

@[export tamarin_residual_variable]
def residualVariable (right : Bool) (key keySort : UInt64) (kind : UInt8)
    (valueSort : UInt64) (ids : Array UInt64) : UInt8 :=
  ResidualVariable.run right key keySort kind valueSort ids

@[export tamarin_xor_odd]
def xorOdd (count : UInt64) : Bool := RuntimeCandidate.xorOdd count

@[export tamarin_xor_branches]
def xorBranches (same : Bool) : UInt8 :=
  RuntimeCandidate.xorBranches same

@[export tamarin_binary_cancellation_rows]
def binaryCancellationRows (_ : Unit) : Array (Array UInt64) :=
  BinaryCancellationCandidate.rows

@[export tamarin_mixed_cancellation_rows]
def mixedCancellationRows (_ : Unit) : Array (Array UInt64) :=
  BinaryCancellationCandidate.mixedRows

@[export tamarin_xor_matchings]
def xorMatchings (width : UInt64) : Option (Array (Array UInt64)) :=
  XorMatchingCandidate.run width

@[export tamarin_exclude_root]
def excludeRoot (rows : Array (Array UInt64)) (args : Array UInt64) : Bool :=
  RuntimeCandidate.excludeRoot rows args

@[export tamarin_exclude_ac_factors]
def excludeACFactors (rows : Array (Array UInt64)) (heads : Array UInt64) : Bool :=
  RuntimeCandidate.excludeACFactors rows heads

@[export tamarin_constructor_variant]
def constructorVariant (roots used : Array UInt64) : Bool :=
  RuntimeCandidate.constructorVariant roots used

@[export tamarin_reduce_rule_slot]
def reduceRuleSlot (slot : UInt64) (keys subjects : Array UInt64) : Array UInt64 :=
  RuntimeCandidate.reduceRuleSlot slot keys subjects

@[export tamarin_ground_variant]
def groundVariant (holes anchors deps : Array UInt64) (rigid : Bool) : UInt8 :=
  RuntimeCandidate.groundVariant holes anchors deps rigid

@[export tamarin_cancel_common]
def cancelCommon (lhs rhs : Array UInt64) : Array (Array UInt64) :=
  RuntimeCandidate.cancelCommon lhs rhs

@[export tamarin_factor_refutes]
def factorRefutes (ds : Array UInt64) (ns : Array (Array UInt64)) (es : Array UInt64) : Bool :=
  FactorRefutation.run ds ns es

@[export tamarin_unpack_conjunction]
def unpackConjunction (nodes : PackedConjunction.Rows) (limit lhs rhs : UInt64) : PackedConjunction.Rows :=
  PackedConjunction.run nodes limit lhs rhs

/-! The searches of an interruptible export under a given caller. The caller
is an explicit argument here and an instance argument below. The compiler
specializes the calls in the body of a function for its instance arguments
only if the function has no instance argument of its own, so these four are
where the searches get specialized for the declarations of a packet. -/

@[noinline] def totalUnifyFor (i : Interrupt) (decls : Array UInt64) (nodes : Array (Array UInt64))
    (roots : Array UInt64) : Array (Array UInt64) := @TotalUnifyWire.run i decls nodes roots

@[noinline] def totalUnifyExistsFor (i : Interrupt) (decls : Array UInt64)
    (nodes : Array (Array UInt64)) (roots : Array UInt64) : UInt8 :=
  @TotalUnifyWire.runExists i decls nodes roots

@[noinline] def pathReduceFor (i : Interrupt) (ds : Array UInt64) (ns : Array (Array UInt64))
    (rules : Array UInt64) (root fuel : UInt64) : Array (Array UInt64) :=
  @PathReductionWire.run i ds ns rules root fuel

@[noinline] def sessionReduceFor (i : Interrupt) (ds : Array UInt64) (ns : Array (Array UInt64))
    (rules : Array UInt64) (extra : Array (Array UInt64)) (root fuel : UInt64) :
    Array (Array UInt64) :=
  @SessionReductionWire.run i ds ns rules extra root fuel

def totalUnify (poll : Unit → Bool) (decls : Array UInt64) (nodes : Array (Array UInt64))
    (roots : Array UInt64) : Array (Array UInt64) :=
  Interrupt.run poll #[#[4]] fun i => totalUnifyFor i decls nodes roots

def totalUnifyExists (poll : Unit → Bool) (decls : Array UInt64) (nodes : Array (Array UInt64))
    (roots : Array UInt64) : UInt8 :=
  Interrupt.run poll 4 fun i => totalUnifyExistsFor i decls nodes roots

/-- Tables that name the variables a family of unifiers adds to its query:
see `Tamarin.UnifierNames`. -/
@[export tamarin_name_unifiers]
def nameUnifiers (names heads : Array UInt64) (ranges proposal : Array (Array UInt64))
    (nat low : Bool) : Array (Array UInt64) :=
  UnifierNames.run names heads ranges proposal nat low

/-- A proposal for `nameUnifiers`, made from what the caller reads off the
reply of the unifier: see `Tamarin.UnifierSelfNames`. Nothing is promised about
it; `nameUnifiers` tests it as any other proposal. -/
@[export tamarin_propose_unifier_names]
def proposeUnifierNames (names heads order : Array UInt64) (ranges : Array (Array UInt64))
    (singles counts : Array UInt64) : Array (Array UInt64) :=
  UnifierSelfNames.propose names heads order ranges singles counts

/-- The reading of a reply of the unifier through the tables of
`nameUnifiers`, as the caller's reader has to produce it. The caller's tests
compare the two. `#[#[0]]` when there is no reading. -/
@[export tamarin_apply_names]
def applyNames (tables : Array (Array UInt64)) (nat : Bool) (reply : Array (Array UInt64)) :
    Array (Array UInt64) :=
  (UnifierNames.apply tables nat reply).getD #[#[0]]

def totalMatch (decls : Array UInt64) (nodes : Array (Array UInt64)) (roots ids : Array UInt64) :
    Array (Array UInt64) := TotalMatchWire.run decls nodes roots ids

def totalMatchExists (decls : Array UInt64) (nodes : Array (Array UInt64)) (roots ids : Array UInt64) :
    UInt8 := TotalMatchWire.runExists decls nodes roots ids

def pathReduce (poll : Unit → Bool) (ds : Array UInt64) (ns : Array (Array UInt64))
    (rules : Array UInt64) (root fuel : UInt64) : Array (Array UInt64) :=
  Interrupt.run poll #[#[4]] fun i => pathReduceFor i ds ns rules root fuel

def sessionReduce (poll : Unit → Bool) (ds : Array UInt64) (ns : Array (Array UInt64))
    (rules : Array UInt64) (extra : Array (Array UInt64)) (root fuel : UInt64) :
    Array (Array UInt64) :=
  Interrupt.run poll #[#[4]] fun i => sessionReduceFor i ds ns rules extra root fuel

@[noinline] def sessionVariantCheckFor (i : Interrupt) (ds : Array UInt64) (ns : Array (Array UInt64))
    (rules : Array UInt64) (extra : Array (Array UInt64)) (roots : Array UInt64)
    (family : Array (Array UInt64)) (fuel work : UInt64) : Array (Array UInt64) :=
  @SessionVariantCheckWire.run i ds ns rules extra roots family fuel work

def sessionVariantCheck (poll : Unit → Bool) (ds : Array UInt64) (ns : Array (Array UInt64))
    (rules : Array UInt64) (extra : Array (Array UInt64)) (roots : Array UInt64)
    (family : Array (Array UInt64)) (fuel work : UInt64) : Array (Array UInt64) :=
  Interrupt.run poll #[#[4]] fun i => sessionVariantCheckFor i ds ns rules extra roots family fuel work

@[export tamarin_checked_variants]
def checkedVariants (ds : Array UInt64) (ns : Array (Array UInt64)) (rules roots : Array UInt64) (fuel : UInt64) :
    Array (Array UInt64) := CheckedVariantsWire.run ds ns rules roots fuel

def certifyTable (ds : Array UInt64) (ns : Array (Array UInt64)) (rules : Array UInt64) (fuel : UInt64) : Bool :=
  CertifiedTableWire.run ds ns rules fuel

@[export tamarin_general_variants]
def generalVariants (ds : Array UInt64) (ns : Array (Array UInt64)) (rules roots : Array UInt64) (fuel : UInt64) :
    Array (Array UInt64) := TableCandidate.variants ds ns rules roots fuel

@[noinline] def foldVariantsFor (i : Interrupt) (ds : Array UInt64) (ns : Array (Array UInt64))
    (rules roots : Array UInt64) (fuel work : UInt64) : Array (Array UInt64) :=
  @FoldVariantsWire.run i ds ns rules roots fuel work

@[export tamarin_fold_variants]
def foldVariants (poll : Unit → Bool) (ds : Array UInt64) (ns : Array (Array UInt64))
    (rules roots : Array UInt64) (fuel work : UInt64) : Array (Array UInt64) :=
  Interrupt.run poll #[#[4]] fun i => foldVariantsFor i ds ns rules roots fuel work

@[export tamarin_variant_overlap_agrees]
def variantOverlapAgrees (decls : Array UInt64) (nodes : Array (Array UInt64)) (roots : Array UInt64) : Bool :=
  ACSpanOverlap.run decls nodes roots

@[export tamarin_check_factors]
def checkFactors (decls : Array UInt64) (nodes : Array (Array UInt64))
    (original bindings residual : Array UInt64) : Bool :=
  FactorCheck.run decls nodes original bindings residual

@[export tamarin_operand_refine]
def operandRefine (sides : Array UInt64) : Array UInt64 := OperandRefinementCandidate.keep sides

@[export tamarin_operand_unify]
def operandUnify (width : UInt64) (sides : Array (Array UInt64)) : Option Homogeneous.Answers :=
  OperandUnification.runWith OperandCounts.run Homogeneous.solve width sides

@[export tamarin_masked_operand_unify]
def maskedOperandUnify (width mask : UInt64) (sides : Array (Array UInt64)) : Option Homogeneous.Answers :=
  MaskedOperands.run width mask sides

@[export tamarin_project_answers]
def projectAnswers (width : UInt64) (answers : Homogeneous.Answers) : Option Homogeneous.Answers :=
  AnswerProjection.project width answers

/-! Exports over the theory of a Tamarin file (`Tamarin.Theory`): the caller
sends the builtin flags, the arities of its other free symbols and the number
of its AC symbols instead of declaration words, and the user rules of a table.
The builtin rules are added here. Each export is the export above on the packet
`Tamarin.Theory` builds; arguments that are not those of a valid signature get
the reply to an undecodable packet. The terms of a call on a table arrive as
rows `extra` numbered from 0, and `root`, `roots` and `family` index them. -/

@[export tamarin_theory_unify]
def theoryUnify (poll : Unit → Bool) (flags : UInt64) (free : Array UInt64) (ac : UInt64)
    (nodes : Array (Array UInt64)) (roots : Array UInt64) : Array (Array UInt64) :=
  totalUnify poll (Theory.wireDeclarations flags free ac) nodes roots

@[export tamarin_theory_unify_exists]
def theoryUnifyExists (poll : Unit → Bool) (flags : UInt64) (free : Array UInt64) (ac : UInt64)
    (nodes : Array (Array UInt64)) (roots : Array UInt64) : UInt8 :=
  totalUnifyExists poll (Theory.wireDeclarations flags free ac) nodes roots

@[export tamarin_theory_match]
def theoryMatch (flags : UInt64) (free : Array UInt64) (ac : UInt64) (nodes : Array (Array UInt64))
    (roots ids : Array UInt64) : Array (Array UInt64) :=
  totalMatch (Theory.wireDeclarations flags free ac) nodes roots ids

@[export tamarin_theory_match_exists]
def theoryMatchExists (flags : UInt64) (free : Array UInt64) (ac : UInt64)
    (nodes : Array (Array UInt64)) (roots ids : Array UInt64) : UInt8 :=
  totalMatchExists (Theory.wireDeclarations flags free ac) nodes roots ids

@[export tamarin_theory_certify]
def theoryCertify (flags : UInt64) (free : Array UInt64) (ac : UInt64) (nodes : Array (Array UInt64))
    (rules : Array UInt64) (fuel : UInt64) : Bool :=
  let p := Theory.wirePacket flags free ac nodes rules
  certifyTable p.ds p.ns p.es fuel

@[export tamarin_theory_path_reduce]
def theoryPathReduce (poll : Unit → Bool) (flags : UInt64) (free : Array UInt64) (ac : UInt64)
    (nodes : Array (Array UInt64)) (rules : Array UInt64) (extra : Array (Array UInt64))
    (root fuel : UInt64) : Array (Array UInt64) :=
  let p := Theory.wirePacket flags free ac nodes rules
  pathReduce poll p.ds (p.ns ++ Theory.moveRows p.ns.size extra) p.es
    (Theory.place p.ns.size extra.size root) fuel

@[export tamarin_theory_reduce]
def theoryReduce (poll : Unit → Bool) (flags : UInt64) (free : Array UInt64) (ac : UInt64)
    (nodes : Array (Array UInt64)) (rules : Array UInt64) (extra : Array (Array UInt64))
    (root fuel : UInt64) : Array (Array UInt64) :=
  let p := Theory.wirePacket flags free ac nodes rules
  sessionReduce poll p.ds p.ns p.es (Theory.moveRows p.ns.size extra)
    (Theory.place p.ns.size extra.size root) fuel

@[export tamarin_theory_variant_check]
def theoryVariantCheck (poll : Unit → Bool) (flags : UInt64) (free : Array UInt64) (ac : UInt64)
    (nodes : Array (Array UInt64)) (rules : Array UInt64) (extra : Array (Array UInt64))
    (roots : Array UInt64) (family : Array (Array UInt64)) (fuel work : UInt64) :
    Array (Array UInt64) :=
  let p := Theory.wirePacket flags free ac nodes rules
  sessionVariantCheck poll p.ds p.ns p.es (Theory.moveRows p.ns.size extra)
    (roots.map (Theory.place p.ns.size extra.size))
    (family.map (·.map (Theory.place p.ns.size extra.size))) fuel work

end Tamarin.Executable
