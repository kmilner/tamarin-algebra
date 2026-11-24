#!/usr/bin/env python3
"""Negative integration checks for the root-module build audit and the standalone export audit.

Each probe elaborates a temporary copy of TamarinCI.lean with one additional
declaration before its audit. Production files are never modified. The
implemented_by probe has a kernel proof of logical correctness, so rejecting
it specifically tests the gap between logical and executable definitions.
"""

from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import os
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
SOURCE = (ROOT / "TamarinCI.lean").read_text()
PROPOSERS = (ROOT / "TamarinProposers.lean").read_text()


# Assemble the contract exports and their contract statements in one temporary
# module, so mutations check the current source rather than an old imported
# .olean. The module holds the text of TamarinRuntime.lean, which defines the
# exports, followed by every contract theorem of the proof root. It imports
# what the proof root imports except the umbrella module, which imports the
# compiled runtime.
RUNTIME = (ROOT / "TamarinRuntime.lean").read_text()
imports = list(dict.fromkeys(
    line for line in (RUNTIME + SOURCE).splitlines()
    if line.startswith("import ") and line not in ("import Tamarin", "import Lean")
))
CONTRACT = SOURCE[SOURCE.index("\nnamespace Tamarin\n"):SOURCE.index("\nend Tamarin\n") + len("\nend Tamarin\n")]
EXECUTABLE = "\n".join(imports) + "\n" + "\n".join(
    line for line in RUNTIME.splitlines() if not line.startswith("import ")
) + "\n" + CONTRACT
MARKER = "open Lean in\nrun_cmd do"
PROBES = [
    (
        "unproved_export",
        "@[export tamarin_unproved] def Tamarin.AuditProbe.unproved : Nat := 0\n",
        "Unapproved project export",
    ),
    (
        "duplicate_export",
        "@[export tamarin_flat_ac_equal] def Tamarin.AuditProbe.unproved "
        "(_ _ : Array UInt64) : UInt8 := 1\n",
        "Unapproved project export",
    ),
    (
        "changed_export_mapping",
        "attribute [export tamarin_wrong_equal] Tamarin.Executable.flatACEqual\n",
        "Cannot add attribute `[export]`",
    ),
    (
        "implemented_by",
        """
namespace Tamarin.AuditProbe
def wrong (_ : Nat) : Nat := 0
@[implemented_by wrong] def verified (n : Nat) : Nat := n
theorem verified_correct (n : Nat) : verified n = n := rfl
end Tamarin.AuditProbe
""",
        "unchecked implemented_by replacement",
    ),
    # Use real inductives and the compiler's own declaration names. Either
    # half can lie even when the other half has the expected implementation.
    (
        "forged_logical_constructor_index",
        """
namespace Tamarin.AuditProbe
set_option genCtorIdx false in
inductive Tag | left | right
unsafe def Tag.ctorIdx._impl (x : Tag) : Nat := getObjTagNat x
@[implemented_by Tag.ctorIdx._impl] def Tag.ctorIdx (_ : Tag) : Nat := 0
end Tamarin.AuditProbe
""",
        "has unchecked implemented_by replacement",
    ),
    (
        "forged_runtime_constructor_index",
        """
namespace Tamarin.AuditProbe
set_option genCtorIdx false in
inductive Tag | left | right
unsafe def Tag.ctorIdx._impl (_ : Tag) : Nat := 0
@[implemented_by Tag.ctorIdx._impl] def Tag.ctorIdx (x : Tag) : Nat := Tag.casesOn x 0 1
end Tamarin.AuditProbe
""",
        "has unchecked implemented_by replacement",
    ),
    (
        "extern",
        """
namespace Tamarin.AuditProbe
@[extern "audit_probe_untrusted"] def verified (n : Nat) : Nat := n
theorem verified_correct (n : Nat) : verified n = n := rfl
end Tamarin.AuditProbe
""",
        "unchecked extern implementation",
    ),
    (
        "value_initializer",
        """
namespace Tamarin.AuditProbe
def wrong : IO Nat := pure 0
@[init wrong] def verified : Nat := 1
theorem verified_correct : verified = 1 := rfl
end Tamarin.AuditProbe
""",
        "unchecked runtime initializer",
    ),
    (
        "builtin_initializer",
        """
namespace Tamarin.AuditProbe
def wrong : IO Nat := pure 0
@[builtin_init wrong] def verified : Nat := 1
theorem verified_correct : verified = 1 := rfl
end Tamarin.AuditProbe
""",
        "unchecked runtime initializer",
    ),
    (
        "outside_namespace",
        """
namespace OtherNamespace
def wrong (_ : Nat) : Nat := 0
@[implemented_by wrong] def verified (n : Nat) : Nat := n
end OtherNamespace
""",
        "unchecked implemented_by replacement",
    ),
    (
        "unsafe",
        "unsafe def Tamarin.AuditProbe.unchecked : Nat := 0\n",
        "unsafe project declaration",
    ),
    (
        "axiom",
        "axiom Tamarin.AuditProbe.assumed : False\n",
        "depends on unapproved axiom",
    ),
    (
        "contract_theorem_about_proposer",
        "theorem Tamarin.AuditProbe.aboutProposer :\n"
        "    Tamarin.Executable.xorOdd 1 = Tamarin.Executable.xorOdd 1 := rfl\n",
        "mentions the proposer export",
    ),
    (
        "private_axiom",
        "namespace OtherNamespace\nprivate axiom assumed : False\nend OtherNamespace\n",
        "depends on unapproved axiom",
    ),
]

# (label, text of TamarinRuntime.lean, its replacement, theorem whose proof must
# then fail). The text is the body of a definition a contract export is built
# on: the eight theory exports are `totalUnify`, `certifyTable`, ... on the
# packet of the theory. The theorem is a contract statement, or a private lemma
# of the proof root from which the contract statement named in the comment
# beside it is proved, directly or through the lemma about that definition: a
# contract statement that cites a lemma does not fail itself when the lemma
# does. Only contract exports appear: a proposer export has no
# contract, so nothing may depend on what it computes.
CERTIFY_RUN = "CertifiedTableWire.run ds ns rules fuel"
TOTAL_RUN = "@TotalUnifyWire.run i decls nodes roots"
MATCH_RUN = "TotalMatchWire.run decls nodes roots ids"
EXISTS_RUN = "TotalMatchWire.runExists decls nodes roots ids"
UNPACK_RUN = "PackedConjunction.run nodes limit lhs rhs"
PATH_REDUCE = "@PathReductionWire.run i ds ns rules root fuel"
SESSION_REDUCE = "@SessionReductionWire.run i ds ns rules extra root fuel"
SESSION_CHECK = "@SessionVariantCheckWire.run i ds ns rules extra roots family fuel work"
NAME_RUN = "UnifierNames.run names heads ranges proposal nat low"
EXPORT_MUTATIONS = [
    ("certifies_conflicting_tables", CERTIFY_RUN, "true", "theorem theoryCertify_sound"),
    ("certifies_missing_rules", CERTIFY_RUN, "CertifiedTableWire.run ds ns #[] fuel",
     "theorem theoryCertify_builtin"),
    ("refuses_all_certificates", CERTIFY_RUN, "false", "theorem theoryCertify_builtin"),
    # The tables of the builtins alone that a theory sends for DH with XOR and
    # for DH with bilinear pairing: `theoryCertify_builtin` says both are accepted.
    ("refuses_dh_xor_builtin_table", CERTIFY_RUN,
     "(ds != Theory.Signature.declarations ⟨true, true, false, false, false, #[], 0⟩ && "
     "CertifiedTableWire.run ds ns rules fuel)",
     "theorem theoryCertify_builtin"),
    ("refuses_dh_bp_builtin_table", CERTIFY_RUN,
     "(ds != Theory.Signature.declarations ⟨true, false, true, false, false, #[], 0⟩ && "
     "CertifiedTableWire.run ds ns rules fuel)",
     "theorem theoryCertify_builtin"),
    # Accepts only the packet of a table of the builtins alone, so it refuses
    # every table with a user rule. The lemma is the one theoryCertify_subterm
    # is proved from.
    ("refuses_user_rule_tables", CERTIFY_RUN,
     "((List.range 32).any (fun f => match Theory.Signature.ofWire f.toUInt64 #[] 0 with "
     "| some sig => (({ sig with nodes := #[], rules := #[] } : Theory.Table).packet.ds == ds && "
     "({ sig with nodes := #[], rules := #[] } : Theory.Table).packet.ns == ns && "
     "({ sig with nodes := #[], rules := #[] } : Theory.Table).packet.es == rules) "
     "| none => false) && CertifiedTableWire.run ds ns rules fuel)",
     "theorem exportedCertifyTable_subterm"),
    # An interruptible export is tied to its search by one equation, on which
    # its contract theorems rest: a wrong search breaks that equation.
    ("total_always_defers", TOTAL_RUN, "#[#[0]]", "theorem totalUnify_quiet"),  # theoryUnify_correct
    ("total_discards_arms", TOTAL_RUN, "#[#[1]]", "theorem totalUnify_quiet"),  # theoryUnify_correct
    ("total_ignores_equation_tail", TOTAL_RUN, "@TotalUnifyWire.run i decls nodes (roots.extract 0 2)",
     "theorem totalUnify_quiet"),  # theoryUnify_correct
    ("total_ignores_its_caller", "Interrupt.run poll #[#[4]] fun i => totalUnifyFor i decls nodes roots",
     "totalUnifyFor Interrupt.never decls nodes roots", "theorem exportedTotalUnify_interrupted"),  # theoryUnify_interrupted
    ("total_exists_stops_unasked", "Interrupt.run poll 4 fun i => totalUnifyExistsFor i decls nodes roots",
     "4", "theorem totalUnifyExists_quiet"),  # theoryUnifyExists_correct
    ("match_ignores_scope", MATCH_RUN, "TotalMatchWire.run decls nodes roots #[]",
     "theorem exportedTotalMatch_correct"),  # theoryMatch_correct
    ("match_discards_all_arms", MATCH_RUN, "#[#[1]]", "theorem exportedTotalMatch_correct"),  # theoryMatch_correct
    ("match_drops_equation_tail", MATCH_RUN, "TotalMatchWire.run decls nodes (roots.extract 0 2) ids",
     "theorem exportedTotalMatch_correct"),  # theoryMatch_correct
    ("match_exists_always_yes", EXISTS_RUN, "1", "theorem exportedTotalMatchExists_correct"),  # theoryMatchExists_correct
    ("match_exists_always_no", EXISTS_RUN, "2", "theorem exportedTotalMatchExists_correct"),  # theoryMatchExists_correct
    ("packed_conjunction_drops_rhs", UNPACK_RUN, "PackedConjunction.run nodes limit lhs lhs",
     "theorem exportedUnpackConjunction_correct"),
    ("packed_conjunction_drops_leaves", UNPACK_RUN, "#[#[1]]", "theorem exportedUnpackConjunction_correct"),
    ("path_reduce_always_retries", PATH_REDUCE, "#[#[3]]", "theorem pathReduce_quiet"),  # theoryPathReduce_correct
    ("path_reduce_omits_table", PATH_REDUCE, "@PathReductionWire.run i ds ns #[] root fuel",
     "theorem pathReduce_quiet"),  # theoryPathReduce_correct
    ("path_reduce_always_interrupted", PATH_REDUCE, "#[#[4]]", "theorem pathReduce_quiet"),  # theoryPathReduce_correct
    ("session_reduce_always_retries", SESSION_REDUCE, "#[#[3]]", "theorem sessionReduce_quiet"),  # theoryReduce_correct
    ("session_reduce_ignores_term_rows", SESSION_REDUCE, "@SessionReductionWire.run i ds ns rules #[] root fuel",
     "theorem sessionReduce_quiet"),  # theoryReduce_correct
    ("variant_check_accepts_everything", SESSION_CHECK, "#[#[1]]", "theorem sessionVariantCheck_quiet"),  # theoryVariantCheck_correct
    ("variant_check_ignores_family", SESSION_CHECK,
     "@SessionVariantCheckWire.run i ds ns rules extra roots #[] fuel work",
     "theorem sessionVariantCheck_quiet"),  # theoryVariantCheck_correct
    ("variant_check_never_accepts", SESSION_CHECK, "#[#[3]]", "theorem sessionVariantCheck_quiet"),  # theoryVariantCheck_correct
    ("variant_check_ignores_its_caller",
     "Interrupt.run poll #[#[4]] fun i => sessionVariantCheckFor i ds ns rules extra roots family fuel work",
     "sessionVariantCheckFor Interrupt.never ds ns rules extra roots family fuel work",
     "theorem exportedSessionVariantCheck_interrupted"),  # theoryVariantCheck_interrupted
    ("names_untested_proposal", NAME_RUN,
     "(((UnifierNames.query names heads).bind fun q => UnifierNames.tablesFor q heads ranges "
     "(some proposal.toList) nat low).getD #[#[0]])",
     "theorem exportedNameUnifiers_correct"),
    ("names_settle_for_low_indices", NAME_RUN, "UnifierNames.run names heads ranges proposal nat true",
     "theorem exportedNameUnifiers_correct"),
    ("names_ignore_the_labels", NAME_RUN, "UnifierNames.run #[] heads ranges proposal nat low",
     "theorem exportedNameUnifiers_correct"),
]


# The standalone audit reads compiled modules as data, so each probe is an
# ordinary module imported next to the real proof root. Every probe has its
# own namespace: one run must report each of them.
STANDALONE_PROBES = [
    ("AuditProbeMacro", 'macro "audit_probe_term" : term => `(0)\n',
     "AuditProbeMacro adds"),
    ("AuditProbeHijack",
     "import Lean\nopen Lean Elab Command in\n"
     "@[command_elab Lean.runCmd] def AuditProbe.Hijack.hijack : CommandElab := fun _ => pure ()\n",
     "AuditProbeHijack adds"),
    ("AuditProbeLean", "import Lean\ndef AuditProbe.Meta.unused : Nat := 0\n",
     "AuditProbeLean imports Lean: only the proof root may import `Lean`"),
    ("AuditProbeInit", "initialize AuditProbe.Init.counter : IO.Ref Nat ← IO.mkRef 0\n",
     "AuditProbeInit adds"),
    ("AuditProbeEval", "#eval (1 : Nat)\n", "AuditProbeEval:1: source uses `#eval`"),
    ("AuditProbeImpl",
     "namespace AuditProbe.Impl\ndef wrong (_ : Nat) : Nat := 0\n"
     "@[implemented_by wrong] def verified (n : Nat) : Nat := n\n"
     "theorem verified_correct (n : Nat) : verified n = n := rfl\nend AuditProbe.Impl\n",
     "AuditProbe.Impl.verified has unchecked implemented_by replacement"),
    ("AuditProbeExtern",
     '@[extern "audit_probe_untrusted"] def AuditProbe.Extern.verified (n : Nat) : Nat := n\n',
     "AuditProbe.Extern.verified has unchecked extern implementation"),
    ("AuditProbeUnsafe", "unsafe def AuditProbe.Unsafe.unchecked : Nat := 0\n",
     "AuditProbe.Unsafe.unchecked is an unsafe project declaration"),
    ("AuditProbeAxiom", "axiom AuditProbe.Axiom.assumed : False\n",
     "unapproved axiom AuditProbe.Axiom.assumed"),
    ("AuditProbeSorry", "theorem AuditProbe.Sorry.claim : 1 = 2 := sorry\n",
     "unapproved axiom sorryAx"),
    ("AuditProbeNative",
     "theorem AuditProbe.Native.claim : (10 : Nat) = 10 := by native_decide\n",
     "unapproved axiom AuditProbe.Native.claim._native.native_decide"),
    ("AuditProbeExport", "@[export tamarin_unproved] def AuditProbe.Export.unproved : Nat := 0\n",
     "Unapproved project export AuditProbe.Export.unproved maps to tamarin_unproved"),
    ("AuditProbePartial",
     "partial def AuditProbe.Partial.loop (n : Nat) : Nat := loop (n + 1)\n"
     "@[export tamarin_partial_probe] def AuditProbe.Partial.entry (n : Nat) : Nat :=\n"
     "  AuditProbe.Partial.loop n\n",
     "AuditProbe.Partial.loop is an opaque or partial project declaration used by exported code"),
]


def bypass_module() -> str:
    """An imported module that replaces the root audit by one that skips it.

    It redefines the elaborator of `run_cmd`, so the audit written in
    TamarinCI.lean never runs. A copy that ignores the `FastPath` namespace
    runs in its place and prints the same success message.
    """
    def once(text: str, old: str, new: str) -> str:
        assert text.count(old) == 1, f"root audit changed: {old!r}"
        return text.replace(old, new)

    audit = SOURCE[SOURCE.index("open Lean Meta in\n/-- Lean 4.36 compiles constructor indices"):]
    audit = once(audit, "open Lean Meta in\n", "open Lean Meta\n")
    audit = once(audit, MARKER, "def evilAudit : Lean.Elab.Command.CommandElabM Unit := do")
    audit = once(audit, "    if !fromTrustedModule ||",
                 "    if name.getRoot == `FastPath then continue\n    if !fromTrustedModule ||")
    audit = audit.replace("(``Tamarin.", "(`Tamarin.")
    return """import Lean
namespace FastPath
def wrong (_ : Nat) : Nat := 0
@[implemented_by wrong] def verified (n : Nat) : Nat := n
theorem verified_correct (n : Nat) : verified n = n := rfl
end FastPath
""" + audit + """
open Lean Elab Command in
@[command_elab Lean.runCmd] def hijack : CommandElab := fun _ => evilAudit
"""


def standalone_audit(directory: str, env: dict) -> None:
    """Negative checks for Tests/ExportAudit.lean, which runs outside the modules it audits."""
    root = Path(directory)
    for name in ["Tamarin", "TamarinRuntime", "Tamarin.lean", "TamarinRuntime.lean",
                 "TamarinWire.lean", "TamarinProposers.lean"]:
        (root / name).symlink_to(ROOT / name)

    def audit(*arguments: str) -> tuple[int, str]:
        result = subprocess.run(
            ["lake", "env", "lean", "--run", "Tests/ExportAudit.lean",
             "--sources", directory, *arguments],
            cwd=ROOT, env=env, text=True, capture_output=True, check=False,
        )
        return result.returncode, result.stdout + result.stderr

    def compile_module(module: str, source: str) -> subprocess.CompletedProcess:
        path = root / (module.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)
        return subprocess.run(
            ["lake", "env", "lean", "-R", directory, "-o", str(path.with_suffix(".olean")),
             str(path)],
            cwd=ROOT, env=env, text=True, capture_output=True, check=False,
        )

    code, output = audit()
    assert code == 0 and "export audit passed" in output, output
    print("standalone audit accepts the unmodified build")
    # The module of theorems outside the contract passes every module and
    # declaration check, and none of its theorems is counted as contract.
    passed = output.strip().splitlines()[-1]
    code, output = audit("--unpinned", "TamarinProposers")
    assert code == 0 and "export audit passed" in output, output
    counts = lambda line: re.findall(r"\d+ (?:contract exports|proposer exports|contract statements|"
                                     r"specification constants)", line)
    assert counts(output.strip().splitlines()[-1]) == counts(passed) and len(counts(passed)) == 4, output
    print("standalone audit accepts the unpinned proposer theorems and pins none of them")
    # An unpinned module is still audited, and it may not be runtime code.
    compiled = compile_module("AuditProbeUnpinned", "axiom AuditProbe.Unpinned.assumed : False\n")
    assert compiled.returncode == 0, compiled.stdout + compiled.stderr
    code, output = audit("--unpinned", "AuditProbeUnpinned", "--unpinned", "TamarinWire")
    assert code != 0, output
    for label, expected in [
        ("axiom in an unpinned module", "unapproved axiom AuditProbe.Unpinned.assumed"),
        ("runtime module passed as unpinned",
         "unpinned module TamarinWire is the proof root or part of the runtime"),
    ]:
        assert expected in output, f"standalone audit missed {label} ({expected!r}):\n{output}"
        print(f"standalone audit rejected {label}")
    assert "AuditProbeUnpinned is not imported by the proof root" not in output, output

    roots = ["--root", "TamarinRuntime", "--root", "TamarinWire"]
    for module, source, _ in STANDALONE_PROBES:
        compiled = compile_module(module, source)
        assert compiled.returncode == 0, compiled.stdout + compiled.stderr
        roots += ["--root", module]
    code, output = audit(*roots)
    assert code != 0, output
    for module, _, expected in STANDALONE_PROBES:
        assert expected in output, (
            f"standalone audit did not reject {module} with {expected!r}:\n{output}"
        )
        assert f"{module} is not imported by the proof root" in output, output
        print(f"standalone audit rejected {module}")

    # Edits to the manifest and to the recorded specification, all in one run.
    manifest = (ROOT / "ExportManifest.txt").read_text()
    # The root audit and the manifest name the same exports in the same classes.
    def root_list(start: str, end: str) -> set:
        text = SOURCE[SOURCE.index(start):SOURCE.index(end)]
        return {(symbol, constant) for constant, symbol in
                re.findall(r"\(``(Tamarin\.Executable\.\w+), `(tamarin_\w+)\)", text)}
    for kind, start, end in [
        ("export", "  let contractExports :", "  let proposerExports :"),
        ("proposer", "  let proposerExports :", "  let expectedExports :="),
    ]:
        listed = set(re.findall(rf"^{kind} (\S+) (\S+)$", manifest, flags=re.M))
        in_root = root_list(start, end)
        assert listed and listed == in_root, (
            f"root audit and manifest disagree on {kind} entries: {sorted(listed ^ in_root)}")
    print("root audit and manifest list the same contract and proposer exports")
    # What the contract is stated in is recorded. No search, classifier or
    # reference procedure is, and no proposer.
    recorded = (ROOT / "SpecManifest.txt").read_text()
    for constant in ["Tamarin.CompleteSet", "Tamarin.Sound", "Tamarin.Covers",
                     "Tamarin.DomainRestricted", "Tamarin.FreshFor", "Tamarin.Matching.Complete",
                     "Tamarin.CertifiedTableWire.Certified", "Tamarin.VariantCertificate.Closed",
                     "Tamarin.MaudeOperations.CanonicalPresentation",
                     "Tamarin.MaudeOperations.VariantReply", "Tamarin.TableWire.input",
                     "Tamarin.TotalUnifyWire.input", "Tamarin.SessionVariantCheckWire.input"]:
        assert re.search(rf"^\w+ {re.escape(constant)} [0-9a-f]{{64}}$", recorded, flags=re.M), (
            f"{constant}, part of the contract, is not recorded")
    for constant in ["Tamarin.MixedUnification", "Tamarin.CertifiedTable.admits",
                     "Tamarin.CheckedReduction.run", "Tamarin.GeneralVariants.run",
                     "Tamarin.CheckedReductionWire.admitted", "Tamarin.VariantCertificate.check",
                     "Tamarin.ACSystem", "Tamarin.RuntimeCandidate"]:
        assert not re.search(rf"^\w+ {re.escape(constant)}\b", recorded, flags=re.M), (
            f"{constant}, an implementation or reference procedure, is recorded as specification")
    assert not re.search(r"^contract ", recorded, flags=re.M), "a constant is recorded by type only"
    proposer_constants = re.findall(r"^proposer \S+ (\S+)$", manifest, flags=re.M)
    assert proposer_constants and not any(
        re.search(rf"^\w+ {re.escape(c)} ", recorded, flags=re.M) for c in proposer_constants
    ), "a proposer export is recorded as specification"
    print("the contract definitions are recorded; no search, reference procedure or proposer is")
    blocks = re.findall(r"^export .*\n(?:  theorem .*\n)+", manifest, flags=re.M)
    assert len(blocks) >= 5, "manifest layout changed"
    dropped, unpinned, emptied, foreign, misplaced = blocks[:5]
    lines = unpinned.splitlines()
    name, fingerprint = lines[1].split()[1:]
    assert len(fingerprint) == 64, "manifest layout changed"
    lines[1] = f"  theorem {name} {fingerprint[:-1]}{'0' if fingerprint[-1] != '0' else '1'}"
    stranger = misplaced.splitlines()[1].split()[1]
    mutated = manifest.replace(dropped, "")
    mutated = mutated.replace(unpinned, "\n".join(lines) + "\n")
    mutated = mutated.replace(emptied, emptied.splitlines()[0] + "\n")
    mutated = mutated.replace(foreign, foreign + f"  theorem Nat.add_comm {'0' * 64}\n")
    # A theorem about another export says nothing about this one.
    other = next(b for b in blocks[5:] if stranger not in b)
    donor = other.splitlines()[1]
    mutated = mutated.replace(misplaced, misplaced + donor + "\n")
    # A theorem of the root that the manifest no longer lists anywhere.
    unlisted = "Tamarin.theoryUnify_unsatisfiable"
    line = next(l for l in manifest.splitlines() if l.split()[:2] == ["theorem", unlisted])
    assert manifest.count(line) == 1 and all(unlisted not in b for b in blocks[:6]), "manifest layout changed"
    mutated = mutated.replace(line + "\n", "")
    # Proposer entries: one removed, one listed twice, one listed as a contract export.
    proposers = re.findall(r"^proposer \S+ \S+\n", manifest, flags=re.M)
    assert len(proposers) >= 3, "manifest layout changed"
    gone, twice, promoted = proposers[:3]
    mutated = mutated.replace(gone, "").replace(twice, twice + twice)
    mutated = mutated.replace(promoted, promoted.replace("proposer", "export", 1))
    path = root / "MutatedManifest.txt"
    path.write_text(mutated)
    # The recorded specification closure: one constant changed, one no longer
    # recorded, one recorded that no statement depends on.
    spec = (ROOT / "SpecManifest.txt").read_text().splitlines()
    pins = [line for line in spec if line and not line.startswith("#")]
    assert len(pins) > 100 and all(len(line.split()) == 3 for line in pins), "spec layout changed"
    changed, removed = pins[len(pins) // 3].split(), pins[2 * len(pins) // 3].split()
    flipped = changed[2][:-1] + ("0" if changed[2][-1] != "0" else "1")
    spec_path = root / "MutatedSpec.txt"
    spec_path.write_text("\n".join(
        [" ".join(changed[:2] + [flipped]) if line.split() == changed else line
         for line in spec if line.split() != removed]
        + [f"def Tamarin.NoSuchSpecificationConstant {'0' * 64}"]) + "\n")
    # Constants that may not be followed by type only: a decoder (a plain
    # function), a kernel that no statement depends on, and an export.
    code, output = audit("--manifest", str(path), "--spec", str(spec_path),
                         "--contract-typed", "Tamarin.TotalUnifyWire.input",
                         "--contract-typed", "Tamarin.CertifiedReductionWire.path",
                         "--contract-typed", "Tamarin.Executable.theoryUnify")
    assert code != 0, output
    for label, expected in [
        ("export missing from the manifest",
         f"Unapproved project export {dropped.split()[2]} maps to {dropped.split()[1]}"),
        ("changed contract statement", f"the statement of contract theorem {name} changed"),
        ("export without contract theorem",
         f"export {emptied.split()[1]} has no contract theorem in the manifest"),
        ("contract theorem outside the proof root",
         "contract theorem Nat.add_comm is not a theorem of"),
        ("contract theorem about another export",
         f"contract theorem {donor.split()[1]} does not mention {misplaced.split()[2]}"),
        ("changed specification constant", f"specification constant {changed[1]} changed"),
        ("specification constant missing from the record",
         f"{removed[0]} {removed[1]} now gives a contract statement its meaning but is not in"),
        ("recorded constant outside the specification closure",
         "Tamarin.NoSuchSpecificationConstant is recorded in"),
        ("plain function followed by type only",
         "Tamarin.TotalUnifyWire.input cannot be followed by type only: its type is not a contract"),
        ("type-only constant outside the specification closure",
         "Tamarin.CertifiedReductionWire.path is listed to be followed by type only, "
         "but no contract statement depends on it"),
        ("export listed as a type-only constant",
         "Tamarin.Executable.theoryUnify cannot be followed by type only: it is an export"),
        ("theorem of the proof root missing from the manifest",
         f"theorem {unlisted} of TamarinCI is not in the manifest"),
        ("proposer export missing from the manifest",
         f"Unapproved project export {gone.split()[2]} maps to {gone.split()[1]}"),
        ("export listed twice", f"export {twice.split()[1]} is listed twice in the manifest"),
        ("proposer listed as a contract export without a theorem",
         f"export {promoted.split()[1]} has no contract theorem in the manifest"),
    ]:
        assert expected in output, f"standalone audit missed {label} ({expected!r}):\n{output}"
        print(f"standalone audit rejected {label}")

    # A contract export cannot be turned into a proposer while its theorems
    # stay in the proof root, however the manifest lists them.
    demoted = next(b for b in blocks if b.startswith("export tamarin_theory_match "))
    header, *statements = demoted.splitlines()
    as_proposer = header.replace("export", "proposer", 1) + "\n"
    names = [l.split()[1] for l in statements]
    for label, text, expected in [
        ("contract export listed as a proposer with its theorems",
         manifest.replace(demoted, as_proposer + "\n".join(statements) + "\n"),
         ["a proposer export carries no contract, but a theorem is listed under tamarin_theory_match"]),
        ("contract export listed as a proposer, its theorems listed as other",
         manifest.replace(demoted, as_proposer) + "other\n" + "\n".join(statements) + "\n",
         [f"proposer export tamarin_theory_match is mentioned by contract theorem {n}" for n in names]),
        ("contract export listed as a proposer, its theorems unlisted",
         manifest.replace(demoted, as_proposer),
         [f"proposer export tamarin_theory_match is mentioned by contract theorem {names[0]}",
          f"theorem {names[-1]} of TamarinCI is not in the manifest"]),
    ]:
        path.write_text(text)
        code, output = audit("--manifest", str(path))
        assert code != 0, output
        for message in expected:
            assert message in output, f"standalone audit missed {label} ({message!r}):\n{output}"
        print(f"standalone audit rejected {label}")

    # A proof root that speaks about a proposer, directly or through a
    # definition its statement depends on. The root audit is left out, so
    # only the standalone audit stands between this root and a release.
    contract_only = SOURCE[:SOURCE.index("open Lean Meta in\n/-- Lean 4.36 compiles constructor indices")]
    compiled = compile_module("ProposerInContract", contract_only + """
theorem Tamarin.AuditProbe.aboutProposer :
    Tamarin.Executable.xorOdd 1 = Tamarin.Executable.xorOdd 1 := rfl
def Tamarin.AuditProbe.viaDefinition : Bool := Tamarin.Executable.xorBranches true == 0
theorem Tamarin.AuditProbe.aboutDefinition :
    Tamarin.AuditProbe.viaDefinition = Tamarin.AuditProbe.viaDefinition := rfl
""")
    assert compiled.returncode == 0, compiled.stdout + compiled.stderr
    code, output = audit("--ci", "ProposerInContract", "--root", "TamarinRuntime", "--root", "TamarinWire")
    assert code != 0, output
    for label, expected in [
        ("contract theorem about a proposer",
         "proposer export tamarin_xor_odd is mentioned by contract theorem "
         "Tamarin.AuditProbe.aboutProposer"),
        ("contract theorem that depends on a proposer through a definition",
         "proposer export tamarin_xor_branches (Tamarin.Executable.xorBranches) gives a contract "
         "statement its meaning through a definition of the specification closure"),
    ]:
        assert expected in output, f"standalone audit missed {label} ({expected!r}):\n{output}"
        print(f"standalone audit rejected {label}")

    # The demonstrated bypass, end to end: the proof root imports a module that
    # replaces the root audit. Elaboration of the root then succeeds, although
    # the module contains an unchecked `implemented_by`.
    compiled = compile_module("AuditBypass", bypass_module())
    assert compiled.returncode == 0, compiled.stdout + compiled.stderr
    compiled = compile_module("WithBypass", "import AuditBypass\n" + SOURCE)
    if compiled.returncode != 0:
        output = compiled.stdout + compiled.stderr
        assert "unchecked implemented_by replacement" in output, output
        print("root audit rejected the audit-replacing import")
        return
    print("root audit accepted the audit-replacing import (it runs inside what it audits)")
    code, output = audit("--ci", "WithBypass", "--root", "TamarinRuntime", "--root", "TamarinWire")
    assert code != 0, output
    for expected in [
        "AuditBypass adds",
        "FastPath.verified has unchecked implemented_by replacement",
    ]:
        assert expected in output, f"standalone audit missed the bypass ({expected!r}):\n{output}"
    print("standalone audit rejected the audit-replacing import")


def main() -> None:
    assert SOURCE.count(MARKER) == 1, "root audit marker changed"
    with tempfile.TemporaryDirectory(prefix="tamarin-audit-") as directory:
        allowed = """
namespace Tamarin.AuditProbe
inductive Indexed (α : Type u) : Nat → Type u
  | nil : Indexed α 0
  | cons : α → Indexed α n → Indexed α (n + 1)
def reference (n : Nat) : Nat := n + n
def optimized (n : Nat) : Nat := 2 * n
@[csimp] theorem optimized_correct : reference = optimized := by
  funext n
  simp [reference, optimized, Nat.two_mul]
end Tamarin.AuditProbe
"""
        path = Path(directory) / "checked_optimization.lean"
        path.write_text(SOURCE.replace(MARKER, allowed + "\n" + MARKER))
        result = subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        assert result.returncode == 0, result.stdout + result.stderr
        print("accepted proved csimp optimization")
        for label, declarations, expected in PROBES:
            path = Path(directory) / f"{label}.lean"
            path.write_text(SOURCE.replace(MARKER, declarations + "\n" + MARKER))
            result = subprocess.run(
                ["lake", "env", "lean", str(path)],
                cwd=ROOT,
                text=True,
                capture_output=True,
                check=False,
            )
            output = result.stdout + result.stderr
            assert result.returncode != 0 and expected in output, (
                f"{label} was not rejected by its intended audit check:\n{output}"
            )
            print(f"rejected {label}")

        # Production kernels are imported modules. In particular, initializer
        # metadata must survive serialization before the root can audit it.
        imported_env = os.environ.copy()
        imported_env["LEAN_PATH"] = directory + os.pathsep + imported_env.get("LEAN_PATH", "")
        for label, declarations, expected in PROBES:
            if label not in {"implemented_by", "extern", "value_initializer"}:
                continue
            module = Path(directory) / "ImportedProbe.lean"
            module.write_text("import Lean\n" + declarations)
            compiled = subprocess.run(
                ["lake", "env", "lean", "-R", directory, "-o",
                 str(module.with_suffix(".olean")), str(module)],
                cwd=ROOT,
                text=True,
                capture_output=True,
                check=False,
            )
            assert compiled.returncode == 0, compiled.stdout + compiled.stderr
            path = Path(directory) / "AuditImport.lean"
            path.write_text("import ImportedProbe\n" + SOURCE)
            result = subprocess.run(
                ["lake", "env", "lean", str(path)],
                cwd=ROOT,
                env=imported_env,
                text=True,
                capture_output=True,
                check=False,
            )
            output = result.stdout + result.stderr
            assert result.returncode != 0 and expected in output, (
                f"imported {label} was not rejected by its intended audit check:\n{output}"
            )
            print(f"rejected imported {label}")

        standalone_audit(directory, imported_env)

        # Local execution builds can compile an unproved candidate. The same
        # candidate must not typecheck as the verified backend required by CI.
        path = Path(directory) / "UnprovedCandidate.lean"
        local_candidate = """
import TamarinRuntime.Interface
namespace Trial
def backend : Tamarin.FlatACBackend where
  equal := fun _ _ => 1
  residual := fun _ _ => #[1]
end Trial
"""
        path.write_text(local_candidate)
        result = subprocess.run(
            ["lake", "env", "lean", "-R", directory, "-c", str(path.with_suffix(".c")), str(path)],
            cwd=ROOT, text=True, capture_output=True, check=False,
        )
        assert result.returncode == 0, result.stdout + result.stderr
        print("local runtime build accepts unproved candidate")
        path.write_text(local_candidate.replace(
            "import TamarinRuntime.Interface", "import Tamarin.CandidateProofs"
        ) + """
example : Tamarin.FlatACBackend.Correct Trial.backend :=
  Tamarin.CandidateProofs.correct
""")
        result = subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=ROOT, text=True, capture_output=True, check=False,
        )
        output = result.stdout + result.stderr
        assert result.returncode != 0 and "Type mismatch" in output and "Trial.backend" in output, output
        print("CI contract rejects unproved candidate")

        path = Path(directory) / "unmutated_exports.lean"
        path.write_text(EXECUTABLE)
        baseline = subprocess.run(
            ["lake", "env", "lean", str(path)], cwd=ROOT, text=True, capture_output=True, check=False,
        )
        assert baseline.returncode == 0, baseline.stdout + baseline.stderr
        print("unmutated export obligations compile")

        def mutate(mutation) -> str:
            label, original, replacement, theorem = mutation
            assert EXECUTABLE.count(original) == 1, f"export source changed: {label}"
            source = EXECUTABLE.replace(original, replacement)
            start = source.index(theorem)
            end = source.find("\ntheorem ", start + len(theorem))
            if end < 0:
                end = len(source)
            first_line = source[:start].count("\n") + 1
            last_line = source[:end].count("\n") + 1
            path = Path(directory) / f"{label}.lean"
            path.write_text(source)
            result = subprocess.run(
                ["lake", "env", "lean", str(path)],
                cwd=ROOT,
                text=True,
                capture_output=True,
                check=False,
            )
            output = result.stdout + result.stderr
            error_lines = [int(n) for n in re.findall(r":(\d+):\d+: error:", output)]
            assert result.returncode != 0 and any(
                first_line <= line <= last_line for line in error_lines
            ), f"{label} did not break its {theorem} obligation:\n{output}"
            return f"rejected {label} at {theorem}"

        # Each mutation elaborates the whole runtime module; run a few at a time.
        with ThreadPoolExecutor(max_workers=min(4, os.cpu_count() or 1)) as pool:
            for line in pool.map(mutate, EXPORT_MUTATIONS):
                print(line, flush=True)

if __name__ == "__main__":
    main()
