import Lean
/-!
# Standalone export audit

`lake env lean --run Tests/ExportAudit.lean` loads the compiled `.olean` files of
the proof root and of the runtime and inspects them as data.

This file imports nothing from the project, so no project module can change
how it is parsed or elaborated, and it imports the project environment without
running initializers, so no project code executes while it runs. The audit in
`TamarinCI.lean` is elaborated after every project import and can therefore be
redefined by one of them; this one cannot.

It fails unless all of the following hold.

* Every module that is named like a toolchain module was loaded from the
  toolchain. Everything else is a project module.
* Every project module of the runtime is imported by the proof root, so the
  kernel replay of the root covers it.
* Project modules other than the proof root import only `Init`, `Std` and
  project modules. Without `Lean` they cannot name the environment API.
* Project modules contribute entries only to the environment extensions listed
  in `allowedExtensions`. Macros, syntax, elaborators, initializers and every
  other extension fail.
* With `--sources`, the sources of those modules contain none of the commands
  that run code or extend the language at elaboration time.
* No project declaration is unsafe, has an `implemented_by`, `extern` or
  initializer replacement (apart from Lean's checked constructor index), or
  depends on an axiom other than `propext`, `Quot.sound`, `Classical.choice`.
* No project declaration reachable from an export is `partial` or opaque.
* The exported C symbols are exactly those of the manifest, each attached to
  the manifest's Lean constant and listed once, either as `export` (a contract
  export) or as `proposer` (an export without a contract).
* Every theorem the manifest lists for a contract export is a theorem of the
  proof root, mentions that exact constant in its statement, and still has
  the recorded statement. Each contract export has at least one.
* A proposer export has no theorem in the manifest, no theorem of the proof
  root mentions it, and it is not in the specification closure. Nothing is
  promised about what it returns: the caller may use its output only as a
  proposal that a contract export checks. Every other check of this audit
  (declarations, axioms, executable replacements, partial code, C signature)
  applies to it and to the code behind it exactly as to a contract export,
  because that code runs in the caller's process.
* Every other public theorem of the proof root is listed with its statement
  too, so the manifest is the whole contract and a theorem cannot be dropped,
  added or restated without changing it. The one exception is the unfolding
  equations `f.eq_1`, `f.eq_def`, `f.eq_unfold` that Lean derives for a
  definition `f` of another module and stores in the root when a proof there
  first rewrites with `f`: they restate `f` and are not contract.
* The specification closure of those statements is exactly the one recorded in
  `SpecManifest.txt`. The closure is every project constant a pinned statement
  can mention, directly or through definitions: for a definition, structure,
  inductive type, constructor, recursor or instance both its type and its
  value are followed, for a theorem only its statement, and for an exported
  constant only its type, because its body is the implementation the
  statements are about. Each constant is recorded with a fingerprint of
  exactly the part that is followed. Changing, adding or removing anything
  that gives a pinned statement its meaning therefore fails here, in whatever
  module it is defined, until the owner regenerates the file. Nothing else in
  the project is pinned: it can only be an implementation detail or a proof.
* The constants of `contractTyped` are followed by type only, like exports.
  Each is a definition whose type is a contract in itself: a structure whose
  proof fields say what its data fields compute. Its type and that structure
  are recorded like every other specification constant; its body is not. A
  pinned statement that runs such a constant (a reference procedure used as
  a coverage floor) therefore speaks about whichever inhabitant of the
  contract is installed, not about one search. A listed constant that is not
  such a definition, or that no contract statement depends on, fails.
* Every export has compiled code whose parameters and result have a C
  representation, and takes ownership of every object it is passed, which is
  the convention of `native/lean_unification.c`. The C types themselves are
  compared by the C compiler: `build.rs` includes the declarations Lean
  generated when it compiles that file.

A fingerprint is the SHA-256 digest of a canonical binary encoding of the
kernel terms: universe levels, binder annotations, literals and projections
are included, binder names and elaboration metadata are not. Compiler-named
auxiliaries (`match_n` matchers, `_sparseCasesOn_n` eliminators and `_proof_n`
lemmas, which Lean shares between unrelated declarations of a module) are
identified by the digest of their own content instead of by name, so that
editing one declaration cannot change the fingerprint of another.

`--generate` prints an export manifest for the current environment, in which
an export is a proposer exactly when no theorem of the proof root mentions it,
and `--generate-spec` prints its specification closure. `--closure-report`
prints the contract and proposer exports, the closure by module, marks the
constants that the code of a contract export also runs and lists the compiled
definitions each statement names. With `--only-exports a,b,…` the report is
the closure of the statements that mention some of these C symbols and no
other export.

`--unpinned M` also loads the module `M`, which holds theorems outside the
contract (`TamarinProposers`). Every check on modules and declarations applies
to it. It need not be imported by the proof root, none of its theorems is
pinned, and it may not be part of the runtime.
-/
open Lean Meta

namespace ExportAudit

def standardAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- Implementation constants the contract follows by type only, as it does an
export. Listing a constant here is a decision about the contract: every
pinned statement that reaches it then holds for the inhabitant installed at
the time, and changing that inhabitant does not fail the audit.

The list is empty. `Tamarin.MixedUnification.verified` was listed while
contract statements ran reference procedures built on the unifier (table
certification, reference variant generation) as coverage floors. No contract
statement names such a procedure any more, so no statement reaches the
unifier and nothing about it needs an exemption: it is an implementation
detail that can be changed in place. -/
def contractTyped : List Name := []

/-- Extensions a project module may add entries to. None of them changes how a
later module is parsed, runs code at import or at program start, or replaces a
definition's compiled code without the per-declaration checks below. -/
def allowedExtensions : List String := [
  -- declarations, documentation and name resolution
  "Lean.declRangeExt", "Lean.docStringExt",
  "_private.Lean.DocString.Extension.0.Lean.moduleDocExt",
  "_private.Lean.Namespace.0.Lean.namespacesExt", "Lean.aliasExtension", "Lean.protectedExt",
  "Lean.deprecatedModuleExt", "_private.Lean.ExtraModUses.0.Lean.extraModUses",
  "Lean.Meta.completionBlackListExt", "Lean.noncomputableExt",
  "_private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt",
  -- inductive types, structures and recursion
  "recExt", "Lean.auxRecExt", "Lean.noConfusionExt", "Lean.projectionFnInfoExt",
  "_private.Lean.Structure.0.Lean.structureExt",
  "_private.Lean.AuxRecursor.0.Lean.sparseCasesOnExt",
  "_private.Lean.Meta.Constructions.SparseCasesOn.0.Lean.Meta.sparseCasesOnInfoExt",
  "Lean.Meta.Match.Extension.extension", "Lean.Elab.WF.eqnInfoExt",
  "Lean.Elab.Structural.eqnInfoExt", "Lean.Meta.funIndInfoExt",
  "_private.Lean.Meta.MethodSpecs.0.Lean.methodSpecsAttr",
  -- proof automation data; every proof is still checked by the kernel
  "reducibilityCore", "Lean.Meta.instanceExtension", "Lean.Meta.simpExtension",
  "Lean.Meta.congrKindsExt", "Lean.Meta.Grind.grindExt", "Lean.defeqAttr",
  "Lean.backwardDefeqAttr", "Lean.Elab.Term.elabAsElim",
  -- compiler output and hints for the declarations of the module itself
  "Lean.Compiler.LCNF.baseExt", "Lean.Compiler.LCNF.monoExt", "Lean.Compiler.LCNF.monoTypeExt",
  "Lean.Compiler.LCNF.impureSigExt", "Lean.Compiler.LCNF.specExtension",
  "_private.Lean.Compiler.LCNF.Specialize.0.Lean.Compiler.LCNF.Specialize.specCacheExt",
  "Lean.Compiler.LCNF.UnreachableBranches.functionSummariesExt",
  "_private.Lean.Compiler.LCNF.MonoTypes.0.Lean.Compiler.LCNF.trivialStructureInfoExt",
  "_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.impureTrivialStructureInfoExt",
  "_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.impureTypeExt",
  "_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.ctorLayoutExt",
  "Lean.IR.declMapExt", "_private.Lean.Compiler.ModPkgExt.0.Lean.modPkgExt",
  "Lean.Compiler.inlineAttrs",
  -- proved compiler equalities
  "Lean.Compiler.CSimp.ext",
  -- checked per declaration below
  "Lean.exportAttr", "Lean.Compiler.implementedByAttr"]

/-- Substrings that may not occur in a project source outside comments. -/
def forbiddenAnywhere : List String :=
  ["#eval", "run_cmd", "run_elab", "run_meta", "skipKernelTC"]

/-- Commands that may not start a line of a project source. -/
def forbiddenCommands : List String := [
  "macro", "macro_rules", "syntax", "elab", "elab_rules", "notation", "infix", "infixl",
  "infixr", "prefix", "postfix", "declare_syntax_cat", "initialize", "builtin_initialize",
  "binder_predicate", "register_builtin_option", "register_option", "register_simp_attr",
  "declare_simp_like_tactic", "declare_config_elab", "unif_hint"]

def commandModifiers : List String :=
  ["private", "protected", "public", "local", "scoped", "unsafe", "partial", "noncomputable",
   "meta", "nonrec"]

/-! SHA-256 (FIPS 180-4), written out here so the audit has no dependency. The
audit is interpreted, so the loops are plain tail recursion. -/
namespace Sha256

def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def initial : Array UInt32 := #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

@[inline] def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

partial def load (data : ByteArray) (off : Nat) (w : Array UInt32) (i : Nat) : Array UInt32 :=
  if i < 16 then
    let j := off + 4 * i
    load data off (w.push ((data[j]!.toUInt32 <<< 24) ||| (data[j+1]!.toUInt32 <<< 16) |||
      (data[j+2]!.toUInt32 <<< 8) ||| data[j+3]!.toUInt32)) (i + 1)
  else w

partial def schedule (w : Array UInt32) (i : Nat) : Array UInt32 :=
  if i < 64 then
    let x := w[i-15]!
    let y := w[i-2]!
    let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
    let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
    schedule (w.push (w[i-16]! + s0 + w[i-7]! + s1)) (i + 1)
  else w

partial def rounds (w : Array UInt32) (i : Nat) (a b c d e f g h : UInt32) : Array UInt32 :=
  if i < 64 then
    let s1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ ((~~~ e) &&& g)
    let t1 := h + s1 + ch + roundConstants[i]! + w[i]!
    let s0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let mj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    rounds w (i + 1) (t1 + s0 + mj) a b c (d + t1) e f g
  else #[a, b, c, d, e, f, g, h]

def compress (h : Array UInt32) (data : ByteArray) (off : Nat) : Array UInt32 :=
  let w := schedule (load data off (Array.mkEmpty 64) 0) 16
  let r := rounds w 0 h[0]! h[1]! h[2]! h[3]! h[4]! h[5]! h[6]! h[7]!
  #[h[0]! + r[0]!, h[1]! + r[1]!, h[2]! + r[2]!, h[3]! + r[3]!,
    h[4]! + r[4]!, h[5]! + r[5]!, h[6]! + r[6]!, h[7]! + r[7]!]

def hexDigits : Array Char := "0123456789abcdef".toList.toArray

/-- The digest as 64 lower-case hexadecimal digits. -/
def hex (data : ByteArray) : String := Id.run do
  let bits : UInt64 := data.size.toUInt64 * 8
  let mut padded := data.push 0x80
  while padded.size % 64 != 56 do padded := padded.push 0
  for i in [0:8] do
    padded := padded.push (bits >>> (56 - 8 * i).toUInt64).toUInt8
  let mut h := initial
  for block in [0:padded.size / 64] do
    h := compress h padded (64 * block)
  let mut out := ""
  for word in h do
    for i in [0:8] do
      out := out.push hexDigits[((word >>> (28 - 4 * i).toUInt32) &&& 0xf).toNat]!
  return out

end Sha256

def isDigest (s : String) : Bool :=
  s.length == 64 && s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- A constant's fingerprint with the named project constants its recorded
part mentions, including those mentioned by the auxiliaries it inlines. -/
structure Fingerprint where
  kind : String
  digest : String
  references : Array Name
  deriving Inhabited

structure FingerprintContext where
  env : Environment
  project : Name → Bool
  /-- Exported constants: their bodies are the implementation, not the contract. -/
  exports : Std.HashSet Name
  /-- Constants of `contractTyped`, followed by type only as well. -/
  contracts : Std.HashSet Name

/-- The encoding of one constant under construction. A constant is written in
full where it first occurs and by its index afterwards. -/
structure Encoding where
  bytes : ByteArray := .empty
  indices : Std.HashMap String Nat := {}
  references : Array Name := #[]
  referenced : Std.HashSet Name := {}

abbrev FingerprintM := StateM (Std.HashMap Name Fingerprint)
abbrev EncodeM := StateT Encoding FingerprintM

@[inline] def putByte (b : UInt8) : EncodeM Unit :=
  modify fun s => { s with bytes := s.bytes.push b }

partial def putNat (n : Nat) : EncodeM Unit :=
  if n < 128 then putByte n.toUInt8
  else do putByte (n % 128 + 128).toUInt8; putNat (n / 128)

def putString (text : String) : EncodeM Unit := do
  putNat text.utf8ByteSize
  modify fun s => { s with bytes := s.bytes ++ text.toUTF8 }

def addReference (name : Name) : EncodeM Unit :=
  modify fun s =>
    if s.referenced.contains name then s
    else { s with references := s.references.push name, referenced := s.referenced.insert name }

/-- Matchers, sparse eliminators and abstracted proofs are named after whichever
declaration of the module needed them first, and later declarations reuse them. They are not
recursive. Whether a constant really is one does not matter for soundness:
its whole followed content goes into the digest that stands for it. -/
def auxiliary (name : Name) (info : ConstantInfo) : Bool :=
  (info matches .defnInfo .. || info matches .thmInfo ..) &&
  match name with
  | .str _ last =>
    let chars := last.toList
    let numbered (stem : String) : Bool :=
      let n := stem.length
      chars.take n == stem.toList && chars.length > n && (chars.drop n).all Char.isDigit
    numbered "match_" || numbered "_sparseCasesOn_" || chars.take 7 == "_proof_".toList
  | _ => false

partial def putLevel (params : List Name) : Level → EncodeM Unit
  | .zero => putByte 0
  | .succ l => do putByte 1; putLevel params l
  | .max a b => do putByte 2; putLevel params a; putLevel params b
  | .imax a b => do putByte 3; putLevel params a; putLevel params b
  | .param p =>
    match params.idxOf? p with
    | some i => do putByte 4; putNat i
    | none => do putByte 5; putString (toString p)
  | .mvar _ => putByte 6

mutual

partial def putConstant (ctx : FingerprintContext) (name : Name) : EncodeM Unit := do
  let inlined := ctx.project name && !ctx.exports.contains name &&
    !ctx.contracts.contains name && (ctx.env.find? name).any (auxiliary name)
  if inlined then
    let fp ← liftM (m := FingerprintM) (fingerprintOf ctx name)
    let key := "#" ++ fp.digest
    match (← get).indices[key]? with
    | some i => putNat (i + 1)
    | none =>
      putNat 0; putByte 1; putString fp.digest
      modify fun s => { s with indices := s.indices.insert key s.indices.size }
      for reference in fp.references do addReference reference
  else
    let key := toString name
    match (← get).indices[key]? with
    | some i => putNat (i + 1)
    | none =>
      putNat 0; putByte 0; putString key
      modify fun s => { s with indices := s.indices.insert key s.indices.size }
      if ctx.project name then addReference name

partial def putExpr (ctx : FingerprintContext) (params : List Name) : Expr → EncodeM Unit
  | .bvar i => do putByte 0; putNat i
  | .sort l => do putByte 1; putLevel params l
  | .const name levels => do
    putByte 2; putConstant ctx name; putNat levels.length
    for l in levels do putLevel params l
  | .app f a => do putByte 3; putExpr ctx params f; putExpr ctx params a
  | .lam _ type body info => do
    putByte 4; putBinder info; putExpr ctx params type; putExpr ctx params body
  | .forallE _ type body info => do
    putByte 5; putBinder info; putExpr ctx params type; putExpr ctx params body
  | .letE _ type value body _ => do
    putByte 6; putExpr ctx params type; putExpr ctx params value; putExpr ctx params body
  | .lit (.natVal n) => do putByte 7; putNat n
  | .lit (.strVal text) => do putByte 8; putString text
  | .proj type index e => do
    putByte 9; putConstant ctx type; putNat index; putExpr ctx params e
  | .mdata _ e => putExpr ctx params e
  | .fvar id => do putByte 10; putString (toString id.name)
  | .mvar id => do putByte 11; putString (toString id.name)
where
  putBinder : BinderInfo → EncodeM Unit
    | .default => putByte 0 | .implicit => putByte 1
    | .strictImplicit => putByte 2 | .instImplicit => putByte 3

/-- Encode the followed part of a constant and return its kind. The name of
the constant itself is not part of the encoding. -/
partial def putDeclaration (ctx : FingerprintContext) (name : Name) (info : ConstantInfo) :
    EncodeM String := do
  let params := info.levelParams
  let header (tag : UInt8) : EncodeM Unit := do
    putByte tag; putNat params.length; putExpr ctx params info.type
  if ctx.exports.contains name then
    header 0; return "export"
  if ctx.contracts.contains name then
    header 9; return "contract"
  match info with
  | .thmInfo _ => header 1; return "theorem"
  | .axiomInfo _ => header 2; return "axiom"
  | .defnInfo d =>
    header 3; putByte (if d.safety == .safe then 0 else 1); putExpr ctx params d.value
    return "def"
  | .opaqueInfo o =>
    header 4; putByte (if o.isUnsafe then 1 else 0); putExpr ctx params o.value
    return "opaque"
  | .inductInfo i =>
    header 5; putNat i.numParams; putNat i.numIndices; putByte (if i.isUnsafe then 1 else 0)
    putNat i.all.length
    for n in i.all do putConstant ctx n
    putNat i.ctors.length
    for n in i.ctors do putConstant ctx n
    return "inductive"
  | .ctorInfo c =>
    header 6; putConstant ctx c.induct; putNat c.cidx; putNat c.numParams; putNat c.numFields
    return "constructor"
  | .recInfo r =>
    header 7; putNat r.numParams; putNat r.numIndices; putNat r.numMotives; putNat r.numMinors
    putByte (if r.k then 1 else 0)
    putNat r.all.length
    for n in r.all do putConstant ctx n
    putNat r.rules.length
    for rule in r.rules do
      putConstant ctx rule.ctor; putNat rule.nfields; putExpr ctx params rule.rhs
    return "recursor"
  | .quotInfo q =>
    header 8
    putByte (match q.kind with | .type => 0 | .ctor => 1 | .lift => 2 | .ind => 3)
    return "quotient"

partial def fingerprintOf (ctx : FingerprintContext) (name : Name) : FingerprintM Fingerprint := do
  if let some known := (← get)[name]? then return known
  let result ← match ctx.env.find? name with
    | none => pure { kind := "missing", digest := Sha256.hex .empty, references := #[] }
    | some info => do
      let (kind, encoding) ← (putDeclaration ctx name info).run {}
      pure { kind, digest := Sha256.hex encoding.bytes, references := encoding.references }
  modify (·.insert name result)
  return result

end

inductive Mode where
  | check | generate | generateSpec | closureReport
  deriving BEq

structure Config where
  ci : Name := `TamarinCI
  roots : Array Name := #[`TamarinRuntime, `TamarinWire]
  manifest : System.FilePath := "ExportManifest.txt"
  spec : System.FilePath := "SpecManifest.txt"
  sources : Option System.FilePath := none
  mode : Mode := .check
  /-- `contractTyped`, extended by `--contract-typed` for the mutation tests. -/
  contracts : Array Name := contractTyped.toArray
  /-- C symbols a closure report is restricted to. -/
  only : Array Name := #[]
  /-- Proof-only modules loaded next to the proof root (`--unpinned`): every
  lint and declaration check applies to them, none of their theorems is
  contract, and they need not be imported by the proof root. -/
  unpinned : Array Name := #[]

/-- A contract export with its contract theorems, a proposer export (which has
none), or, with anonymous names, the remaining theorems of the proof root. -/
structure Entry where
  symbol : Name
  constant : Name
  /-- Listed as `proposer`: an export without a contract. -/
  proposer : Bool := false
  theorems : Array (Name × String) := #[]
  deriving Inhabited

def parseArgs : Config → Bool → List String → Except String Config
  | c, _, [] => pure c
  | c, fresh, "--ci" :: m :: rest => parseArgs { c with ci := m.toName } fresh rest
  | c, fresh, "--root" :: m :: rest =>
    -- the first explicit root replaces the defaults
    parseArgs { c with roots := (if fresh then #[] else c.roots).push m.toName } false rest
  | c, fresh, "--manifest" :: f :: rest => parseArgs { c with manifest := f } fresh rest
  | c, fresh, "--sources" :: d :: rest => parseArgs { c with sources := some d } fresh rest
  | c, fresh, "--spec" :: f :: rest => parseArgs { c with spec := f } fresh rest
  | c, fresh, "--generate" :: rest => parseArgs { c with mode := .generate } fresh rest
  | c, fresh, "--generate-spec" :: rest => parseArgs { c with mode := .generateSpec } fresh rest
  | c, fresh, "--closure-report" :: rest => parseArgs { c with mode := .closureReport } fresh rest
  | c, fresh, "--contract-typed" :: n :: rest =>
    parseArgs { c with contracts := c.contracts.push n.toName } fresh rest
  | c, fresh, "--unpinned" :: m :: rest =>
    parseArgs { c with unpinned := c.unpinned.push m.toName } fresh rest
  | c, fresh, "--only-exports" :: symbols :: rest =>
    parseArgs { c with only := (symbols.splitOn ",").toArray.map String.toName } fresh rest
  | _, _, arg :: _ => throw s!"unknown argument {arg}"

def parseManifest (text : String) : Except String (Array Entry) := do
  let mut entries : Array Entry := #[]
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn " " |>.filter (· ≠ "") with
    | ["export", symbol, constant] =>
      entries := entries.push { symbol := symbol.toName, constant := constant.toName }
    | ["proposer", symbol, constant] =>
      entries := entries.push
        { symbol := symbol.toName, constant := constant.toName, proposer := true }
    | ["other"] =>
      entries := entries.push { symbol := .anonymous, constant := .anonymous }
    | ["theorem", name, fingerprint] =>
      unless isDigest fingerprint do throw s!"bad statement fingerprint: {line}"
      if entries.isEmpty then throw s!"theorem before any export: {line}"
      if entries.back!.proposer then
        throw s!"a proposer export carries no contract, but a theorem is listed under \
          {entries.back!.symbol}: {line}"
      entries := entries.modify (entries.size - 1) fun e =>
        { e with theorems := e.theorems.push (name.toName, fingerprint) }
    | _ => throw s!"unreadable manifest line: {line}"
  return entries

/-- The recorded specification closure: constant, kind and fingerprint. Names
are compared as printed, which is injective and survives private prefixes. -/
def parseSpec (text : String) : Except String (Std.HashMap String (String × String)) := do
  let mut pins : Std.HashMap String (String × String) := {}
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn " " |>.filter (· ≠ "") with
    | [kind, name, fingerprint] =>
      unless isDigest fingerprint do throw s!"bad fingerprint: {line}"
      if pins.contains name then throw s!"constant listed twice: {line}"
      pins := pins.insert name (kind, fingerprint)
    | _ => throw s!"unreadable line: {line}"
  return pins

/-- Lean 4.36 compiles constructor indices using a runtime tag read. Check the
exact primitive and its argument, and reduce the logical function on every
constructor to check it returns the corresponding tag. Same check as the root
audit in `TamarinCI.lean`. -/
def checkedCtorIndex (env : Environment) (name impl : Name) : MetaM Bool := do
  let some ind := isCtorIdxCore? env name | return false
  unless impl == name.str "_impl" && Compiler.getImplementedBy? env name == some impl &&
      ind.numCtors > 1 && !ind.isUnsafe && !Compiler.LCNF.isRuntimeBuiltinType ind.name do
    return false
  if ← isPropFormerType ind.type then return false
  let casesOn ← getConstInfo (mkCasesOnName ind.name)
  unless casesOn.levelParams.length > ind.levelParams.length do return false
  let some (.defnInfo logical) := env.find? name | return false
  let some (.defnInfo runtime) := env.find? impl | return false
  unless logical.safety == .safe && runtime.safety == .unsafe &&
      logical.levelParams == ind.levelParams && runtime.levelParams == ind.levelParams &&
      logical.type == runtime.type do return false
  let us := ind.levelParams.map mkLevelParam
  forallTelescope logical.type fun args result => do
    unless args.size == ind.numParams + ind.numIndices + 1 && result == mkConst ``Nat do
      return false
    let value := args.back!
    let ty := mkAppN (mkConst ind.name us) args.pop
    unless (← inferType value) == ty do return false
    let tag := mkApp2 (mkConst ``getObjTagNat [← getLevel ty]) ty value
    unless runtime.value == (← mkLambdaFVars args tag) do return false
    for ctorName in ind.ctors do
      let ctor ← getConstInfoCtor ctorName
      let agrees ← forallTelescope ctor.type fun fields target => do
        let constructed := mkAppN (mkConst ctorName us) fields
        let idx := mkApp (mkAppN (mkConst name us) target.getAppArgs) constructed
        withTransparency .all <| isDefEq idx (mkNatLit ctor.cidx)
      unless agrees do return false
    return true

/-- A type that is a contract in itself: a proposition, or a structure of the
project that has proof fields and whose every data field occurs in the
statement of one of them. A plain function type is not. -/
def carriesContract (env : Environment) (project : Name → Bool) (type : Expr) : MetaM Bool :=
  forallTelescope type fun _ body => do
    if ← isProp body then return true
    let .const carrier _ := body.getAppFn | return false
    unless project carrier do return false
    let some (.inductInfo ind) := env.find? carrier | return false
    unless ind.ctors.length == 1 && ind.numIndices == 0 && !ind.isRec do return false
    let some (.ctorInfo ctor) := env.find? ind.ctors[0]! | return false
    forallTelescope ctor.type fun fields _ => do
      let fields := fields.extract ctor.numParams fields.size
      let mut proofs : Array Expr := #[]
      let mut data : Array Expr := #[]
      for field in fields do
        let fieldType ← inferType field
        if ← isProp fieldType then proofs := proofs.push fieldType else data := data.push field
      return !proofs.isEmpty && data.all fun d => proofs.any fun statement => statement.containsFVar d.fvarId!

def runMeta {α} (env : Environment) (x : MetaM α) : IO α := do
  let ctx : Core.Context := { fileName := "<export audit>", fileMap := default }
  let (a, _) ← (x.run' {} {}).toIO ctx { env }
  return a

/-- Remove comments, keeping line structure. -/
def stripComments (text : String) : String := Id.run do
  let chars := text.toList.toArray
  let mut out := ""
  let mut depth := 0
  let mut i := 0
  while i < chars.size do
    let c := chars[i]!
    let next := chars.getD (i + 1) ' '
    if c == '/' && next == '-' then
      depth := depth + 1
      i := i + 2
    else if depth > 0 && c == '-' && next == '/' then
      depth := depth - 1
      i := i + 2
    else if depth > 0 then
      if c == '\n' then out := out.push c
      i := i + 1
    else if c == '-' && next == '-' then
      while i < chars.size && chars[i]! != '\n' do i := i + 1
    else
      out := out.push c
      i := i + 1
  return out

/-- The first word of a command after attributes and modifiers. -/
partial def commandHead (line : String) : String :=
  let line := line.trimAscii.toString
  if line.startsWith "@[" then
    match line.splitOn "]" with
    | _ :: rest => commandHead ("]".intercalate rest)
    | [] => ""
  else
    match line.splitOn " " |>.filter (· ≠ "") with
    | [] => ""
    | word :: rest =>
      if commandModifiers.contains word then commandHead (" ".intercalate rest) else word

def lintSource (module : Name) (text : String) : Array String := Id.run do
  let mut errors := #[]
  let mut number := 0
  for line in (stripComments text).splitOn "\n" do
    number := number + 1
    for word in forbiddenAnywhere do
      if (line.splitOn word).length > 1 then
        errors := errors.push s!"{module}:{number}: source uses `{word}`"
    let head := commandHead line
    if forbiddenCommands.contains head then
      errors := errors.push s!"{module}:{number}: source uses the `{head}` command"
  return errors

def sourcePath (root : System.FilePath) (module : Name) : System.FilePath :=
  (module.components.foldl (fun path part => path / part.toString) root).withExtension "lean"

def cType : IR.IRType → Option String
  | .uint8 => some "uint8_t" | .uint16 => some "uint16_t" | .uint32 => some "uint32_t"
  | .uint64 => some "uint64_t" | .usize => some "size_t" | .float => some "double"
  | .float32 => some "float"
  | .object | .tobject | .tagged => some "lean_object*"
  | _ => none

/-- The C declaration of an exported function. The bridge hands every object
argument over, so a borrowed parameter would leak it. -/
def signature (env : Environment) (symbol constant : Name) : Except String String := do
  let some decl := IR.findEnvDecl env constant
    | throw s!"{constant} has no compiled code"
  let some result := cType decl.resultType
    | throw s!"{constant} returns a type without a C representation"
  let mut params := #[]
  for p in decl.params do
    let some ty := cType p.ty | throw s!"{constant} takes a type without a C representation"
    if p.borrow then
      throw s!"{constant} borrows a parameter, but the C bridge passes ownership"
    params := params.push ty
  return s!"{result} {symbol}({", ".intercalate params.toList})"

def dependencies (info : ConstantInfo) : Array Name := info.getUsedConstantsAsSet.toArray

def run (config : Config) : IO UInt32 := do
  let sysroot ← findSysroot
  initSearchPath sysroot
  let toolchain := (← IO.FS.realPath (sysroot / "lib" / "lean")).toString ++ "/"
  let imports := (#[config.ci] ++ config.roots ++ config.unpinned).map
    fun m => ({ module := m } : Import)
  -- `loadExts := false`: extension entries stay data and no initializer runs.
  let env ← importModules imports {} (loadExts := false)
  let modules := env.header.moduleNames
  let data := env.header.moduleData
  let mut errors : Array String := #[]

  -- Which modules are the toolchain's.
  let mut trusted : Array Bool := #[]
  for m in modules do
    let root := m.getRoot
    if root == `Init || root == `Std || root == `Lean then
      let path := (← IO.FS.realPath (← findOLean m)).toString
      if path.startsWith toolchain then
        trusted := trusted.push true
      else
        errors := errors.push s!"{m} is named like a toolchain module but was loaded from {path}"
        trusted := trusted.push false
    else
      trusted := trusted.push false
  let index : Std.HashMap Name Nat :=
    (List.range modules.size).foldl (fun map i => map.insert modules[i]! i) {}
  let some ciIndex := index[config.ci]?
    | IO.eprintln s!"proof root {config.ci} was not loaded"; return 1
  let isProject (i : Nat) : Bool := !trusted[i]!

  -- The kernel replay starts at the proof root, so it must reach every module.
  let mut reached : Std.HashSet Nat := {}
  let mut pending := [ciIndex]
  while !pending.isEmpty do
    match pending with
    | [] => pure ()
    | i :: rest =>
      pending := rest
      unless reached.contains i do
        reached := reached.insert i
        for imp in data[i]!.imports do
          if let some j := index[imp.module]? then pending := j :: pending
  for i in [0:modules.size] do
    if isProject i && !reached.contains i && !config.unpinned.contains modules[i]! then
      errors := errors.push s!"{modules[i]!} is not imported by the proof root {config.ci}"
  -- An unpinned module holds proofs outside the contract. It may not be part of
  -- the runtime, whose every module the kernel replay of the root has to cover.
  let mut runtime : Std.HashSet Nat := {}
  let mut linked := config.roots.toList.filterMap (index[·]?)
  while !linked.isEmpty do
    match linked with
    | [] => pure ()
    | i :: rest =>
      linked := rest
      unless runtime.contains i do
        runtime := runtime.insert i
        for imp in data[i]!.imports do
          if let some j := index[imp.module]? then linked := j :: linked
  for m in config.unpinned do
    match index[m]? with
    | none => errors := errors.push s!"unpinned module {m} was not loaded"
    | some i =>
      if runtime.contains i || i == ciIndex then
        errors := errors.push s!"unpinned module {m} is the proof root or part of the runtime"

  -- Imports and extension entries of project modules.
  let mut projectModules := 0
  for i in [0:modules.size] do
    unless isProject i do continue
    projectModules := projectModules + 1
    for imp in data[i]!.imports do
      if imp.module == config.ci then
        errors := errors.push s!"{modules[i]!} imports the proof root"
      let some j := index[imp.module]? | continue
      if i != ciIndex && trusted[j]! && imp.module.getRoot == `Lean then
        errors := errors.push
          s!"{modules[i]!} imports {imp.module}: only the proof root may import `Lean`"
    for (ext, entries) in data[i]!.entries do
      if !entries.isEmpty && !allowedExtensions.contains (toString ext) then
        errors := errors.push
          s!"{modules[i]!} adds {entries.size} entries to the environment extension {ext}, \
            which is outside the audit's allowlist (macros, syntax, elaborators, initializers \
            and other meta-level code are not allowed in audited modules)"
    if let some root := config.sources then
      if i != ciIndex then
        let path := sourcePath root modules[i]!
        if ← path.pathExists then
          errors := errors ++ lintSource modules[i]! (← IO.FS.readFile path)
        else
          errors := errors.push s!"{modules[i]!} has no source at {path}"

  -- Per-declaration checks.
  let moduleOf (name : Name) : Option Nat := (env.getModuleIdxFor? name).map (·.toNat)
  let projectConstant (name : Name) : Bool :=
    match moduleOf name with
    | some i => isProject i
    | none => true
  let mut project : Array (Name × ConstantInfo) := #[]
  for (name, info) in env.constants.toList do
    if projectConstant name then project := project.push (name, info)
  let mut exported : Array (Name × Name) := #[]
  for (name, info) in project do
    if let some symbol := getExportNameFor? env name then
      exported := exported.push (symbol, name)
    if let some replacement := Compiler.getImplementedBy? env name then
      unless ← runMeta env (checkedCtorIndex env name replacement) do
        errors := errors.push s!"{name} has unchecked implemented_by replacement {replacement}"
    if isExtern env name then
      errors := errors.push s!"{name} has unchecked extern implementation"
    if let some initializer := getInitFnNameFor? env name then
      errors := errors.push s!"{name} has unchecked runtime initializer {initializer}"
    if let some initializer := getBuiltinInitFnNameFor? env name then
      errors := errors.push s!"{name} has unchecked runtime initializer {initializer}"
    if info.isUnsafe then
      unless ← runMeta env (checkedCtorIndex env name.getPrefix name) do
        errors := errors.push s!"{name} is an unsafe project declaration"

  -- Axioms: everything reachable from a project declaration.
  let mut edges : Std.HashMap Name (Array Name) := {}
  let mut stack : Array Name := project.map (·.1)
  let mut axioms : Array Name := #[]
  while !stack.isEmpty do
    let name := stack.back!
    stack := stack.pop
    if edges.contains name then continue
    let some info := env.find? name
      | errors := errors.push s!"unknown constant {name}"; edges := edges.insert name #[]
    if info matches .axiomInfo .. then
      unless standardAxioms.contains name do axioms := axioms.push name
    let deps := dependencies info
    edges := edges.insert name deps
    for dep in deps do
      unless edges.contains dep do stack := stack.push dep
  unless axioms.isEmpty do
    let mut users : Std.HashMap Name (Array Name) := {}
    for (name, deps) in edges.toList do
      for dep in deps do
        users := users.insert dep ((users.getD dep #[]).push name)
    for ax in axioms do
      let mut seen : Std.HashSet Name := {}
      let mut todo := #[ax]
      let mut hits : Array Name := #[]
      while !todo.isEmpty do
        let name := todo.back!
        todo := todo.pop
        if seen.contains name then continue
        seen := seen.insert name
        if projectConstant name then hits := hits.push name
        todo := todo ++ users.getD name #[]
      let shown := ", ".intercalate ((hits.toList.take 5).map toString)
      errors := errors.push
        s!"{hits.size} project declarations depend on unapproved axiom {ax}, for example {shown}"

  -- Exports, their theorems and the statements of those theorems.
  let exportSet : Std.HashSet Name := exported.foldl (fun set (_, c) => set.insert c) {}
  -- A `partial` definition is opaque to the logic: nothing proved about its
  -- callers says what it computes or that it returns. None may be exported code.
  let mut compiled : Std.HashSet Name := {}
  let mut frontier := exported.map (·.2)
  while !frontier.isEmpty do
    let name := frontier.back!
    frontier := frontier.pop
    if compiled.contains name then continue
    compiled := compiled.insert name
    if projectConstant name then
      if let some info := env.find? name then
        if info.isPartial || info matches .opaqueInfo .. then
          errors := errors.push
            s!"{name} is an opaque or partial project declaration used by exported code"
    frontier := frontier ++ edges.getD name #[]
  let ciTheorem (name : Name) : Option TheoremVal :=
    match env.find? name with
    | some (.thmInfo t) => if moduleOf name == some ciIndex then some t else none
    | _ => none

  -- The contract: every public theorem of the proof root, by name. Unfolding
  -- equations that Lean derives for a definition when a proof first rewrites
  -- with it are stored in the module of that proof. They restate the
  -- definition, here an implementation detail, and are not contract.
  let derived (name : Name) (type : Expr) : Bool :=
    match name with
    | .str parent last =>
      let chars := last.toList
      let conclusion := type.getForallBody
      (last == "eq_def" || last == "eq_unfold" ||
        (chars.take 3 == "eq_".toList && chars.length > 3 && (chars.drop 3).all Char.isDigit)) &&
      (env.find? parent matches some (.defnInfo ..)) && moduleOf parent != some ciIndex &&
      conclusion.isAppOfArity ``Eq 3 && (conclusion.getArg! 1).getAppFn.isConstOf parent
    | _ => false
  let mut theorems : Array (Name × TheoremVal) := #[]
  for (name, info) in project do
    if let .thmInfo t := info then
      if moduleOf name == some ciIndex && !name.isInternal && !isPrivateName name
          && !derived name t.type then
        theorems := theorems.push (name, t)
  theorems := theorems.qsort fun a b => a.1.toString < b.1.toString
  let restricted := config.mode == .closureReport && !config.only.isEmpty
  if restricted then
    -- Only the statements about the chosen exports: some of them, and no other export.
    for symbol in config.only do
      unless exported.any (·.1 == symbol) do
        IO.eprintln s!"--only-exports: {symbol} is not an exported symbol"; return 2
    let chosen : Std.HashSet Name := exported.foldl
      (fun set (symbol, constant) => if config.only.contains symbol then set.insert constant else set) {}
    theorems := theorems.filter fun (_, t) =>
      let mentioned := t.type.getUsedConstants.filter exportSet.contains
      !mentioned.isEmpty && mentioned.all chosen.contains
    exported := exported.filter fun (symbol, _) => config.only.contains symbol

  -- An export that a theorem of the proof root mentions has a contract. The
  -- others are proposers: nothing is promised about them.
  let mut mentioned : Std.HashSet Name := {}
  let mut mentions : Std.HashMap Name (Array Name) := {}
  for (name, t) in theorems do
    for c in t.type.getUsedConstants do
      if exportSet.contains c then
        mentioned := mentioned.insert c
        mentions := mentions.insert c ((mentions.getD c #[]).push name)
  let contractExports := exported.filter fun (_, c) => mentioned.contains c
  let proposerExports := (exported.filter fun (_, c) => !mentioned.contains c).qsort
    fun a b => a.1.toString < b.1.toString

  -- Constants followed by type only because their type is the contract.
  let contractSet : Std.HashSet Name := config.contracts.foldl (fun set name => set.insert name) {}
  for name in config.contracts do
    match env.find? name with
    | some (.defnInfo d) =>
      if exportSet.contains name || !projectConstant name || d.safety != .safe then
        errors := errors.push s!"{name} cannot be followed by type only: it is an export, \
          not a project definition, or unsafe"
      else unless ← runMeta env (carriesContract env projectConstant d.type) do
        errors := errors.push s!"{name} cannot be followed by type only: its type is not a \
          contract (a proposition, or a project structure whose proof fields mention every \
          data field)"
    | _ => errors := errors.push s!"{name} is listed to be followed by type only but is not a definition"

  -- Fingerprints of the statements and of everything that gives them meaning.
  let context : FingerprintContext :=
    { env, project := projectConstant, exports := exportSet, contracts := contractSet }
  let mut memo : Std.HashMap Name Fingerprint := {}
  let mut statements : Std.HashMap Name String := {}
  let mut closure : Std.HashMap Name Fingerprint := {}
  let mut todo : Array Name := #[]
  for (name, _) in theorems do
    let (fp, next) := (fingerprintOf context name).run memo
    memo := next
    statements := statements.insert name fp.digest
    todo := todo ++ fp.references
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if closure.contains name then continue
    let (fp, next) := (fingerprintOf context name).run memo
    memo := next
    closure := closure.insert name fp
    todo := todo ++ fp.references
  let closureLines := closure.toArray.map (fun (name, fp) => (toString name, fp.kind, fp.digest))
    |>.qsort fun a b => a.1 < b.1
  for (name, _, _) in closureLines do
    if name.any Char.isWhitespace then
      errors := errors.push s!"the name of specification constant {name} contains white space"
  -- Auxiliaries inlined into the fingerprints above are fingerprinted but not named.
  let inlined := memo.size - closure.size - theorems.size
  unless restricted do
    for name in config.contracts do
      unless closure.contains name do
        errors := errors.push s!"{name} is listed to be followed by type only, \
          but no contract statement depends on it"

  if config.mode == .generate then
    let sorted := exported.qsort fun a b => a.1.toString < b.1.toString
    IO.println "# Exported C symbols, the Lean constants behind them and the theorems that state"
    IO.println "# their contract, with the SHA-256 fingerprint of each kernel statement."
    IO.println "# Regenerate: lake env lean --run Tests/ExportAudit.lean --generate"
    IO.println "# `proposer` lines are exports without a contract: no theorem of the proof root"
    IO.println "# may mention them, and the caller may use their output only as a proposal that a"
    IO.println "# contract export checks. `other` lists root theorems that mention no export."
    let mut attached : Std.HashSet Name := {}
    for (symbol, constant) in sorted do
      unless mentioned.contains constant do continue
      IO.println s!"export {symbol} {constant}"
      for (name, t) in theorems do
        if t.type.getUsedConstants.contains constant then
          attached := attached.insert name
          IO.println s!"  theorem {name} {statements.getD name ""}"
    for (symbol, constant) in proposerExports do
      IO.println s!"proposer {symbol} {constant}"
    unless theorems.all fun (name, _) => attached.contains name do
      IO.println "other"
      for (name, _) in theorems do
        unless attached.contains name do
          IO.println s!"  theorem {name} {statements.getD name ""}"
    return 0

  if config.mode == .generateSpec then
    IO.println "# Specification closure of the contract statements in ExportManifest.txt: every"
    IO.println "# project constant a pinned statement mentions, directly or through definitions,"
    IO.println "# with the SHA-256 fingerprint of the part that gives it meaning (type and value;"
    IO.println "# type only for a theorem, an exported constant or a `contract` constant, which the"
    IO.println "# audit lists in `contractTyped`). Sorted by name."
    IO.println "# Regenerate: lake env lean --run Tests/ExportAudit.lean --generate-spec"
    for (name, kind, digest) in closureLines do
      IO.println s!"{kind} {name} {digest}"
    return 0

  if config.mode == .closureReport then
    -- What the code of a contract export runs: the compiled declarations
    -- reachable from the exports that have a contract. Proposers do not count.
    let mut runs : Std.HashSet Name := {}
    let mut calls := contractExports.map (·.2)
    while !calls.isEmpty do
      let name := calls.back!
      calls := calls.pop
      if runs.contains name then continue
      runs := runs.insert name
      if let some decl := IR.findEnvDecl env name then
        calls := calls ++ IR.collectUsedDecls env [decl]
    -- Types and constructors exported code is defined with, proofs not opened.
    let mut built : Std.HashSet Name := {}
    let mut parts := contractExports.map (·.2)
    while !parts.isEmpty do
      let name := parts.back!
      parts := parts.pop
      if built.contains name || !projectConstant name then continue
      built := built.insert name
      if let some info := env.find? name then
        parts := parts ++ (match info with
          | .thmInfo t => t.type.getUsedConstants
          | _ => dependencies info)
    let mut rows : Array String := #[]
    let mut perModule : Std.HashMap String (Nat × Nat × Nat) := {}
    for (name, fp) in closure.toArray do
      let module := match moduleOf name with
        | some i => toString modules[i]!
        | none => "(none)"
      let typeOnly := fp.kind == "export" || fp.kind == "contract"
      let executed := !typeOnly && runs.contains name
      let data := !typeOnly && !executed && built.contains name &&
        (fp.kind == "inductive" || fp.kind == "constructor" || fp.kind == "recursor")
      let (count, code, types) := perModule.getD module (0, 0, 0)
      perModule := perModule.insert module
        (count + 1, code + (if executed then 1 else 0), types + (if data then 1 else 0))
      let share := if executed then "runs" else if data then "data" else "-"
      rows := rows.push s!"{module}\t{fp.kind}\t{share}\t{name}"
    IO.println s!"# {closure.size} named constants in the specification closure of \
      {theorems.size} statements ({inlined} auxiliaries inlined)"
    if restricted then
      IO.println s!"# restricted to the statements that mention only: {config.only.toList}"
    IO.println "# followed by type only (contractTyped)\tin this closure"
    for name in config.contracts do
      IO.println s!"contract\t{name}\t{if closure.contains name then "yes" else "no"}"
    IO.println s!"# {contractExports.size} contract exports, {proposerExports.size} proposer \
      exports (no contract; in no statement and not in this closure)"
    for (symbol, constant) in contractExports.qsort (fun a b => a.1.toString < b.1.toString) do
      IO.println s!"export\t{symbol}\t{constant}"
    for (symbol, constant) in proposerExports do
      IO.println s!"proposer\t{symbol}\t{constant}"
    IO.println "# statements"
    for (name, _) in theorems do IO.println s!"statement\t{name}"
    IO.println "# module\tconstants\texecuted by a contract export\tdata types of their code"
    for (module, count, code, types) in perModule.toArray.qsort (fun a b => a.1 < b.1) do
      IO.println s!"module\t{module}\t{count}\t{code}\t{types}"
    for row in rows.qsort (· < ·) do IO.println s!"constant\t{row}"
    -- The compiled definitions each statement names: those it reaches through
    -- propositions, types and theorems only. A decoder or a reference
    -- semantics belongs here; a search does not.
    let computes (name : Name) : Bool :=
      !exportSet.contains name && !contractSet.contains name &&
        (env.find? name matches some (.defnInfo ..)) && (IR.findEnvDecl env name).isSome
    let mut named : Array String := #[]
    for (thm, t) in theorems do
      let mut seen : Std.HashSet Name := {}
      let mut unvisited := t.type.getUsedConstants
      while !unvisited.isEmpty do
        let name := unvisited.back!
        unvisited := unvisited.pop
        if seen.contains name || !projectConstant name then continue
        seen := seen.insert name
        if computes name then
          let module := match moduleOf name with
            | some i => toString modules[i]!
            | none => "(none)"
          named := named.push s!"{thm}\t{module}\t{if runs.contains name then "runs" else "-"}\t{name}"
        else if !exportSet.contains name && !contractSet.contains name then
          if let some info := env.find? name then
            unvisited := unvisited ++ (match info with
              | .thmInfo t => t.type.getUsedConstants
              | .inductInfo i => i.type.getUsedConstants ++ i.ctors.toArray
              | _ => dependencies info)
    IO.println "# statement\tmodule\texecuted by a contract export\tcompiled definition the statement names"
    for row in named.qsort (· < ·) do IO.println s!"names\t{row}"
    return 0

  let entries ← match parseManifest (← IO.FS.readFile config.manifest) with
    | .ok entries => pure entries
    | .error message => IO.eprintln s!"{config.manifest}: {message}"; return 1
  let pins ← match parseSpec (← IO.FS.readFile config.spec) with
    | .ok pins => pure pins
    | .error message => IO.eprintln s!"{config.spec}: {message}"; return 1
  for (symbol, constant) in exported do
    unless entries.any fun e => e.symbol == symbol && e.constant == constant do
      errors := errors.push s!"Unapproved project export {constant} maps to {symbol}"
  let mut pinned : Std.HashSet Name := {}
  let mut listed : Std.HashSet Name := {}
  let mut proposers := 0
  for e in entries do
    let isExport := !e.symbol.isAnonymous
    if isExport then
      if listed.contains e.symbol then
        errors := errors.push s!"export {e.symbol} is listed twice in the manifest"
      listed := listed.insert e.symbol
      unless exported.contains (e.symbol, e.constant) do
        errors := errors.push s!"Required verified export {e.constant} must map to {e.symbol}"
      if e.proposer then
        -- A proposer has no contract: nothing the caller is promised may speak
        -- about it, directly or through a definition a statement depends on.
        proposers := proposers + 1
        let users := mentions.getD e.constant #[]
        for name in users do
          errors := errors.push s!"proposer export {e.symbol} is mentioned by contract theorem \
            {name}: a proposer carries no contract"
        if users.isEmpty && closure.contains e.constant then
          errors := errors.push s!"proposer export {e.symbol} ({e.constant}) gives a contract \
            statement its meaning through a definition of the specification closure"
      else if e.theorems.isEmpty then
        errors := errors.push s!"export {e.symbol} has no contract theorem in the manifest \
          (an export without a contract has to be listed as `proposer`)"
    for (name, expected) in e.theorems do
      let some t := ciTheorem name
        | errors := errors.push s!"contract theorem {name} is not a theorem of {config.ci}"
      pinned := pinned.insert name
      if isExport then
        unless t.type.getUsedConstants.contains e.constant do
          errors := errors.push s!"contract theorem {name} does not mention {e.constant}"
      let actual := statements.getD name ""
      unless actual == expected do
        errors := errors.push
          s!"the statement of contract theorem {name} changed \
            (fingerprint {actual}, manifest {expected})"
  -- The manifest is the whole contract: no theorem of the root is left unpinned.
  for (name, _) in theorems do
    unless pinned.contains name do
      errors := errors.push s!"theorem {name} of {config.ci} is not in the manifest"

  -- The specification closure is exactly the recorded one.
  let mut specErrors : Array String := #[]
  for (name, kind, digest) in closureLines do
    match pins[name]? with
    | none =>
      specErrors := specErrors.push
        s!"{kind} {name} now gives a contract statement its meaning but is not in {config.spec}"
    | some (pinnedKind, pinnedDigest) =>
      unless pinnedKind == kind && pinnedDigest == digest do
        specErrors := specErrors.push
          s!"specification constant {name} changed \
            ({kind} {digest}, recorded {pinnedKind} {pinnedDigest})"
  let current : Std.HashSet String := closureLines.foldl (fun set (name, _, _) => set.insert name) {}
  for name in (pins.toArray.map (·.1)).qsort (· < ·) do
    unless current.contains name do
      specErrors := specErrors.push
        s!"{name} is recorded in {config.spec} but no contract statement depends on it any more"
  let shown := 40
  errors := errors ++ specErrors.extract 0 shown
  if specErrors.size > shown then
    errors := errors.push s!"... and {specErrors.size - shown} more differences from {config.spec}"

  for (symbol, constant) in exported do
    if let .error message := signature env symbol constant then
      errors := errors.push message

  unless errors.isEmpty do
    for message in errors do IO.eprintln s!"export audit: {message}"
    IO.eprintln s!"export audit FAILED with {errors.size} findings"
    return 1
  IO.println s!"export audit passed: {projectModules} project modules, {project.size} project \
    declarations, {exported.size - proposers} contract exports, {proposers} proposer exports, \
    {pinned.size} contract statements, \
    {closure.size} specification constants ({inlined} auxiliaries inlined)"
  return 0

end ExportAudit

def main (args : List String) : IO UInt32 := do
  match ExportAudit.parseArgs {} true args with
  | .ok config => ExportAudit.run config
  | .error message => IO.eprintln message; return 2
