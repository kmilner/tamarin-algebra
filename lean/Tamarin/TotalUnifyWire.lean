import Tamarin.MixedUnification
import Tamarin.UnifyExists
import Tamarin.WordEncoding
import TamarinWire

/-! The ordinary-unification packet uses a per-query symbol dictionary.
Decode an arity-correct DAG without assigning a sort to the root of each
application. Sorting is imposed on substitution images by the unifier. -/
namespace Tamarin.TotalUnifyWire
open Whole

def sortCode : SortId → UInt64
  | .pub => 0 | .fresh => 1 | .msg => 2 | .node => 3 | .nat => 4

def sortOf (n : UInt64) : SortId :=
  if n == 0 then .pub else if n == 1 then .fresh else if n == 2 then .msg
  else if n == 3 then .node else .nat

theorem sortOf_code (s : SortId) : sortOf (sortCode s) = s := by cases s <;> decide

def decl (ds : List Decl) (k id : UInt64) :=
  ds.find? (fun d => d.kind == k && d.id == id)

abbrev Symbol (ds : List Decl) (k : UInt64) := { id : UInt64 // (decl ds k id).isSome }

private def resolve (ds : List Decl) (k id : UInt64) : Option (Symbol ds k) :=
  if h : (decl ds k id).isSome then some ⟨id,h⟩ else none

def info {ds k} (f : Symbol ds k) := (decl ds k f.val).get f.property

structure Dictionary where
  decls : List Decl
  atoms : List (UInt64 × SortId)

abbrev Dictionary.sig (d : Dictionary) : Signature where
  FreeSym := Symbol d.decls 2
  CSym := Symbol d.decls 3
  ACSym := Symbol d.decls 4
  Atom := { a : UInt64 × SortId // a ∈ d.atoms }
  arity f := (info f).inputs.length
  inputSort f i := sortOf ((info f).inputs.get i)
  outputSort f := sortOf (info f).output
  cSort f := sortOf (info f).output
  acSort f := sortOf (info f).output
  atomSort a := a.val.2

private def atom (d : Dictionary) (id : UInt64) (s : SortId) : Option d.sig.Atom :=
  if h : (id,s) ∈ d.atoms then some ⟨(id,s),h⟩ else none

def leaf (d : Dictionary) (k id arg : UInt64) : Option (Term d.sig) := do
  guard (arg ≤ 4)
  if k == 0 then return .var ⟨id.toNat,sortOf arg⟩
  if k == 1 then return .atom (← atom d id (sortOf arg))
  none

def app (d : Dictionary) (k id : UInt64) (children : List (Term d.sig)) :
    Option (Term d.sig) := do
  if k == 2 then
    let f ← resolve d.decls 2 id
    if h : children.length = d.sig.arity f then
      return .free f fun i => children.get ⟨i.val,h.symm ▸ i.isLt⟩
    else none
  else if k == 3 then
    let f ← resolve d.decls 3 id
    let [l,r] := children | none
    return .comm f l r
  else if k == 4 then
    let f ← resolve d.decls 4 id
    let l :: r :: rs := children | none
    return .ac f l (ACRepresentation.fold f r rs)
  else none

def node (d : Dictionary) (prior : Array (Term d.sig)) (row : Array UInt64) := do
  let k :: id :: tail := row.toList | none
  if k ≤ 1 then
    let [arg] := tail | none
    leaf d k id arg
  else
    app d k id (← tail.mapM (fun (i : UInt64) => prior[i.toNat]?))

def equations {s : Signature} (ts : Array (Term s)) : List UInt64 → Option (Problem s)
  | [] => some []
  | i :: j :: rest => do return ⟨← ts[i.toNat]?,← ts[j.toNat]?⟩ :: (← equations ts rest)
  | [_] => none

def graph (decls : Array UInt64) (nodes : Array (Array UInt64)) :
    Option ((d : Dictionary) × Array (Term d.sig)) := do
  let ds ← declarations decls.toList
  let atoms := nodes.toList.filterMap fun row => match row.toList with
    | [1,id,s] => some (id,sortOf s)
    | _ => none
  let d : Dictionary := ⟨ds,atoms.eraseDups⟩
  let ts ← nodes.foldlM (fun acc r => do return acc.push (← node d acc r)) #[]
  return ⟨d,ts⟩

def input (decls : Array UInt64) (nodes : Array (Array UInt64)) (roots : Array UInt64) :
    Option ((d : Dictionary) × Problem d.sig) := do
  let ⟨d,ts⟩ ← graph decls nodes
  return ⟨d,← equations ts roots.toList⟩

/-- Fixed contract for a one-sided refutation of a whole query. -/
def RefutationCorrect (candidate : Array UInt64 → Array (Array UInt64) → Array UInt64 → Bool) : Prop :=
  ∀ ds ns es, candidate ds ns es = true →
    ∃ d p, input ds ns es = some ⟨d,p⟩ ∧ ¬ p.Satisfiable

/-- Postorder triples. The third word is a sort for a leaf and a child
count for an application. Only natural-number fields need checked packing. -/
structure Token where
  kind : UInt64
  id : UInt64
  arg : UInt64
  deriving DecidableEq

def Token.words (t : Token) := [t.kind,t.id,t.arg]

def write {d : Dictionary} : Term d.sig → Option (List Token)
  | .var v => do return [⟨0,← WordEncoding.pack v.id,sortCode v.sort⟩]
  | .atom a => some [⟨1,a.val.1,sortCode a.val.2⟩]
  | .free f args => do
    let code ← (List.finRange _).mapM fun i => write (args i)
    return code.flatten ++ [⟨2,f.val,← WordEncoding.pack (d.sig.arity f)⟩]
  | .comm f l r => do return (← write l) ++ (← write r) ++ [⟨3,f.val,2⟩]
  | .ac f l r => do return (← write l) ++ (← write r) ++ [⟨4,f.val,2⟩]

def binding {d : Dictionary} (σ : Substitution d.sig) (v : Variable) : Option (Array UInt64) := do
  return ((← WordEncoding.pack v.id) :: sortCode v.sort :: (← write (σ.image v)).flatMap Token.words).toArray

/-- Append the words of a term to a buffer, without the intermediate token lists. -/
private def emit {d : Dictionary} : Term d.sig → Array UInt64 → Option (Array UInt64)
  | .var v, acc => (WordEncoding.pack v.id).map fun id => ((acc.push 0).push id).push (sortCode v.sort)
  | .atom a, acc => some (((acc.push 1).push a.val.1).push (sortCode a.val.2))
  | .free f args, acc => do
    let acc ← (List.finRange _).foldlM (fun acc i => emit (args i) acc) acc
    let n ← WordEncoding.pack (d.sig.arity f)
    return ((acc.push 2).push f.val).push n
  | .comm f l r, acc => do
    let acc ← emit l acc
    let acc ← emit r acc
    return ((acc.push 3).push f.val).push 2
  | .ac f l r, acc => do
    let acc ← emit l acc
    let acc ← emit r acc
    return ((acc.push 4).push f.val).push 2

private def words (ts : List Token) : Array UInt64 := (ts.flatMap Token.words).toArray

private theorem words_append (xs ys : List Token) : words (xs ++ ys) = words xs ++ words ys := by
  simp [words]

private theorem push3 (acc : Array UInt64) (a b c : UInt64) :
    ((acc.push a).push b).push c = acc ++ #[a,b,c] := by
  apply Array.toList_inj.mp
  simp

private theorem emit_fold {d : Dictionary} {ι : Type} (args : ι → Term d.sig)
    (ih : ∀ i acc, emit (args i) acc = (write (args i)).map fun ts => acc ++ words ts)
    (is : List ι) (acc : Array UInt64) :
    is.foldlM (fun acc i => emit (args i) acc) acc =
      (is.mapM fun i => write (args i)).map fun cs => acc ++ words cs.flatten := by
  induction is generalizing acc with
  | nil => simp [words]
  | cons i is step =>
    rw [List.foldlM_cons, List.mapM_cons, ih]
    cases write (args i) with
    | none => rfl
    | some ts =>
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, step]
      cases is.mapM (fun i => write (args i)) with
      | none => rfl
      | some cs => simp [words_append, Array.append_assoc]

private theorem emit_eq {d : Dictionary} (t : Term d.sig) (acc : Array UInt64) :
    emit t acc = (write t).map fun ts => acc ++ words ts := by
  induction t generalizing acc with
  | var v =>
    simp only [emit, write]
    cases WordEncoding.pack v.id <;> simp [words, Token.words, push3]
  | atom a => simp [emit, write, words, Token.words, push3]
  | free f args ih =>
    simp only [emit, write, bind_pure_comp, Option.bind_eq_bind]
    rw [emit_fold args ih]
    cases (List.finRange _).mapM (fun i => write (args i)) with
    | none => rfl
    | some cs =>
      cases WordEncoding.pack (d.sig.arity f) <;> simp [words, Token.words, push3]
  | comm f l r il ir | ac f l r il ir =>
    simp only [emit, write, il, ir, bind_pure_comp, Option.bind_eq_bind]
    cases write l with
    | none => rfl
    | some a =>
      cases write r with
      | none => rfl
      | some b => simp [words, Token.words, push3]

/-- `binding` writing the image straight into the row. -/
private def bindingDirect {d : Dictionary} (σ : Substitution d.sig) (v : Variable) :
    Option (Array UInt64) := do
  let id ← WordEncoding.pack v.id
  emit (σ.image v) #[id, sortCode v.sort]

@[csimp] private theorem binding_eq_direct : @binding = @bindingDirect := by
  funext d σ v
  simp only [binding, bindingDirect, emit_eq, bind_pure_comp, Option.bind_eq_bind]
  cases WordEncoding.pack v.id with
  | none => rfl
  | some id =>
    cases write (σ.image v) with
    | none => rfl
    | some ts => simp [words]

def arm {d : Dictionary} (vs : List Variable) (σ : Substitution d.sig) : Option (List (Array UInt64)) := do
  return #[] :: (← vs.mapM (binding σ))

def pack {d : Dictionary} (p : Problem d.sig) (answers : List (Substitution d.sig)) :
    Option (Array (Array UInt64)) := do
  return (#[1] :: (← answers.mapM (arm p.variables.eraseDups)).flatten).toArray

/-- `pack` removing repeated variables bucket by bucket. -/
private def packBucketed {d : Dictionary} (p : Problem d.sig) (answers : List (Substitution d.sig)) :
    Option (Array (Array UInt64)) := do
  return (#[1] :: (← answers.mapM (arm (Buckets.dedup Variable.id p.variables))).flatten).toArray

@[csimp] private theorem pack_eq_bucketed : @pack = @packBucketed := by
  funext d p answers
  simp only [pack, packBucketed, Buckets.dedup_eq]

/-- A variable or a product at the root. -/
private def sumLike {d : Dictionary} : Term d.sig → Bool
  | .var _ | .ac _ _ _ => true
  | _ => false

/-- The operands of a product at its root, counted along the right spine up
to the given bound. -/
private def spine {d : Dictionary} : Nat → Term d.sig → Nat
  | 0, _ => 0
  | fuel + 1, .ac _ _ r => 1 + spine fuel r
  | _ + 1, _ => 1

/-- Operands of a product from which a query is examined before listing. -/
def wideProduct : Nat := 8

/-- The family of the unifier, or the empty family when the linear residuals
of the query already show that it has no unifier. Only a query between sums
with a product of at least `wideProduct` operands and at least 32 variable
occurrences is examined first: listing refutes another one as fast, and the
examination would repeat its free factoring. -/
def family {d : Dictionary} (p : Problem d.sig) : List (Substitution d.sig) :=
  if (p.all fun e => sumLike e.lhs && sumLike e.rhs) &&
      (p.any fun e => wideProduct ≤ spine wideProduct e.lhs || wideProduct ≤ spine wideProduct e.rhs) &&
      32 ≤ p.variables.length &&
      UnifyExists.fast UnifyExists.depth p == some false then []
  else (MixedUnification.verified (s := d.sig)).solve p trivial []

theorem family_correct {d : Dictionary} (p : Problem d.sig) :
    (Outcome.complete (family p)).CorrectIn p [] := by
  unfold family
  split
  · next none =>
    refine ⟨(complete_empty_iff p).mpr fun yes => ?_, by simp [Outcome.answers], by simp [Outcome.answers]⟩
    have verdict : UnifyExists.fast UnifyExists.depth p = some false := by
      simpa using (Bool.and_eq_true_iff.mp none).2
    have := (UnifyExists.fast_sound _ p false verdict).mpr yes
    cases this
  · exact MixedUnification.unify_correct rfl

theorem family_subset {d : Dictionary} (p : Problem d.sig) :
    ∀ σ ∈ family p, σ ∈ (MixedUnification.verified (s := d.sig)).solve p trivial [] := by
  unfold family
  split
  · intro σ h; cases h
  · exact fun _ h => h

def run (decls : Array UInt64) (nodes : Array (Array UInt64)) (roots : Array UInt64) :
    Array (Array UInt64) :=
  (do
    let ⟨_,p⟩ ← input decls nodes roots
    pack p (family p)).getD #[#[0]]

theorem app_free {d : Dictionary} (f : d.sig.FreeSym) (args : Fin (d.sig.arity f) → Term d.sig) :
    app d 2 f.val (List.ofFn args) = some (.free f args) := by
  simp [app,resolve,f.property,List.get_eq_getElem,List.getElem_ofFn]

theorem app_comm {d : Dictionary} (f : d.sig.CSym) (l r : Term d.sig) :
    app d 3 f.val [l,r] = some (.comm f l r) := by simp [app,resolve,f.property]

theorem app_ac {d : Dictionary} (f : d.sig.ACSym) (l r : Term d.sig) :
    app d 4 f.val [l,r] = some (.ac f l r) := by simp [app,resolve,f.property,ACRepresentation.fold]

theorem leaf_var {d : Dictionary} (id : UInt64) (s : SortId) :
    leaf d 0 id (sortCode s) = some (.var ⟨id.toNat,s⟩) := by cases s <;> rfl

theorem leaf_atom {d : Dictionary} (a : d.sig.Atom) :
    leaf d 1 a.val.1 (sortCode a.val.2) = some (.atom a) := by
  rcases a with ⟨⟨i,k⟩,h⟩
  cases k <;> simp [leaf,atom,sortCode,sortOf,h,guard]

end Tamarin.TotalUnifyWire
