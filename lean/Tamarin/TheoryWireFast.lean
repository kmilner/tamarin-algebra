import Tamarin.TheoryWire

/-! `Theory.wireDeclarations` with the words of the builtin symbols written
once, as constants, instead of encoding their declarations on every call. -/
namespace Tamarin.Theory

/-- The words of a list of declarations. -/
def encodeDecls (ds : List Whole.Decl) : List UInt64 :=
  ds.flatMap fun d => [d.kind, d.id, d.inputs.length.toUInt64, d.output] ++ d.inputs

def dhWords : Array UInt64 :=
  (encodeDecls [⟨2, Free.exp, msgSort, [msgSort, msgSort]⟩, ⟨2, Free.inv, msgSort, [msgSort]⟩,
    ⟨2, Free.one, msgSort, []⟩, ⟨2, Free.dhNeutral, msgSort, []⟩,
    ⟨4, AC.mult, msgSort, [msgSort, msgSort]⟩]).toArray
def xorWords : Array UInt64 :=
  (encodeDecls [⟨4, AC.xor, msgSort, [msgSort, msgSort]⟩, ⟨2, Free.zero, msgSort, []⟩]).toArray
def bpWords : Array UInt64 :=
  (encodeDecls [⟨2, Free.pmult, msgSort, [msgSort, msgSort]⟩, ⟨3, C.em, msgSort, [msgSort, msgSort]⟩]).toArray
def msetWords : Array UInt64 := (encodeDecls [⟨4, AC.union, msgSort, [msgSort, msgSort]⟩]).toArray
def natWords : Array UInt64 :=
  (encodeDecls [⟨4, AC.tplus, natSort, [natSort, natSort]⟩, ⟨2, Free.tone, natSort, []⟩]).toArray

/-- The declaration words of the user symbols. -/
def userWords (sig : Signature) : Array UInt64 :=
  (encodeDecls (sig.free.toList.mapIdx (fun i arity =>
      ⟨2, base + i.toUInt64, msgSort, List.replicate arity.toNat msgSort⟩) ++
    (List.range sig.ac.toNat).map (fun j => ⟨4, base + j.toUInt64, msgSort, [msgSort, msgSort]⟩))).toArray

/-- Push `n` copies of `w`. -/
def pushCopies (acc : Array UInt64) (w : UInt64) : Nat → Array UInt64
  | 0 => acc
  | n + 1 => pushCopies (acc.push w) w n

theorem pushCopies_eq (acc : Array UInt64) (w : UInt64) (n : Nat) :
    pushCopies acc w n = acc ++ (List.replicate n w).toArray := by
  induction n generalizing acc with
  | zero => simp [pushCopies]
  | succ n ih =>
    rw [pushCopies, ih]
    apply Array.toList_inj.mp
    simp [List.replicate_succ]

/-- The words of the user free symbols from index `i` on. -/
def freeWords (acc : Array UInt64) (i : Nat) : List UInt64 → Array UInt64
  | [] => acc
  | a :: as =>
    freeWords (pushCopies ((((acc.push 2).push (base + i.toUInt64)).push a.toNat.toUInt64).push msgSort)
      msgSort a.toNat) (i + 1) as

theorem freeWords_eq (acc : Array UInt64) (i : Nat) (l : List UInt64) :
    freeWords acc i l = acc ++ (encodeDecls (l.mapIdx fun j arity =>
      (⟨2, base + (i + j).toUInt64, msgSort, List.replicate arity.toNat msgSort⟩ : Whole.Decl))).toArray := by
  induction l generalizing acc i with
  | nil => simp [freeWords, encodeDecls]
  | cons a as ih =>
    rw [freeWords, ih, pushCopies_eq]
    apply Array.toList_inj.mp
    simp only [List.mapIdx_cons, encodeDecls, List.flatMap_cons, Array.toList_append,
      Array.toList_push, Nat.add_zero, List.length_replicate]
    simp [Nat.add_assoc, Nat.add_comm 1]

/-- The words of the user AC symbols from index `j` on. -/
def acWords (acc : Array UInt64) (j : Nat) : Nat → Array UInt64
  | 0 => acc
  | n + 1 => acWords (((((((acc.push 4).push (base + j.toUInt64)).push 2).push msgSort).push msgSort).push msgSort)) (j + 1) n

theorem acWords_eq (acc : Array UInt64) (j n : Nat) :
    acWords acc j n = acc ++ (encodeDecls ((List.range' j n).map fun j =>
      (⟨4, base + j.toUInt64, msgSort, [msgSort, msgSort]⟩ : Whole.Decl))).toArray := by
  induction n generalizing acc j with
  | zero => simp [acWords, encodeDecls]
  | succ n ih =>
    rw [acWords, ih]
    apply Array.toList_inj.mp
    simp [encodeDecls, List.range'_succ]

theorem userWords_fast (sig : Signature) : userWords sig = acWords (freeWords #[] 0 sig.free.toList) 0 sig.ac.toNat := by
  rw [acWords_eq, freeWords_eq, userWords]
  apply Array.toList_inj.mp
  simp [encodeDecls, List.range_eq_range']

def declarationsFast (sig : Signature) : Array UInt64 :=
  (if sig.dh then dhWords else #[]) ++ (if sig.xor then xorWords else #[]) ++
    (if sig.bp then bpWords else #[]) ++ (if sig.mset then msetWords else #[]) ++
    (if sig.nat then natWords else #[]) ++ acWords (freeWords #[] 0 sig.free.toList) 0 sig.ac.toNat

theorem declarations_fast (sig : Signature) : sig.declarations = declarationsFast sig := by
  apply Array.toList_inj.mp
  simp only [Signature.declarations, Signature.symbols, declarationsFast, ← userWords_fast, userWords, dhWords, xorWords,
    bpWords, msetWords, natWords, encodeDecls, List.flatMap_append, Array.toList_append, List.toList_toArray]
  cases sig.dh <;> cases sig.xor <;> cases sig.bp <;> cases sig.mset <;> cases sig.nat <;> simp

def wireDeclarationsFast (flags : UInt64) (free : Array UInt64) (ac : UInt64) : Array UInt64 :=
  match Signature.ofWire flags free ac with
  | some sig => declarationsFast sig
  | none => undecodable

@[csimp] theorem wireDeclarations_eq_fast : @wireDeclarations = @wireDeclarationsFast := by
  funext flags free ac
  unfold wireDeclarations wireDeclarationsFast
  cases Signature.ofWire flags free ac with
  | some sig => exact declarations_fast sig
  | none => rfl

end Tamarin.Theory
