import Tamarin.TheoryWire
import Tamarin.CertifiedTableWire

/-! Facts about `Tamarin.Theory`: the flags word is read back exactly, the
declarations of a valid signature decode to its symbols, the arguments of a
`tamarin_theory_*` export give the packet of its table. -/
namespace Tamarin.Theory
open Whole

/-! ## Flags -/

theorem ofWire_signature (sig : Signature) :
    Signature.ofWire sig.flags sig.free sig.ac = if sig.valid then some sig else none := by
  obtain ⟨dh,xor,bp,mset,nat,free,ac⟩ := sig
  cases dh <;> cases xor <;> cases bp <;> cases mset <;> cases nat <;>
    simp [Signature.ofWire,Signature.flags]

theorem ofWire_some {flags free ac sig} (h : Signature.ofWire flags free ac = some sig) :
    sig.valid ∧ sig.flags = flags ∧ sig.free = free ∧ sig.ac = ac := by
  unfold Signature.ofWire at h
  dsimp only at h
  split at h
  · rename_i ok
    cases h
    obtain ⟨same,valid⟩ := Bool.and_eq_true_iff.mp ok
    exact ⟨valid,eq_of_beq same,rfl,rfl⟩
  · cases h

theorem ofWire_none_of_invalid {sig : Signature} (bad : sig.valid = false) :
    Signature.ofWire sig.flags sig.free sig.ac = none := by
  rw [ofWire_signature,bad]
  rfl

/-! ## Wire arguments -/

theorem wireDeclarations_valid {sig : Signature} (valid : sig.valid) :
    wireDeclarations sig.flags sig.free sig.ac = sig.declarations := by
  simp [wireDeclarations,ofWire_signature,valid]

theorem wireDeclarations_none {flags free ac} (none_ : Signature.ofWire flags free ac = none) :
    wireDeclarations flags free ac = undecodable := by
  simp [wireDeclarations,none_]

theorem wirePacket_valid {T : Table} (valid : T.valid) :
    wirePacket T.flags T.free T.ac T.nodes T.rules = T.packet := by
  simp [wirePacket,ofWire_signature,valid]

theorem wirePacket_none {flags free ac nodes rules} (none_ : Signature.ofWire flags free ac = none) :
    wirePacket flags free ac nodes rules = ⟨undecodable,#[],#[]⟩ := by
  simp [wirePacket,none_]

theorem graph_undecodable (ns : Array (Array UInt64)) : TotalUnifyWire.graph undecodable ns = none := by
  simp [TotalUnifyWire.graph,undecodable,Whole.declarations]

end Tamarin.Theory

namespace Tamarin.Theory
open Whole

/-! ## Declarations -/

private def encode (d : Decl) : List UInt64 :=
  [d.kind, d.id, d.inputs.length.toUInt64, d.output] ++ d.inputs

private def key (d : Decl) : UInt64 × UInt64 := (d.kind, d.id)

private structure Good (d : Decl) : Prop where
  output : d.output ≤ 4
  inputs : ∀ x ∈ d.inputs, x ≤ 4
  kind : d.kind = 2 ∨ ((d.kind = 3 ∨ d.kind = 4) ∧ d.inputs = [d.output, d.output])
  short : d.inputs.length < 2 ^ 64

private theorem decode_encode : ∀ (ds : List Decl), (∀ d ∈ ds, Good d) → (ds.map key).Nodup →
    Whole.declarations (ds.flatMap encode) = some ds
  | [], _, _ => by simp [Whole.declarations]
  | d :: ds, good, nodup => by
    have g := good d List.mem_cons_self
    have ih := decode_encode ds (fun e he => good e (List.mem_cons_of_mem _ he))
      (List.nodup_cons.mp nodup).2
    have fresh := (List.nodup_cons.mp nodup).1
    have len : d.inputs.length.toUInt64.toNat = d.inputs.length := by
      simp only [Nat.toUInt64_eq]
      exact Nat.mod_eq_of_lt g.short
    simp only [List.flatMap_cons, encode, List.cons_append]
    rw [Whole.declarations]
    have inputsOK : (d.inputs.all fun x => decide (x ≤ 4)) = true :=
      List.all_eq_true.mpr fun x hx => decide_eq_true (g.inputs x hx)
    have kindOK : (d.kind == 2 || (d.kind == 3 || d.kind == 4) && d.inputs == [d.output, d.output]) = true := by
      rcases g.kind with h | ⟨h, e⟩
      · simp [h]
      · rcases h with h | h <;> simp [h, e]
    have freshOK (e : Decl) (he : e ∈ ds) (k : e.kind = d.kind) : ¬e.id = d.id := fun i =>
      fresh (List.mem_map.mpr ⟨e, he, by simp [key, k, i]⟩)
    have freshAll : (∀ e ∈ ds, e.kind = d.kind → ¬e.id = d.id) = True := eq_true freshOK
    simp [len, ih, g.output, inputsOK, kindOK, freshAll, guard]

private def goodB (d : Decl) : Bool :=
  d.output ≤ 4 && d.inputs.all (· ≤ 4) &&
    (d.kind == 2 || (d.kind == 3 || d.kind == 4) && d.inputs == [d.output, d.output]) &&
    decide (d.inputs.length < 2 ^ 64)

private theorem good_of_goodB {d : Decl} (h : goodB d) : Good d := by
  simp only [goodB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    beq_iff_eq] at h
  obtain ⟨⟨⟨out, ins⟩, kind⟩, short⟩ := h
  exact ⟨out, ins, kind, short⟩

private def builtinOf (dh xor bp mset nat : Bool) : List Decl :=
  (({ dh, xor, bp, mset, nat, free := #[], ac := 0 } : Signature).symbols)

private theorem builtin_facts (dh xor bp mset nat : Bool) :
    (builtinOf dh xor bp mset nat).all goodB ∧ ((builtinOf dh xor bp mset nat).map key).Nodup ∧
      (builtinOf dh xor bp mset nat).all (fun d => d.id < base) := by
  cases dh <;> cases xor <;> cases bp <;> cases mset <;> cases nat <;> decide

private def userFree (sig : Signature) : List Decl :=
  sig.free.toList.mapIdx fun i arity => ⟨2, base + i.toUInt64, msgSort, List.replicate arity.toNat msgSort⟩

private def userAC (sig : Signature) : List Decl :=
  (List.range sig.ac.toNat).map fun j => ⟨4, base + j.toUInt64, msgSort, [msgSort, msgSort]⟩

private theorem symbols_split (sig : Signature) :
    sig.symbols = builtinOf sig.dh sig.xor sig.bp sig.mset sig.nat ++ userFree sig ++ userAC sig := by
  simp [Signature.symbols, builtinOf, userFree, userAC]

private theorem uid_toNat {i : Nat} (h : i ≤ limit) : (base + i.toUInt64).toNat = 16 + i := by
  simp only [base, limit, Nat.toUInt64_eq] at h ⊢
  rw [UInt64.toNat_add, UInt64.toNat_ofNat']
  simp only [UInt64.reduceToNat]
  omega

private theorem nodup_range_map {α} {n : Nat} {f : Nat → α}
    (inj : ∀ i j, i < n → j < n → f i = f j → i = j) : ((List.range n).map f).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  refine List.nodup_range.imp_of_mem ?_
  intro a b ha hb ne eq
  exact ne (inj a b (List.mem_range.mp ha) (List.mem_range.mp hb) eq)

private theorem userFree_keys (sig : Signature) :
    (userFree sig).map key = (List.range sig.free.size).map fun i => ((2 : UInt64), base + i.toUInt64) := by
  apply List.ext_getElem
  · simp [userFree]
  · intro i h₁ h₂
    simp [userFree, key]

private theorem userAC_keys (sig : Signature) :
    (userAC sig).map key = (List.range sig.ac.toNat).map fun j => ((4 : UInt64), base + j.toUInt64) := by
  simp [userAC, key, Function.comp_def]

private theorem symbols_good (sig : Signature) : ∀ d ∈ sig.symbols, Good d := by
  rw [symbols_split]
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · rcases List.mem_append.mp hd with hd | hd
    · exact good_of_goodB (List.all_eq_true.mp (builtin_facts ..).1 d hd)
    · simp only [userFree, List.mem_mapIdx] at hd
      obtain ⟨i, _, rfl⟩ := hd
      refine ⟨by simp [msgSort], ?_, .inl rfl, ?_⟩
      · intro x hx
        rw [List.eq_of_mem_replicate hx]
        simp [msgSort]
      · simpa using UInt64.toNat_lt _
  · simp only [userAC, List.mem_map] at hd
    obtain ⟨j, _, rfl⟩ := hd
    exact ⟨by simp [msgSort], by simp [msgSort], .inr ⟨.inr rfl, rfl⟩, by simp⟩

private theorem symbols_nodup {sig : Signature} (valid : sig.valid) : (sig.symbols.map key).Nodup := by
  simp only [Signature.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
  obtain ⟨⟨⟨_, size⟩, _⟩, acSize⟩ := valid
  obtain ⟨_, builtinNodup, small⟩ := builtin_facts sig.dh sig.xor sig.bp sig.mset sig.nat
  have userIds : ∀ k ∈ (userFree sig ++ userAC sig).map key, 16 ≤ k.2.toNat := by
    intro k hk
    rw [List.map_append, userFree_keys, userAC_keys] at hk
    rcases List.mem_append.mp hk with hk | hk
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
      rw [uid_toNat (by have := List.mem_range.mp hi; omega)]
      omega
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hk
      rw [uid_toNat (by have := List.mem_range.mp hj; omega)]
      omega
  have userNodup : ((userFree sig ++ userAC sig).map key).Nodup := by
    rw [List.map_append, userFree_keys, userAC_keys, List.nodup_append]
    refine ⟨nodup_range_map ?_, nodup_range_map ?_, ?_⟩
    · intro i j hi hj eq
      have := congrArg (fun k : UInt64 × UInt64 => k.2.toNat) eq
      simp only at this
      rw [uid_toNat (by omega), uid_toNat (by omega)] at this
      omega
    · intro i j hi hj eq
      have := congrArg (fun k : UInt64 × UInt64 => k.2.toNat) eq
      simp only at this
      rw [uid_toNat (by omega), uid_toNat (by omega)] at this
      omega
    · intro a ha b hb eq
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb
      cases eq
  rw [symbols_split, List.append_assoc, List.map_append, List.nodup_append]
  refine ⟨builtinNodup, userNodup, ?_⟩
  intro a ha b hb eq
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
  have low := List.all_eq_true.mp small d hd
  have high := userIds b hb
  rw [← eq] at high
  simp only [key, base] at low high
  have := UInt64.lt_iff_toNat_lt.mp (of_decide_eq_true low)
  simp only [UInt64.reduceToNat] at this
  omega

/-- The declarations of a valid signature decode to its symbols. -/
theorem declarations_decode {sig : Signature} (valid : sig.valid) :
    Whole.declarations sig.declarations.toList = some sig.symbols := by
  simp only [Signature.declarations, List.toList_toArray]
  exact decode_encode sig.symbols (symbols_good sig) (symbols_nodup valid)

/-! ## Decoded dictionaries -/

private theorem graph_decls {decls ns} {d : TotalUnifyWire.Dictionary} {ts}
    (h : TotalUnifyWire.graph decls ns = some ⟨d, ts⟩) : Whole.declarations decls.toList = some d.decls := by
  unfold TotalUnifyWire.graph at h
  cases hd : Whole.declarations decls.toList with
  | none => simp [hd] at h
  | some ds =>
    simp only [hd, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, same⟩ := h
    cases same
    rfl

/-- The dictionary of a decoded query has exactly the symbols of the signature. -/
theorem query_symbols {sig : Signature} {ns es} {d : TotalUnifyWire.Dictionary} {p}
    (h : sig.query ns es = some ⟨d, p⟩) : d.decls = sig.symbols := by
  unfold Signature.query at h
  split at h
  · rename_i valid
    unfold TotalUnifyWire.input at h
    cases hg : TotalUnifyWire.graph sig.declarations ns with
    | none => simp [hg] at h
    | some g =>
      obtain ⟨d', ts⟩ := g
      simp only [hg, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff] at h
      obtain ⟨_, _, same⟩ := h
      cases same
      exact Option.some_inj.mp ((graph_decls hg).symm.trans (declarations_decode valid))
  · cases h

/-- The dictionary of a decoded table has exactly the symbols of its signature. -/
theorem input_symbols {T : Table} {d : TotalUnifyWire.Dictionary} {rs q}
    (h : T.input = some ⟨d, rs, q⟩) : d.decls = T.symbols := by
  unfold Table.input at h
  split at h
  · rename_i valid
    unfold TableWire.input at h
    cases hg : TotalUnifyWire.graph T.packet.ds T.packet.ns with
    | none => simp [hg] at h
    | some g =>
      obtain ⟨d', ts⟩ := g
      simp only [hg, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff] at h
      obtain ⟨_, _, _, _, same⟩ := h
      cases same
      exact Option.some_inj.mp ((graph_decls hg).symm.trans (declarations_decode valid))
  · cases h

/-! ## The packets of the exports -/

private theorem query_undecodable (ns es) : TotalUnifyWire.input undecodable ns es = none := by
  simp [TotalUnifyWire.input, graph_undecodable]

private theorem table_undecodable (ns es obs) : TableWire.input undecodable ns es obs = none := by
  simp [TableWire.input, graph_undecodable]

private theorem reduce_undecodable (ns es extra root) :
    SessionReductionWire.input undecodable ns es extra root = none := by
  simp [SessionReductionWire.input, graph_undecodable]

private theorem check_undecodable (ns es extra roots family) :
    SessionVariantCheckWire.input undecodable ns es extra roots family = none := by
  simp [SessionVariantCheckWire.input, graph_undecodable]

theorem wire_query (sig : Signature) (ns : Array (Array UInt64)) (es : Array UInt64) :
    TotalUnifyWire.input (wireDeclarations sig.flags sig.free sig.ac) ns es = sig.query ns es := by
  unfold Signature.query
  cases h : sig.valid
  · rw [wireDeclarations_none (ofWire_none_of_invalid h), query_undecodable]
    rfl
  · rw [wireDeclarations_valid h]
    rfl

theorem wire_query_none {flags free ac} (none_ : Signature.ofWire flags free ac = none)
    (ns : Array (Array UInt64)) (es : Array UInt64) :
    TotalUnifyWire.input (wireDeclarations flags free ac) ns es = none := by
  rw [wireDeclarations_none none_, query_undecodable]

private theorem wirePacket_table (T : Table) :
    wirePacket T.flags T.free T.ac T.nodes T.rules =
      if T.valid then T.packet else ⟨undecodable, #[], #[]⟩ := by
  cases h : T.valid
  · rw [wirePacket_none (ofWire_none_of_invalid h)]
    rfl
  · rw [wirePacket_valid h]
    rfl

theorem wire_table (T : Table) :
    let p := wirePacket T.flags T.free T.ac T.nodes T.rules
    TableWire.input p.ds p.ns p.es #[] = T.input := by
  unfold Table.input
  rw [wirePacket_table]
  cases T.valid
  · exact table_undecodable _ _ _
  · rfl

theorem wire_path (T : Table) (extra : Array (Array UInt64)) (root : UInt64) :
    let p := wirePacket T.flags T.free T.ac T.nodes T.rules
    TableWire.input p.ds (p.ns ++ moveRows p.ns.size extra) p.es #[place p.ns.size extra.size root] =
      T.pathInput extra root := by
  unfold Table.pathInput
  rw [wirePacket_table]
  cases T.valid
  · exact table_undecodable _ _ _
  · rfl

theorem wire_reduce (T : Table) (extra : Array (Array UInt64)) (root : UInt64) :
    let p := wirePacket T.flags T.free T.ac T.nodes T.rules
    SessionReductionWire.input p.ds p.ns p.es (moveRows p.ns.size extra) (place p.ns.size extra.size root) =
      T.reduceInput extra root := by
  unfold Table.reduceInput
  rw [wirePacket_table]
  cases T.valid
  · exact reduce_undecodable _ _ _ _
  · rfl

theorem wire_check (T : Table) (extra : Array (Array UInt64)) (roots : Array UInt64)
    (family : Array (Array UInt64)) :
    let p := wirePacket T.flags T.free T.ac T.nodes T.rules
    SessionVariantCheckWire.input p.ds p.ns p.es (moveRows p.ns.size extra)
      (roots.map (place p.ns.size extra.size)) (family.map (·.map (place p.ns.size extra.size))) =
      T.checkInput extra roots family := by
  unfold Table.checkInput
  rw [wirePacket_table]
  cases T.valid
  · exact check_undecodable _ _ _ _ _
  · rfl

theorem wire_none {flags free ac nodes rules} (none_ : Signature.ofWire flags free ac = none) :
    let p := wirePacket flags free ac nodes rules
    (∀ obs, TableWire.input p.ds p.ns p.es obs = none) ∧
    (∀ more obs, TableWire.input p.ds (p.ns ++ more) p.es obs = none) ∧
    (∀ extra root, SessionReductionWire.input p.ds p.ns p.es extra root = none) ∧
    (∀ extra roots family, SessionVariantCheckWire.input p.ds p.ns p.es extra roots family = none) := by
  simp only [wirePacket_none none_]
  exact ⟨table_undecodable _ _, fun _ => table_undecodable _ _, reduce_undecodable _ _,
    check_undecodable _ _⟩

/-- The table of a session call is the table of the theory. -/
theorem reduceInput_table {T : Table} {extra root} {d : TotalUnifyWire.Dictionary} {rs t}
    (h : T.reduceInput extra root = some ⟨d, rs, t⟩) : T.input = some ⟨d, rs, []⟩ := by
  unfold Table.reduceInput at h
  unfold Table.input
  split at h
  · rename_i valid
    simp only [valid, ite_true]
    exact SessionReductionWire.input_table h
  · cases h

theorem checkInput_table {T : Table} {extra roots family} {d : TotalUnifyWire.Dictionary} {rs q members}
    (h : T.checkInput extra roots family = some ⟨d, rs, q, members⟩) : T.input = some ⟨d, rs, []⟩ := by
  unfold Table.checkInput at h
  unfold Table.input
  split at h
  · rename_i valid
    simp only [valid, ite_true]
    exact SessionVariantCheckWire.input_table h
  · cases h

end Tamarin.Theory
