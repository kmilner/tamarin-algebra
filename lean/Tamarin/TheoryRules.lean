import Tamarin.TheoryFacts

/-! The rules a theory table decodes to: the denotations of the builtin rules
(`Theory.Signature.builtinEquations`) followed by the rules of the user's own
block, read by itself. -/
namespace Tamarin.Theory
open TotalUnifyWire

/-! ## Decoding rows one at a time -/

private abbrev step (d : Dictionary) (acc : Array (Tamarin.Term d.sig)) (r : Array UInt64) :
    Option (Array (Tamarin.Term d.sig)) := do return acc.push (← node d acc r)

private theorem fold_extends {d : Dictionary} :
    ∀ (xs : List (Array UInt64)) (acc b : Array (Tamarin.Term d.sig)),
      xs.foldlM (step d) acc = some b →
      b.size = acc.size + xs.length ∧ ∀ i, i < acc.size → b[i]? = acc[i]?
  | [], acc, b, h => by
    simp only [List.foldlM_nil] at h
    cases h
    simp
  | x :: xs, acc, b, h => by
    simp only [List.foldlM_cons] at h
    cases hn : node d acc x with
    | none => simp [step, hn] at h
    | some v =>
      simp only [step, hn, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
      obtain ⟨sz, pre⟩ := fold_extends xs _ _ h
      refine ⟨by simp only [sz, Array.size_push, List.length_cons]; omega, fun i hi => ?_⟩
      rw [pre i (by simp only [Array.size_push]; omega), Array.getElem?_push]
      simp only [show i ≠ acc.size by omega, ite_false]

/-! ## The rows of a term -/

mutual
private def kinded : Theory.Term → Bool
  | .var _ => true
  | .app k _ args => 2 ≤ k && kindedArgs args

private def kindedArgs : List Theory.Term → Bool
  | [] => true
  | t :: ts => kinded t && kindedArgs ts
end

private theorem append_cancel {α} {R S S' : Array α} (h : R ++ S = R ++ S') : S = S' := by
  apply Array.toList_inj.mp
  have := congrArg Array.toList h
  simp only [Array.toList_append] at this
  exact List.append_cancel_left this

mutual
private theorem rows_prefix : ∀ (t : Theory.Term) (R : Array (Array UInt64)), ∃ S, t.rows R = R ++ S
  | .var i, R => ⟨#[#[0, i, msgSort]], by simp [Term.rows]⟩
  | .app k id args, R => by
    obtain ⟨S, cs, h⟩ := argRows_prefix args R #[]
    refine ⟨S.push (#[k, id] ++ (#[] ++ cs)), ?_⟩
    simp only [Term.rows, h, Array.append_push]

private theorem argRows_prefix : ∀ (ts : List Theory.Term) (R : Array (Array UInt64)) (roots : Array UInt64),
    ∃ S cs, Term.argRows ts R roots = (R ++ S, roots ++ cs)
  | [], R, roots => ⟨#[], #[], by simp [Term.argRows]⟩
  | t :: ts, R, roots => by
    obtain ⟨S₁, h₁⟩ := rows_prefix t R
    obtain ⟨S₂, cs, h₂⟩ := argRows_prefix ts (t.rows R) (roots.push ((t.rows R).size - 1).toUInt64)
    refine ⟨S₁ ++ S₂, #[((t.rows R).size - 1).toUInt64] ++ cs, ?_⟩
    simp only [Term.argRows]
    rw [h₂, h₁]
    simp [Array.append_assoc]
end

private theorem index_lt {α} {xs : Array α} {i : Nat} {u : α} (h : xs[i]? = some u) : i < xs.size := by
  apply Classical.byContradiction
  intro no
  rw [Array.getElem?_eq_none (by omega)] at h
  cases h

private theorem toNat_small {n : Nat} (h : n < UInt64.size) : n.toUInt64.toNat = n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

mutual
private theorem rows_denote {d : Dictionary} : ∀ (t : Theory.Term), kinded t = true →
    ∀ (R S : Array (Array UInt64)) (acc b : Array (Tamarin.Term d.sig)),
      t.rows R = R ++ S → acc.size = R.size → (R ++ S).size < UInt64.size →
      S.toList.foldlM (step d) acc = some b →
      ∃ u, t.denote d = some u ∧ b[(R ++ S).size - 1]? = some u
  | .var i, _, R, S, acc, b, hr, hs, _, hf => by
    have hS : S = #[#[0, i, msgSort]] := append_cancel (hr.symm.trans (by simp [Term.rows]))
    subst hS
    simp [step, node, leaf, msgSort, sortOf, guard] at hf
    subst hf
    refine ⟨_, rfl, ?_⟩
    rw [show (R ++ #[#[0, i, msgSort]]).size - 1 = acc.size by simp [hs]]
    simp
  | .app k id args, hk, R, S, acc, b, hr, hs, hsz, hf => by
    simp only [kinded, Bool.and_eq_true, decide_eq_true_eq] at hk
    obtain ⟨S₁, cs, ha⟩ := argRows_prefix args R #[]
    have hS : S = S₁.push (#[k, id] ++ cs) :=
      append_cancel (hr.symm.trans (by simp only [Term.rows, ha, Array.append_push, Array.empty_append]))
    subst hS
    rw [Array.toList_push, List.foldlM_append] at hf
    cases ha1 : S₁.toList.foldlM (step d) acc with
    | none => simp [ha1] at hf
    | some a =>
      simp only [ha1, Option.bind_eq_bind, Option.bind_some] at hf
      have sz1 : (R ++ S₁).size < UInt64.size := by
        simp only [Array.size_append, Array.size_push] at hsz ⊢
        omega
      obtain ⟨us, hus, hcs⟩ := argRows_denote args hk.2 R #[] S₁ cs acc a ha hs sz1 ha1
      have aSize := (fold_extends _ _ _ ha1).1
      simp only [List.foldlM_cons, List.foldlM_nil, step] at hf
      cases hn : node d a (#[k, id] ++ cs) with
      | none => simp [hn] at hf
      | some v =>
        simp only [hn, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hf
        cases hf
        have big : ¬ k ≤ 1 := by
          intro le
          have := UInt64.le_iff_toNat_le.mp le
          have := UInt64.le_iff_toNat_le.mp hk.1
          simp only [UInt64.reduceToNat] at *
          omega
        have nodeApp : node d a (#[k, id] ++ cs) = app d k id us := by
          unfold node
          simp [big, hcs]
        refine ⟨v, ?_, ?_⟩
        · simp only [Term.denote, hus, Option.bind_eq_bind, Option.bind_some]
          rw [← nodeApp, hn]
        · have : (R ++ S₁.push (#[k, id] ++ cs)).size - 1 = a.size := by
            simp only [Array.size_append, Array.size_push, aSize, hs, Array.length_toList]
            omega
          rw [this]
          simp

private theorem argRows_denote {d : Dictionary} : ∀ (ts : List Theory.Term), kindedArgs ts = true →
    ∀ (R : Array (Array UInt64)) (roots : Array UInt64) (S : Array (Array UInt64)) (cs : Array UInt64)
      (acc b : Array (Tamarin.Term d.sig)),
      Term.argRows ts R roots = (R ++ S, roots ++ cs) → acc.size = R.size → (R ++ S).size < UInt64.size →
      S.toList.foldlM (step d) acc = some b →
      ∃ us, Term.denoteArgs d ts = some us ∧ cs.toList.mapM (fun i => b[i.toNat]?) = some us
  | [], _, R, roots, S, cs, acc, b, h, _, _, hf => by
    simp only [Term.argRows, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have e1 : S = #[] := append_cancel (h1.symm.trans Array.append_empty.symm)
    have e2 : cs = #[] := append_cancel (h2.symm.trans Array.append_empty.symm)
    subst e1 e2
    simp [Term.denoteArgs]
  | t :: ts, hk, R, roots, S, cs, acc, b, h, hs, hsz, hf => by
    simp only [kindedArgs, Bool.and_eq_true] at hk
    obtain ⟨S₁, h₁⟩ := rows_prefix t R
    obtain ⟨S₂, cs₂, h₂⟩ := argRows_prefix ts (t.rows R) (roots.push ((t.rows R).size - 1).toUInt64)
    have hall : Term.argRows (t :: ts) R roots =
        (R ++ (S₁ ++ S₂), roots ++ (#[((t.rows R).size - 1).toUInt64] ++ cs₂)) := by
      simp only [Term.argRows]
      rw [h₂, h₁]
      simp [Array.append_assoc]
    rw [hall] at h
    simp only [Prod.mk.injEq] at h
    have hS := append_cancel h.1
    have hcs := append_cancel h.2
    subst hS hcs
    rw [Array.toList_append, List.foldlM_append] at hf
    cases ha : S₁.toList.foldlM (step d) acc with
    | none => simp [ha] at hf
    | some a =>
      simp only [ha, Option.bind_eq_bind, Option.bind_some] at hf
      have sz1 : (R ++ S₁).size < UInt64.size := by
        simp only [Array.size_append] at hsz ⊢
        omega
      obtain ⟨u, hu, hau⟩ := rows_denote t hk.1 R S₁ acc a h₁ hs sz1 ha
      have aSize := (fold_extends _ _ _ ha).1
      obtain ⟨us, hus, hcs2⟩ := argRows_denote ts hk.2 (R ++ S₁) _ S₂ cs₂ a b
        (by rw [← h₁]; exact h₂) (by simp [aSize, hs]) (by simpa [Array.append_assoc] using hsz) hf
      have bExt := (fold_extends _ _ _ hf).2
      refine ⟨u :: us, by simp [Term.denoteArgs, hu, hus], ?_⟩
      have rnat : ((t.rows R).size - 1).toUInt64.toNat = (R ++ S₁).size - 1 := by
        rw [h₁]
        exact toNat_small (by omega)
      have hb : b[((t.rows R).size - 1).toUInt64.toNat]? = some u := by
        rw [rnat, bExt _ (index_lt hau), hau]
      rw [show (#[((t.rows R).size - 1).toUInt64] ++ cs₂).toList =
          ((t.rows R).size - 1).toUInt64 :: cs₂.toList by simp, List.mapM_cons, hb, hcs2]
      rfl
end

/-! ## The rows of a list of rules -/

private def pairEq (d : Dictionary) (p : Theory.Term × Theory.Term) : Option (Equation d.sig) := do
  return ⟨← p.1.denote d, ← p.2.denote d⟩

private theorem builtinEquations_eq (sig : Signature) (d : Dictionary) :
    sig.builtinEquations d = sig.builtinRules.mapM (pairEq d) := rfl

private theorem ruleRows_prefix : ∀ (rules : List (Theory.Term × Theory.Term))
    (R : Array (Array UInt64)) (roots : Array UInt64),
    ∃ S es, ruleRows rules (R, roots) = (R ++ S, roots ++ es)
  | [], R, roots => ⟨#[], #[], by simp [ruleRows]⟩
  | (l, r) :: rest, R, roots => by
    obtain ⟨S₁, h₁⟩ := rows_prefix l R
    obtain ⟨S₂, h₂⟩ := rows_prefix r (l.rows R)
    obtain ⟨S₃, es, h₃⟩ := ruleRows_prefix rest (r.rows (l.rows R))
      (roots ++ #[((l.rows R).size - 1).toUInt64, ((r.rows (l.rows R)).size - 1).toUInt64])
    refine ⟨S₁ ++ S₂ ++ S₃,
      #[((l.rows R).size - 1).toUInt64, ((r.rows (l.rows R)).size - 1).toUInt64] ++ es, ?_⟩
    simp only [ruleRows]
    rw [h₃, h₂, h₁]
    simp only [Array.append_assoc]

private theorem ruleRows_denote {d : Dictionary} : ∀ (rules : List (Theory.Term × Theory.Term)),
    rules.all (fun p => kinded p.1 && kinded p.2) = true →
    ∀ (R S : Array (Array UInt64)) (roots es : Array UInt64) (acc b : Array (Tamarin.Term d.sig)),
      ruleRows rules (R, roots) = (R ++ S, roots ++ es) → acc.size = R.size →
      (R ++ S).size < UInt64.size → S.toList.foldlM (step d) acc = some b →
      ∃ eqs, rules.mapM (pairEq d) = some eqs ∧
        ∀ ts : Array (Tamarin.Term d.sig), (∀ i, i < b.size → ts[i]? = b[i]?) → ∀ rest,
          equations ts (es.toList ++ rest) = (equations ts rest).map (eqs ++ ·)
  | [], _, R, S, roots, es, acc, b, h, _, _, hf => by
    simp only [ruleRows, Prod.mk.injEq] at h
    have e1 : S = #[] := append_cancel (h.1.symm.trans Array.append_empty.symm)
    have e2 : es = #[] := append_cancel (h.2.symm.trans Array.append_empty.symm)
    subst e1 e2
    refine ⟨[], rfl, fun ts _ rest => ?_⟩
    show equations ts rest = _
    cases equations ts rest <;> rfl
  | (l, r) :: rest, hk, R, S, roots, es, acc, b, h, hs, hsz, hf => by
    simp only [List.all_cons, Bool.and_eq_true] at hk
    obtain ⟨S₁, h₁⟩ := rows_prefix l R
    obtain ⟨S₂, h₂⟩ := rows_prefix r (l.rows R)
    obtain ⟨S₃, es₃, h₃⟩ := ruleRows_prefix rest (r.rows (l.rows R))
      (roots ++ #[((l.rows R).size - 1).toUInt64, ((r.rows (l.rows R)).size - 1).toUInt64])
    have hall : ruleRows ((l, r) :: rest) (R, roots) = (R ++ (S₁ ++ S₂ ++ S₃), roots ++
        (#[((l.rows R).size - 1).toUInt64, ((r.rows (l.rows R)).size - 1).toUInt64] ++ es₃)) := by
      simp only [ruleRows]
      rw [h₃, h₂, h₁]
      simp only [Array.append_assoc]
    rw [hall] at h
    simp only [Prod.mk.injEq] at h
    have hS := append_cancel h.1
    have hes := append_cancel h.2
    subst hS hes
    rw [h₁] at h₂
    rw [Array.toList_append, Array.toList_append, List.foldlM_append, List.foldlM_append] at hf
    cases ha₁ : S₁.toList.foldlM (step d) acc with
    | none => simp only [ha₁, Option.bind_eq_bind, Option.bind_none] at hf; cases hf
    | some a₁ =>
    cases ha₂ : S₂.toList.foldlM (step d) a₁ with
    | none => simp only [ha₁, ha₂, Option.bind_eq_bind, Option.bind_some, Option.bind_none] at hf; cases hf
    | some a₂ =>
    simp only [ha₁, ha₂, Option.bind_eq_bind, Option.bind_some] at hf
    simp only [Array.size_append] at hsz
    have e₁ := fold_extends _ _ _ ha₁
    have e₂ := fold_extends _ _ _ ha₂
    have e₃ := fold_extends _ _ _ hf
    obtain ⟨u₁, hu₁, hau₁⟩ := rows_denote l hk.1.1 R S₁ acc a₁ h₁ hs
      (by simp only [Array.size_append]; omega) ha₁
    obtain ⟨u₂, hu₂, hau₂⟩ := rows_denote r hk.1.2 (R ++ S₁) S₂ a₁ a₂ h₂
      (by simp [e₁.1, hs]) (by simp only [Array.size_append]; omega) ha₂
    obtain ⟨eqs, heqs, hrest⟩ := ruleRows_denote rest hk.2 (R ++ S₁ ++ S₂) S₃ _ es₃ a₂ b
      (by rw [← h₂, ← h₁]; exact h₃) (by simp [e₂.1, e₁.1, hs]; omega)
      (by simp only [Array.size_append]; omega) hf
    refine ⟨⟨u₁, u₂⟩ :: eqs, ?_, fun ts ext more => ?_⟩
    · simp [List.mapM_cons, pairEq, hu₁, hu₂, heqs]
    · have lt₁ := index_lt hau₁
      have lt₂ := index_lt hau₂
      have l₁ : ts[((l.rows R).size - 1).toUInt64.toNat]? = some u₁ := by
        rw [h₁, toNat_small (by simp only [Array.size_append]; omega), ext _ (by omega),
          e₃.2 _ (by omega), e₂.2 _ (by omega), hau₁]
      have l₂ : ts[((r.rows (l.rows R)).size - 1).toUInt64.toNat]? = some u₂ := by
        rw [h₁, h₂, toNat_small (by simp only [Array.size_append]; omega), ext _ (by omega),
          e₃.2 _ (by omega), hau₂]
      have tail := hrest ts ext more
      simp only [Array.toList_append, List.cons_append, List.nil_append, equations, l₁, l₂, tail]
      cases equations ts more <;> rfl

/-! ## The user's block -/

private def moveRow (off k : Nat) (row : Array UInt64) : Array UInt64 :=
  match row.toList with
  | kind :: id :: children => if kind ≤ 1 then row else (kind :: id :: children.map (place off k)).toArray
  | _ => row

private theorem moveRows_toList (off : Nat) (rows : Array (Array UInt64)) :
    (moveRows off rows).toList = rows.toList.mapIdx (moveRow off) := by
  simp only [moveRows, Array.toList_mapIdx]
  rfl

private theorem place_get {α} {a V : Array α} {off k : Nat} (ha : a.size = off) (hV : V.size = k)
    (small : off + k < UInt64.size) (i : UInt64) : (a ++ V)[(place off k i).toNat]? = V[i.toNat]? := by
  unfold place
  rw [toNat_small (by have := Nat.min_le_right i.toNat k; omega),
    Array.getElem?_append_right (by omega)]
  rw [show off + min i.toNat k - a.size = min i.toNat k by omega]
  by_cases lt : i.toNat < k
  · rw [Nat.min_eq_left (by omega)]
  · rw [Nat.min_eq_right (by omega), Array.getElem?_eq_none (by omega),
      Array.getElem?_eq_none (by omega)]

private theorem node_moved {d : Dictionary} {a V : Array (Tamarin.Term d.sig)} {off k : Nat}
    (ha : a.size = off) (hV : V.size = k) (small : off + k < UInt64.size) (row : Array UInt64) :
    node d (a ++ V) (moveRow off k row) = node d V row := by
  unfold moveRow
  split
  · rename_i kind id children hrow
    split
    · rename_i le
      unfold node
      simp only [hrow, le, ite_true]
    · rename_i big
      have fe : (fun i : UInt64 => (a ++ V)[(place off k i).toNat]?) = fun i => V[i.toNat]? :=
        funext (place_get ha hV small)
      unfold node
      simp only [hrow, big, ite_false, List.mapM_map, Function.comp_def, fe]
  · rename_i hrow
    unfold node
    split
    · rename_i k' id' tail h'
      exact absurd h' (hrow k' id' tail)
    · rfl

private theorem fold_moved {d : Dictionary} {a : Array (Tamarin.Term d.sig)} {off : Nat}
    (ha : a.size = off) : ∀ (L : List (Array UInt64)) (k : Nat) (V : Array (Tamarin.Term d.sig)),
      V.size = k → off + k + L.length ≤ UInt64.size →
      (L.mapIdx (fun i => moveRow off (i + k))).foldlM (step d) (a ++ V) =
        (L.foldlM (step d) V).map (a ++ ·)
  | [], _, V, _, _ => by simp
  | x :: L, k, V, hV, small => by
    simp only [List.length_cons] at small
    rw [List.mapIdx_cons, List.foldlM_cons, List.foldlM_cons]
    simp only [Nat.zero_add, step]
    rw [node_moved ha hV (by omega) x]
    cases hn : node d V x with
    | none => rfl
    | some v =>
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      rw [Array.push_append]
      have shift : (fun i => moveRow off (i + 1 + k)) = (fun i => moveRow off (i + (k + 1))) := by
        funext i
        rw [Nat.add_assoc, Nat.add_comm 1 k]
      rw [shift]
      exact fold_moved ha L (k + 1) (V.push v) (by simp [hV]) (by omega)

private def atomOf (row : Array UInt64) : Option (UInt64 × SortId) :=
  match row.toList with
  | [1, id, s] => some (id, sortOf s)
  | _ => none

private theorem atom_moved (off k : Nat) (row : Array UInt64) : atomOf (moveRow off k row) = atomOf row := by
  unfold moveRow
  split
  · rename_i kind id children hrow
    split
    · rfl
    · rename_i big
      have : kind ≠ 1 := fun e => big (by rw [e]; decide)
      unfold atomOf
      simp only [hrow]
      split
      · rename_i h
        simp only [List.cons.injEq] at h
        exact absurd h.1 this
      · split
        · rename_i h
          simp only [List.cons.injEq] at h
          exact absurd h.1 this
        · rfl
  · rfl

private theorem atoms_mapIdx : ∀ (L : List (Array UInt64)) (g : Nat → Array UInt64 → Array UInt64),
    (∀ k r, atomOf (g k r) = atomOf r) → (L.mapIdx g).filterMap atomOf = L.filterMap atomOf
  | [], _, _ => rfl
  | x :: L, g, hg => by
    rw [List.mapIdx_cons, List.filterMap_cons, List.filterMap_cons, hg,
      atoms_mapIdx L (fun i => g (i + 1)) (fun k r => hg (k + 1) r)]

private theorem graph_eq (ds : Array UInt64) (ns : Array (Array UInt64)) :
    graph ds ns = (Whole.declarations ds.toList).bind fun dl =>
      (ns.toList.foldlM (step ⟨dl, (ns.toList.filterMap atomOf).eraseDups⟩) #[]).bind
        fun ts => some ⟨⟨dl, (ns.toList.filterMap atomOf).eraseDups⟩, ts⟩ := by
  unfold graph
  simp only [Array.foldlM_toList]
  rfl

private theorem equations_map {s : Tamarin.Signature} {ts U : Array (Tamarin.Term s)} {g : UInt64 → UInt64}
    (hg : ∀ x, ts[(g x).toNat]? = U[x.toNat]?) :
    ∀ xs : List UInt64, equations ts (xs.map g) = equations U xs
  | [] => rfl
  | [_] => rfl
  | i :: j :: rest => by
    simp only [List.map_cons, equations, hg, equations_map hg rest]

/-! ## The decoded table -/

private theorem builtin_closed (dh xor bp : Bool) :
    let rules := (⟨dh, xor, bp, false, false, #[], 0⟩ : Signature).builtinRules
    rules.all (fun p => kinded p.1 && kinded p.2) = true ∧
      (ruleRows rules (#[], #[])).1.size < 1000 ∧
      (ruleRows rules (#[], #[])).1.toList.filterMap atomOf = [] := by
  cases dh <;> cases xor <;> cases bp <;> decide +kernel

private theorem builtinRules_flags (sig : Signature) :
    sig.builtinRules = (⟨sig.dh, sig.xor, sig.bp, false, false, #[], 0⟩ : Signature).builtinRules := rfl

/-- The rules of a decoded table are the denotations of the builtin rules
followed by rules `us`. Without user rules `us` is empty; when the packet has
fewer than `2^64` rows, `us` are the rules of the user's block decoded by
itself, over the same dictionary. -/
theorem input_rules {T : Table} {d : Dictionary} {rs q} (h : T.input = some ⟨d, rs, q⟩) :
    ∃ bs us, T.builtinEquations d = some bs ∧ rs = bs ++ us ∧ (T.rules = #[] → us = []) ∧
      (T.packet.ns.size < UInt64.size →
        TableWire.input T.declarations T.nodes T.rules #[] = some ⟨d, us, []⟩) := by
  unfold Table.input at h
  split at h
  case isFalse => cases h
  obtain ⟨kindedB, smallB, atomsB⟩ := builtin_closed T.dh T.xor T.bp
  rw [← builtinRules_flags] at kindedB smallB atomsB
  rcases hB : ruleRows T.builtinRules (#[], #[]) with ⟨rows, roots⟩
  rw [hB] at smallB atomsB
  simp only at smallB atomsB
  have hP : T.packet = ⟨T.declarations, rows ++ moveRows rows.size T.nodes,
      roots ++ T.rules.map (place rows.size T.nodes.size)⟩ := by
    unfold Table.packet
    rw [hB]
  rw [hP] at h ⊢
  simp only at h ⊢
  unfold TableWire.input at h
  rw [graph_eq] at h
  cases hdl : Whole.declarations T.declarations.toList with
  | none => simp [hdl] at h
  | some dl =>
  simp only [hdl, Option.bind_eq_bind, Option.bind_some] at h
  generalize hA : ((rows ++ moveRows rows.size T.nodes).toList.filterMap atomOf).eraseDups = A at h
  rw [Array.toList_append, List.foldlM_append] at h
  cases ha : rows.toList.foldlM (step ⟨dl, A⟩) #[] with
  | none => simp only [ha, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at h
  | some a =>
  cases hts : (moveRows rows.size T.nodes).toList.foldlM (step ⟨dl, A⟩) a with
  | none => simp only [ha, hts, Option.bind_eq_bind, Option.bind_some, Option.bind_none, reduceCtorEq] at h
  | some ts =>
  simp only [ha, hts, Option.bind_eq_bind, Option.bind_some] at h
  have rowsDecoded := ruleRows_denote _ kindedB #[] rows #[] roots #[] a
    (by rw [hB]; simp) rfl
    (by simp only [Array.empty_append]; have : UInt64.size = 18446744073709551616 := rfl; omega) ha
  obtain ⟨eqs, heqs, hroots⟩ := rowsDecoded
  have aSize := (fold_extends _ _ _ ha).1
  have tsExt := fold_extends _ _ _ hts
  have split := hroots ts tsExt.2 (T.rules.map (place rows.size T.nodes.size)).toList
  rw [Array.toList_append] at h
  rw [split] at h
  cases hus : equations ts (T.rules.map (place rows.size T.nodes.size)).toList with
  | none => simp only [hus, Option.map_none, Option.bind_none, reduceCtorEq] at h
  | some us =>
  simp only [hus, Option.map_some, Option.bind_some, List.mapM_nil, Option.pure_def,
    Option.some.injEq] at h
  cases h
  refine ⟨eqs, us, by rw [builtinEquations_eq]; exact heqs, rfl, fun none_ => ?_, fun fits => ?_⟩
  · rw [none_] at hus
    simp [equations] at hus
    exact hus
  · simp only [Array.size_append] at fits
    have movedSize : (moveRows rows.size T.nodes).size = T.nodes.size := by simp [moveRows]
    rw [movedSize] at fits
    simp only [Array.length_toList, Nat.zero_add, Array.size_empty] at aSize
    have atomsEq : T.nodes.toList.filterMap atomOf =
        (rows ++ moveRows rows.size T.nodes).toList.filterMap atomOf := by
      rw [Array.toList_append, List.filterMap_append, atomsB, List.nil_append, moveRows_toList,
        atoms_mapIdx _ _ (atom_moved rows.size)]
    have moved := fold_moved (d := ⟨dl, A⟩) aSize T.nodes.toList 0 #[] rfl
      (by simp only [Array.length_toList, Nat.add_zero]; omega)
    rw [Array.append_empty] at moved
    have shape : T.nodes.toList.mapIdx (fun i => moveRow rows.size (i + 0)) =
        (moveRows rows.size T.nodes).toList := by
      rw [moveRows_toList]
      rfl
    rw [shape, hts] at moved
    cases hU : T.nodes.toList.foldlM (step ⟨dl, A⟩) #[] with
    | none => rw [hU] at moved; cases moved
    | some U =>
    rw [hU] at moved
    simp only [Option.map_some, Option.some.injEq] at moved
    have USize := (fold_extends _ _ _ hU).1
    simp only [Array.size_empty, Nat.zero_add, Array.length_toList] at USize
    unfold TableWire.input
    rw [graph_eq, hdl, atomsEq, hA]
    simp only [Option.bind_some, hU]
    rw [moved, Array.toList_map, equations_map (place_get aSize USize (by omega))] at hus
    simp [hus]

/-- Without user rules a decoded table holds exactly the builtin rules. -/
theorem input_builtinRules {T : Table} {d : Dictionary} {rs q} (h : T.input = some ⟨d, rs, q⟩)
    (noRules : T.rules = #[]) : T.builtinEquations d = some rs := by
  obtain ⟨bs, us, hbs, hrs, hus, _⟩ := input_rules h
  rw [hrs, hus noRules, List.append_nil]
  exact hbs

end Tamarin.Theory
