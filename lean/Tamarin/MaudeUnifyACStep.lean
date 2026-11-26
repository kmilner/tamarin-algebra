import Tamarin.MaudeUnifyACStepProofs

/-!
# The AC subproblem

`acStates` collects the AC problems of one symbol into Diophantine rows,
unsolves earlier bindings into the symbol, computes Maude's basis and
selections, and builds one state per selection (`witnesses`, `assign`,
`buildFrom`). Every statement holds for all ranks `r` and all fuel `k`.
-/
namespace Tamarin.MaudeUnify
open Cancellation


variable {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]
variable (r : Ranks s)

/-- Well-formedness: every state of the subproblem is bounded, only adds
slots, and keeps the sort of every slot. -/
theorem acStates_wf (k : Nat) {st : St s} {f : s.ACSym} {unifs : List (Dag s × Dag s)} (b : Bounded st)
    (hu : ∀ p ∈ unifs, p.1.Fit st.vals.size ∧ p.2.Fit st.vals.size) {L : List (St s)}
    (h : acStates r k st f unifs = .ok L) :
    ∀ st' ∈ L, Bounded st' ∧ Grows st st' ∧ ∀ i, st'.sortOf i = st.sortOf i := by
  unfold acStates at h
  generalize hR : List.foldl _ ([], []) unifs = R at h
  obtain ⟨subs0, rows0⟩ := R
  dsimp only at h
  split at h
  · cases h
    intro st' hst'
    rw [List.mem_singleton.mp hst']
    exact ⟨b, ⟨Nat.le_refl _, fun _ _ => rfl⟩, fun _ => rfl⟩
  · generalize hU : unsolve f st.vals.size st subs0 rows0 = U at h
    obtain ⟨st1, subs, rows⟩ := U
    dsimp only at h
    split at h
    · cases h
    · next sols hb =>
      obtain ⟨b1, sz1, so1, -, -, hsubs, hrows, -⟩ := ac_front f b hu hR hU
      intro st' hst'
      obtain ⟨T, hT, bs, hg, hy⟩ := concatMap_ok_mem _ _ L h st' hst'
      generalize hW : witnesses subs (T.map (·.vec.toList)) (T.map (·.vec.toList)) 0 st1 = W at hg
      obtain ⟨st2, ws, reused⟩ := W
      dsimp only at hg
      obtain ⟨st'', hbf, rfl⟩ := Res.map_eq_ok hg
      rw [List.mem_singleton.mp hy]
      obtain ⟨-, -, cov⟩ := Select.all_sound _ _ hT
      have hsol : ∀ E ∈ T, ACBasis.Hilbert.Sol (colsOf subs.length rows) E.vec := by
        intro E hE
        have hv : E.vec ∈ basisList _ sols := (Select.all_sound _ _ hT).1.subset (List.mem_map_of_mem hE)
        exact ((Dioph.basis_spec _ _ _ hb (ac_pos st1 f subs)).1 E.vec (mem_basisList.mp hv).1).1
      rw [← sz1] at hsubs
      obtain ⟨b', g', so', -⟩ := sel_sound r k f b1 hsubs hrows cov hsol hW hbf
      exact ⟨b', ⟨by omega, fun i _ => (so' i).trans (so1 i)⟩, fun i => (so' i).trans (so1 i)⟩

/-- Soundness: a model of any state of the subproblem models the start and
solves every problem of the symbol. -/
theorem acStates_sound (k : Nat) {st : St s} {f : s.ACSym} {unifs : List (Dag s × Dag s)} (b : Bounded st)
    (hu : ∀ p ∈ unifs, p.1.Fit st.vals.size ∧ p.2.Fit st.vals.size) {L : List (St s)}
    (h : acStates r k st f unifs = .ok L) {st' : St s} (hm : st' ∈ L) {ρ : Nat → Term s}
    (m : Models st' ρ) :
    Models st ρ ∧ ∀ p ∈ unifs, EquivB (Dag.eval ρ p.1) (Dag.eval ρ p.2) := by
  have hw : ∀ p ∈ unifs, p.1.Wf ∧ p.2.Wf := fun p hp => ⟨(hu p hp).1.1, (hu p hp).2.1⟩
  unfold acStates at h
  generalize hR : List.foldl _ ([], []) unifs = R at h
  obtain ⟨subs0, rows0⟩ := R
  have hR' : unifs.foldl (fun (acc : List (Dag s) × List (List Int)) (p : Dag s × Dag s) =>
      addUnif st f acc.1 acc.2 p.1 p.2) ([], []) = (subs0, rows0) := hR
  dsimp only at h
  split at h
  · next hemp =>
    cases h
    rw [List.mem_singleton.mp hm] at m
    refine ⟨m, fun p hp => ?_⟩
    obtain ⟨-, -, iffC⟩ := collect_spec f st m.chains unifs [] [] hw (fun _ h => by cases h)
    rw [hR'] at iffC
    rw [equiv_iff_sameCnt f]
    intro a
    have : RowsOk f ρ subs0 rows0 a := by
      intro row hrow
      rw [List.isEmpty_iff] at hemp
      rw [hemp] at hrow
      cases hrow
    exact ((iffC a).mp this).2 p hp
  · generalize hU : unsolve f st.vals.size st subs0 rows0 = U at h
    obtain ⟨st1, subs, rows⟩ := U
    dsimp only at h
    split at h
    · cases h
    · next sols hb =>
      obtain ⟨b1, sz1, -, pd1, vars1, hsubs, hrows, hrows0⟩ := ac_front f b hu hR hU
      obtain ⟨T, hT, bs, hg, hy⟩ := concatMap_ok_mem _ _ L h st' hm
      generalize hW : witnesses subs (T.map (·.vec.toList)) (T.map (·.vec.toList)) 0 st1 = W at hg
      obtain ⟨st2, ws, reused⟩ := W
      dsimp only at hg
      obtain ⟨st'', hbf, rfl⟩ := Res.map_eq_ok hg
      rw [List.mem_singleton.mp hy] at m
      obtain ⟨-, -, cov⟩ := Select.all_sound _ _ hT
      have hsol : ∀ E ∈ T, ACBasis.Hilbert.Sol (colsOf subs.length rows) E.vec := by
        intro E hE
        have hv : E.vec ∈ basisList _ sols := (Select.all_sound _ _ hT).1.subset (List.mem_map_of_mem hE)
        exact ((Dioph.basis_spec _ _ _ hb (ac_pos st1 f subs)).1 E.vec (mem_basisList.mp hv).1).1
      rw [← sz1] at hsubs
      obtain ⟨-, -, -, snd⟩ := sel_sound r k f b1 hsubs hrows cov hsol hW hbf
      obtain ⟨m1, rowsOk⟩ := snd ρ m
      have c : Chains st ρ := fun x y hxy => by
        have := m1.binds x _ (vars1 x y hxy)
        rwa [Dag.eval_var] at this
      have hvw : ∀ i d, st.value i = some d → d.Wf := fun i d h => (b.vals i d h).1
      have U := unsolve_spec f (ρ := ρ) st.vals.size st subs0 rows0 (Nat.le_refl _) hrows0 hvw c
      rw [hU] at U
      obtain ⟨-, -, -, -, -, -, -, iffU⟩ := U
      obtain ⟨rows0Ok, bindsSt⟩ := iffU.mp ⟨rowsOk, m1.binds⟩
      obtain ⟨-, -, iffC⟩ := collect_spec f st c unifs [] [] hw (fun _ h => by cases h)
      rw [hR'] at iffC
      refine ⟨⟨bindsSt, fun p hp => m1.pend p (by rw [pd1]; exact hp)⟩, fun p hp => ?_⟩
      rw [equiv_iff_sameCnt f]
      intro a
      exact ((iffC a).mp (rows0Ok a)).2 p hp

/-- Completeness: a model of the start that gives sorted slots their sorts and
solves every problem of the symbol extends to a model of some state of the
subproblem. -/
theorem acStates_complete (k : Nat) {st : St s} {f : s.ACSym} {unifs : List (Dag s × Dag s)}
    (b : Bounded st) (hu : ∀ p ∈ unifs, p.1.Fit st.vals.size ∧ p.2.Fit st.vals.size)
    {ρ : Nat → Term s} (m : Models st ρ) (so : Sorted st ρ)
    (e : ∀ p ∈ unifs, EquivB (Dag.eval ρ p.1) (Dag.eval ρ p.2)) :
    match acStates r k st f unifs with
    | .ok L => ∃ st' ∈ L, ∃ ρ', Agree st.vals.size ρ ρ' ∧ Models st' ρ'
    | .fail => False
    | .gaveUp => True := by
  have hw : ∀ p ∈ unifs, p.1.Wf ∧ p.2.Wf := fun p hp => ⟨(hu p hp).1.1, (hu p hp).2.1⟩
  have c := m.chains
  rcases hA : acStates r k st f unifs with L | _ | _
  · unfold acStates at hA
    generalize hR : List.foldl _ ([], []) unifs = R at hA
    obtain ⟨subs0, rows0⟩ := R
    have hR' : unifs.foldl (fun (acc : List (Dag s) × List (List Int)) (p : Dag s × Dag s) =>
        addUnif st f acc.1 acc.2 p.1 p.2) ([], []) = (subs0, rows0) := hR
    obtain ⟨-, -, iffC⟩ := collect_spec f st c unifs [] [] hw (fun _ h => by cases h)
    rw [hR'] at iffC
    have rows0Ok : ∀ a, RowsOk f ρ subs0 rows0 a := fun a =>
      (iffC a).mpr ⟨fun _ h => (by cases h), fun p hp => (equiv_iff_sameCnt f ρ p.1 p.2).mp (e p hp) a⟩
    dsimp only at hA
    split at hA
    · cases hA
      exact ⟨st, List.mem_singleton_self _, ρ, fun _ _ => rfl, m⟩
    · generalize hU : unsolve f st.vals.size st subs0 rows0 = U at hA
      obtain ⟨st1, subs, rows⟩ := U
      dsimp only at hA
      split at hA
      · cases hA
      · next sols hb =>
        obtain ⟨b1, sz1, so1, pd1, -, hsubs, hrows, hrows0⟩ := ac_front f b hu hR hU
        have hvw : ∀ i d, st.value i = some d → d.Wf := fun i d h => (b.vals i d h).1
        have U := unsolve_spec f (ρ := ρ) st.vals.size st subs0 rows0 (Nat.le_refl _) hrows0 hvw c
        rw [hU] at U
        obtain ⟨-, -, -, -, -, -, -, iffU⟩ := U
        obtain ⟨rowsOk, binds1⟩ : (∀ a, RowsOk f ρ subs rows a) ∧ Binds st1 ρ := iffU.mpr ⟨rows0Ok, m.binds⟩
        have m1 : Models st1 ρ := ⟨binds1, fun p hp => m.pend p (by rw [← pd1]; exact hp)⟩
        have so' : Sorted st1 ρ := fun i srt h => so i srt (by rw [← so1 i]; exact h)
        have wf1 : ∀ i d, st1.value i = some d → d.Wf := fun i d h => (b1.vals i d h).1
        have cls := fun (i : Fin subs.length) =>
          classify_spec f binds1 so' wf1 (hsubs _ (List.getElem_mem i.isLt)).1
        obtain ⟨T, hT, wt, hwt, hfac⟩ := factor f (fun i : Fin subs.length => Dag.eval ρ subs[i]) rows _
          ((subs.map (classify st1 f)).map (·.2)) hb (ac_pos st1 f subs)
          (rowsHold_of_ok f ρ subs rows hrows rowsOk)
          (fun i u hu' => (cls i).1 u (by rw [upper_at st1 f subs i] at hu'; exact hu'))
          (fun i j x y hx hy ne a hai haj => by
            rw [stable_at] at hx hy
            obtain ⟨v, hv, -, fv⟩ := (cls i).2 x hx
            obtain ⟨v', hv', -, fv'⟩ := (cls j).2 y hy
            have hai' : a ∈ flatten f (Dag.eval ρ subs[(i : Nat)]) := hai
            have haj' : a ∈ flatten f (Dag.eval ρ subs[(j : Nat)]) := haj
            rw [fv] at hai'
            rw [fv'] at haj'
            have := (List.mem_singleton.mp hai').symm.trans (List.mem_singleton.mp haj')
            exact heads_ne hv hv' ne (Quotient.exact this))
        obtain ⟨-, -, cov⟩ := Select.all_sound _ _ hT
        apply concatMap_promise hA hT
        generalize hW : witnesses subs (T.map (·.vec.toList)) (T.map (·.vec.toList)) 0 st1 = W
        rw [← sz1]
        rw [← sz1] at hsubs
        exact promise_map (sel_complete r k f b1 hsubs cov m1 hwt hfac hW)
  · exfalso
    unfold acStates at hA
    generalize List.foldl _ ([], []) unifs = R at hA
    obtain ⟨subs0, rows0⟩ := R
    dsimp only at hA
    split at hA
    · cases hA
    · generalize unsolve f st.vals.size st subs0 rows0 = U at hA
      obtain ⟨st1, subs, rows⟩ := U
      dsimp only at hA
      split at hA
      · cases hA
      · exact concatMap_ne_fail _ _ hA
  · trivial

end Tamarin.MaudeUnify
