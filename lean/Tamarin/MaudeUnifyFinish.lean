import Tamarin.MaudeUnifyFinishProofs

/-!
# The completion of solved forms

`finish` checks a final state for cycles, instantiates its bindings, assigns
maximal sorts to its free slots and names them. Every statement holds for
all ranks `r` and all fuel `k`.
-/
namespace Tamarin.MaudeUnify
open Cancellation

variable {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]
variable (r : Ranks s)

/-- The image of original slot `i` in an answer. -/
def Answer.image (ans : Answer s) (i : Nat) : Dag s := ans.images.getD i (.var 0)

/-- The sort of output variable `j` in an answer. -/
def Answer.sortAt (ans : Answer s) (j : Nat) : SortId := ans.sorts.getD j .msg

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem image_mk (st : St s) (nOrig : Nat) (ub : Array (Option SortId)) {i : Nat} (hi : i < nOrig) :
    (mkAnswer st nOrig ub).image i = imageOf st i := by
  simp [Answer.image, mkAnswer, List.getD_eq_getElem?_getD, hi]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem sortAt_mk (st : St s) (nOrig : Nat) (ub : Array (Option SortId)) {j : Nat}
    (hj : j < (freeOf st).length) :
    (mkAnswer st nOrig ub).sortAt j = (ub.getD (freeOf st)[j] none).getD .msg := by
  simp [Answer.sortAt, mkAnswer, List.getD_eq_getElem?_getD, hj]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem sortAt_mk_ge (st : St s) (nOrig : Nat) (ub : Array (Option SortId)) {j : Nat}
    (hj : ¬ j < (freeOf st).length) : (mkAnswer st nOrig ub).sortAt j = .msg := by
  simp [Answer.sortAt, mkAnswer, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by simpa using hj)]
  rfl

/-- Soundness: whatever terms the output variables stand for, some model of
the final state agrees with the answer on the original slots. -/
theorem finish_sound (k nOrig : Nat) {st : St s} {ans : Answer s} (b : Bounded st)
    (hp : st.pending = []) (h : finish r k nOrig st = .ok (some ans)) (out : Nat → Term s) :
    ∃ ρ, Models st ρ ∧ ∀ i < nOrig, EquivB (ρ i) (Dag.eval out (ans.image i)) := by
  obtain ⟨order, ub, ho, _, rfl⟩ := finish_some r h
  have I := instantiate_spec r b ho
  generalize instantiate r st order = st' at I ⊢
  let τ : Nat → Term s := fun x => out ((namesOf st').getD x 0)
  refine ⟨Dag.through τ st'.value, ⟨(I.models _).mpr ?_, by simp [hp]⟩, fun i hi => ?_⟩
  · intro i d hd
    have e : Dag.eval (Dag.through τ st'.value) d = Dag.eval τ d := Dag.eval_congr d fun x hx => by
      have := (I.none_iff x).mpr ((I.vals _ _ hd).2 x hx).2
      simp only [Dag.through, this]
    rw [e]
    simp only [Dag.through, hd]
    exact .refl _
  · rw [image_mk _ _ _ hi]
    cases hv : st'.value i with
    | some d =>
      simp only [imageOf, Dag.through, hv]
      rw [eval_renameOut]
      exact .refl _
    | none =>
      simp only [imageOf, Dag.through, hv]
      rw [Dag.eval_var]
      exact .refl _

/-- The images respect the sorts of the original slots when the output
variables respect theirs. -/
theorem finish_sorted (k nOrig : Nat) {st : St s} {ans : Answer s} (b : Bounded st)
    (h : finish r k nOrig st = .ok (some ans)) (out : Nat → Term s)
    (hout : ∀ j, HasSort (out j) (ans.sortAt j)) :
    ∀ i < nOrig, ∀ srt, st.sortOf i = some srt → HasSort (Dag.eval out (ans.image i)) srt := by
  obtain ⟨order, ub, ho, hub, rfl⟩ := finish_some r h
  have I := instantiate_spec r b ho
  generalize instantiate r st order = st' at I hub hout ⊢
  intro i hi srt hs
  let n := st.vals.size
  let P : Nat → Prop := fun x => x < n ∧ st'.value x = none
  let τ : Nat → Term s := fun x => out ((namesOf st').getD x 0)
  have sat : FinishProofs.SatP P τ ub := by
    intro x c px hx
    obtain ⟨j, hj, hfj, e⟩ := names_spec (mem_freeOf.mpr ⟨I.size ▸ px.1, px.2⟩)
    have := hout j
    rw [sortAt_mk _ _ _ hj, hfj, hx] at this
    simp only [τ, e]
    exact this
  have fs := FinishProofs.foldBind_sound P n
    (fun ub i => match st'.value i, st'.sortOf i with
      | some d, some srt => bounds ub d srt
      | _, _ => some ub)
    (fun ν i => ∀ d srt, st'.value i = some d → st'.sortOf i = some srt → HasSort (Dag.eval ν d) srt)
    (List.range nOrig)
    (fun i _ ub ub' hn h => by
      cases hv : st'.value i with
      | none =>
        simp only [hv] at h
        cases h
        exact ⟨hn, fun ν sat => ⟨sat, fun d _ hd => by cases hd⟩⟩
      | some d =>
        cases hso : st'.sortOf i with
        | none =>
          simp only [hv, hso] at h
          cases h
          exact ⟨hn, fun ν sat => ⟨sat, fun _ _ _ hs' => by cases hs'⟩⟩
        | some srt =>
          simp only [hv, hso] at h
          have vd := I.vals _ _ hv
          have bs := FinishProofs.bounds_sound P n d ub ub' srt vd.1 hn
            (fun x hx => ⟨⟨(vd.2 x hx).1, (I.none_iff x).mpr (vd.2 x hx).2⟩, (vd.2 x hx).1⟩) h
          refine ⟨bs.1, fun ν sat => ⟨(bs.2 ν sat).1, fun d' srt' hd' hs' => ?_⟩⟩
          cases hd'; cases hs'
          exact (bs.2 ν sat).2)
    (ub0Of st' nOrig) ub (by rw [ub0_size, I.size]) hub
  obtain ⟨sat0, all⟩ := fs.2 τ sat
  rw [image_mk _ _ _ hi]
  have hs' : st'.sortOf i = some srt := by rw [I.sortOf]; exact hs
  cases hv : st'.value i with
  | some d =>
    simp only [imageOf, hv]
    rw [eval_renameOut]
    exact all i (List.mem_range.mpr hi) d srt hv hs'
  | none =>
    simp only [imageOf, hv]
    rw [Dag.eval_var]
    have hin : i < n := by have := St.lt_of_sortOf_some hs; rw [b.sizes] at this; exact this
    refine sat0 i srt ⟨hin, hv⟩ ?_
    rw [ub0_getD, ite_eq_left ⟨I.size ▸ hin, hi, by simp [hv]⟩]
    exact hs'

/-- Completeness: a model of the final state that respects the sorts of the
original slots is an instance of the answer, through output values that
respect the sorts of the output variables; the state is not dropped. -/
theorem finish_complete (k nOrig : Nat) {st : St s} (b : Bounded st)
    (hn : nOrig ≤ st.vals.size) (hs : ∀ i < nOrig, st.sortOf i ≠ none) {ρ : Nat → Term s} (m : Models st ρ)
    (sorted : ∀ i < nOrig, ∀ srt, st.sortOf i = some srt → HasSort (ρ i) srt) :
    match finish r k nOrig st with
    | .ok (some ans) => ∃ δ : Nat → Term s, (∀ j, HasSort (δ j) (ans.sortAt j)) ∧
        ∀ i < nOrig, EquivB (ρ i) (Dag.eval δ (ans.image i))
    | .ok none => False
    | .fail => False
    | .gaveUp => True := by
  rw [finish_eq]
  cases he : exploreAll st k (List.range nOrig ++ (List.range st.vals.size).drop nOrig) with
  | gaveUp => trivial
  | cycle c =>
    dsimp only
    simp only [isCycle_false b m.binds c, Bool.false_eq_true, ↓reduceIte]
  | done status order =>
    dsimp only
    cases ho : isOrder st order with
    | false => simp only [Bool.not_false, ↓reduceIte]
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have I := instantiate_spec r b ho
      generalize instantiate r st order = st' at I ⊢
      have m' : Binds st' ρ := (I.models ρ).mp m.binds
      let n := st.vals.size
      let S : Nat → List Nat := fun i => match st'.value i with
        | some d => d.vars
        | none => []
      have g0 : FinishProofs.Good ρ n (ub0Of st' nOrig) := by
        refine ⟨by rw [ub0_size, I.size], fun x c _ hx => ?_⟩
        rw [ub0_getD] at hx
        split at hx
        · next hc => exact sorted x hc.2.1 c (by rw [← I.sortOf]; exact hx)
        · cases hx
      have fc := FinishProofs.foldBind_complete (FinishProofs.Good ρ n)
        (fun ub i => match st'.value i, st'.sortOf i with
          | some d, some srt => bounds ub d srt
          | _, _ => some ub)
        S (List.range nOrig)
        (fun i hi ub g => by
          cases hv : st'.value i with
          | none => exact ⟨ub, by simp only, g, fun _ h => h, by simp [S, hv]⟩
          | some d =>
            have hi : i < nOrig := List.mem_range.mp hi
            obtain ⟨srt, hso⟩ := Option.ne_none_iff_exists'.mp (hs i hi)
            have hso' : st'.sortOf i = some srt := by rw [I.sortOf]; exact hso
            have vd := I.vals _ _ hv
            have hd := FinishProofs.hasSort_equiv (m' i d hv) (sorted i hi srt hso)
            obtain ⟨ub', hb, g', mono, vs⟩ := FinishProofs.bounds_complete ρ n d ub srt vd.1
              (fun x hx => (vd.2 x hx).1) g hd
            exact ⟨ub', by simp only [hso']; exact hb, g', mono, by simp only [S, hv]; exact vs⟩)
        (ub0Of st' nOrig) g0
      obtain ⟨ub, hub, g, mono, vs⟩ := fc
      have hub' : ubFold st' nOrig = some ub := hub
      rw [hub']
      dsimp only
      let δ : Nat → Term s := fun j =>
        if h : j < (freeOf st').length then
          (if (ub.getD (freeOf st')[j] none).isSome then ρ (freeOf st')[j] else .var ⟨0, .msg⟩)
        else .var ⟨0, .msg⟩
      have named : ∀ x, x ∈ freeOf st' → (ub.getD x none).isSome → δ ((namesOf st').getD x 0) = ρ x := by
        intro x hx hsome
        obtain ⟨j, hj, hfj, e⟩ := names_spec hx
        simp only [δ, e, hj, ↓reduceDIte, hfj, hsome, ↓reduceIte]
      refine ⟨δ, fun j => ?_, fun i hi => ?_⟩
      · by_cases hj : j < (freeOf st').length
        · rw [sortAt_mk _ _ _ hj]
          simp only [δ, hj, ↓reduceDIte]
          cases hu : ub.getD (freeOf st')[j] none with
          | none => exact .var _
          | some c => simp only [Option.isSome_some, ↓reduceIte, Option.getD_some]; exact g.2 _ c trivial hu
        · rw [sortAt_mk_ge _ _ _ hj]
          simp only [δ, hj, ↓reduceDIte]
          exact .var _
      · rw [image_mk _ _ _ hi]
        cases hv : st'.value i with
        | some d =>
          simp only [imageOf, hv]
          rw [eval_renameOut]
          have vd := I.vals _ _ hv
          have e : Dag.eval ρ d = Dag.eval (fun x => δ ((namesOf st').getD x 0)) d :=
            Dag.eval_congr d fun x hx => (named x
              (mem_freeOf.mpr ⟨I.size ▸ (vd.2 x hx).1, (I.none_iff x).mpr (vd.2 x hx).2⟩)
              (vs i (List.mem_range.mpr hi) x (by simp only [S, hv]; exact hx))).symm
          rw [← e]
          exact m' i d hv
        | none =>
          simp only [imageOf, hv]
          rw [Dag.eval_var]
          have hin : i < n := Nat.lt_of_lt_of_le hi hn
          rw [named i (mem_freeOf.mpr ⟨I.size ▸ hin, hv⟩) ?_]
          · exact .refl _
          · apply mono i
            rw [ub0_getD, ite_eq_left ⟨I.size ▸ hin, hi, by simp [hv]⟩, I.sortOf]
            obtain ⟨srt, hso⟩ := Option.ne_none_iff_exists'.mp (hs i hi)
            rw [hso]; rfl

/-- The images are well formed and mention only output variables numbered
below the number of sorts. -/
theorem finish_vars (k nOrig : Nat) {st : St s} {ans : Answer s} (b : Bounded st)
    (hn : nOrig ≤ st.vals.size) (h : finish r k nOrig st = .ok (some ans)) :
    ans.images.length = nOrig ∧ (∀ i < nOrig, ∀ j ∈ (ans.image i).vars, j < ans.sorts.length) ∧
      ∀ i < nOrig, (ans.image i).Wf := by
  obtain ⟨order, ub, ho, _, rfl⟩ := finish_some r h
  have I := instantiate_spec r b ho
  generalize instantiate r st order = st' at I ⊢
  refine ⟨by simp [mkAnswer], fun i hi j hj => ?_, fun i hi => ?_⟩
  rotate_left
  · rw [image_mk _ _ _ hi]
    cases hv : st'.value i with
    | some d => simp only [imageOf, hv]; exact wf_renameOut _ d (I.vals _ _ hv).1
    | none => simp only [imageOf, hv, Dag.Wf]
  rw [image_mk _ _ _ hi] at hj
  have len : (mkAnswer st' nOrig ub).sorts.length = (freeOf st').length := by simp [mkAnswer]
  rw [len]
  cases hv : st'.value i with
  | some d =>
    simp only [imageOf, hv] at hj
    obtain ⟨x, hx, rfl⟩ := mem_vars_renameOut _ d hj
    have ⟨xn, xv⟩ := (I.vals _ _ hv).2 x hx
    obtain ⟨k, hk, _, e⟩ := names_spec (mem_freeOf.mpr ⟨I.size ▸ xn, (I.none_iff x).mpr xv⟩)
    rw [e]; exact hk
  | none =>
    simp only [imageOf, hv, Dag.vars, List.mem_singleton] at hj
    subst hj
    obtain ⟨k, hk, _, e⟩ := names_spec (mem_freeOf.mpr ⟨I.size ▸ Nat.lt_of_lt_of_le hi hn, hv⟩)
    rw [e]; exact hk

end Tamarin.MaudeUnify
