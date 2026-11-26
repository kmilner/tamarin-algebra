import Tamarin.MaudeUnifyACStep
import Tamarin.MaudeUnifyFinish

/-!
# The driver: the pending stack, the C subproblem, and the whole unification
-/
namespace Tamarin.MaudeUnify
open Cancellation


variable {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

/-! ### Results -/

namespace Res
variable {α β : Type}

theorem concatMap_ne_fail (f : α → Res (List β)) (l : List α) : concatMap f l ≠ .fail := by
  induction l with
  | nil => simp [concatMap]
  | cons a as ih =>
    simp only [concatMap]
    split
    · simp
    · exact ih
    · cases h : concatMap f as <;> simp_all [map]

theorem mem_concatMap {f : α → Res (List β)} {l : List α} {L : List β} (h : concatMap f l = .ok L)
    {x : β} (hx : x ∈ L) : ∃ a ∈ l, ∃ L', f a = .ok L' ∧ x ∈ L' := by
  induction l generalizing L with
  | nil => simp only [concatMap, ok.injEq] at h; subst h; cases hx
  | cons a as ih =>
    simp only [concatMap] at h
    split at h
    · cases h
    · obtain ⟨b, hb, L', e, hx'⟩ := ih h hx
      exact ⟨b, List.mem_cons_of_mem _ hb, L', e, hx'⟩
    · next bs e =>
      cases h' : concatMap f as with
      | ok rest =>
        rw [h'] at h
        simp only [map, ok.injEq] at h
        subst h
        rcases List.mem_append.mp hx with hx | hx
        · exact ⟨a, List.mem_cons_self, bs, e, hx⟩
        · obtain ⟨b, hb, L', e', hx'⟩ := ih h' hx
          exact ⟨b, List.mem_cons_of_mem _ hb, L', e', hx'⟩
      | fail => rw [h'] at h; cases h
      | gaveUp => rw [h'] at h; cases h

/-- What completeness needs of a concatenation: if one of its computations
succeeds with an element, the whole gives up or contains it. -/
theorem concatMap_reaches {f : α → Res (List β)} {l : List α} {a : α} (ha : a ∈ l) {L' : List β}
    (e : f a = .ok L') {x : β} (hx : x ∈ L') :
    concatMap f l = .gaveUp ∨ ∃ L, concatMap f l = .ok L ∧ x ∈ L := by
  induction l with
  | nil => cases ha
  | cons b bs ih =>
    simp only [concatMap]
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [e]
      cases h : concatMap f bs with
      | ok rest => exact .inr ⟨_, rfl, List.mem_append_left _ hx⟩
      | fail => exact absurd h (concatMap_ne_fail f bs)
      | gaveUp => exact .inl rfl
    · split
      · exact .inl rfl
      · exact ih ha
      · rcases ih ha with g | ⟨L, eq, mem⟩
        · rw [g]; exact .inl rfl
        · rw [eq]; exact .inr ⟨_, rfl, List.mem_append_right _ mem⟩

/-- A computation of the concatenation that gives up makes it give up. -/
theorem concatMap_gaveUp {f : α → Res (List β)} {l : List α} {a : α} (ha : a ∈ l) (e : f a = .gaveUp) :
    concatMap f l = .gaveUp := by
  induction l with
  | nil => cases ha
  | cons b bs ih =>
    simp only [concatMap]
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [e]
    · split
      · rfl
      · exact ih ha
      · rw [ih ha]; rfl

end Res

/-! ### Small facts -/

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem fit_comm {n : Nat} {f : s.CSym} {a b : Dag s} (h : (Dag.comm f a b).Fit n) : a.Fit n ∧ b.Fit n := by
  obtain ⟨w, below⟩ := h
  simp only [Dag.Wf] at w
  obtain ⟨wa, wb⟩ := w
  exact ⟨⟨wa, fun j hj => below j (by simp [Dag.vars, hj])⟩, ⟨wb, fun j hj => below j (by simp [Dag.vars, hj])⟩⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem Grows.trans {st1 st2 st3 : St s} (a : Grows st1 st2) (b : Grows st2 st3) : Grows st1 st3 :=
  ⟨Nat.le_trans a.1 b.1, fun i hi => (b.2 i (Nat.lt_of_lt_of_le hi a.1)).trans (a.2 i hi)⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem Grows.refl (st : St s) : Grows st st := ⟨Nat.le_refl _, fun _ _ => rfl⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem eval_agree {n : Nat} {ρ ρ' : Nat → Term s} (a : Agree n ρ ρ') {d : Dag s} (h : d.Below n) :
    Dag.eval ρ' d = Dag.eval ρ d :=
  Dag.eval_congr d fun i hi => a i (h i hi)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem Sorted.extend {st st' : St s} {ρ ρ' : Nat → Term s} (so : Sorted st ρ) (a : Agree st.vals.size ρ ρ')
    (sorts : ∀ i, st'.sortOf i = st.sortOf i) (b : Bounded st) : Sorted st' ρ' := by
  intro i srt h
  rw [sorts] at h
  have lt : i < st.vals.size := by
    apply Classical.byContradiction
    intro c
    unfold St.sortOf at h
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [b.sizes]; omega)] at h
    cases h
  rw [a i lt]
  exact so i srt h

omit [DecidableEq s.FreeSym] [DecidableEq s.Atom] in
theorem Theory.beq_eq {a b : Theory s} (h : a.beq b = true) : a = b := by
  cases a <;> cases b <;> simp_all [Theory.beq]

omit [DecidableEq s.FreeSym] [DecidableEq s.Atom] in
theorem Theory.beq_self (a : Theory s) : a.beq a = true := by
  cases a <;> simp [Theory.beq]

/-! ### Splitting off the problems of one theory -/

/-- The problems of a theory and the state without them. -/
def take (st : St s) (th : Theory s) : List (Dag s × Dag s) × St s :=
  ((st.pending.filter fun p => p.th.beq th).map fun p => (p.lhs, p.rhs),
    { st with pending := st.pending.filter fun p => !p.th.beq th })

omit [DecidableEq s.FreeSym] [DecidableEq s.Atom] in
theorem take_models (st : St s) (th : Theory s) (ρ : Nat → Term s) :
    Models st ρ ↔ Models (take st th).2 ρ ∧ ∀ p ∈ (take st th).1, EquivB (Dag.eval ρ p.1) (Dag.eval ρ p.2) := by
  constructor
  · intro m
    refine ⟨⟨m.binds, fun p hp => m.pend p (List.mem_filter.mp hp).1⟩, fun q hq => ?_⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact m.pend p (List.mem_filter.mp hp).1
  · rintro ⟨m, e⟩
    refine ⟨m.binds, fun p hp => ?_⟩
    by_cases h : p.th.beq th
    · exact e (p.lhs, p.rhs) (List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, h⟩, rfl⟩)
    · exact m.pend p (List.mem_filter.mpr ⟨hp, by simp [h]⟩)

omit [DecidableEq s.FreeSym] [DecidableEq s.Atom] in
theorem take_bounded {st : St s} (b : Bounded st) (th : Theory s) :
    Bounded (take st th).2 ∧ (take st th).2.vals = st.vals ∧ (take st th).2.sorts = st.sorts ∧
      ∀ p ∈ (take st th).1, p.1.Fit st.vals.size ∧ p.2.Fit st.vals.size := by
  refine ⟨⟨b.sizes, b.vals, fun p hp => b.pend p (List.mem_filter.mp hp).1⟩, rfl, rfl, fun q hq => ?_⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  exact ⟨(b.pend p (List.mem_filter.mp hp).1).1, (b.pend p (List.mem_filter.mp hp).1).2.1⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.Atom] in
theorem take_comm_shape {st : St s} (b : Bounded st) (f : s.CSym) :
    ∀ p ∈ (take st (.comm f)).1, (∃ a c, p.1 = .comm f a c) ∧ ∃ a c, p.2 = .comm f a c := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  have sh := (b.pend p (List.mem_filter.mp hp).1).2.2
  have e := Theory.beq_eq (List.mem_filter.mp hp).2
  unfold Pend.Shaped at sh
  rw [e] at sh
  exact sh

/-! ### The C subproblem -/

variable (r : Ranks s)

/-- Two steps of `csf` in a row keep the invariants. -/
theorem csf2_wf (k : Nat) {st st1 st2 : St s} {a b c d : Dag s} (bd : Bounded st)
    (ha : a.Fit st.vals.size) (hb : b.Fit st.vals.size) (hc : c.Fit st.vals.size) (hd : d.Fit st.vals.size)
    (h1 : csf r k st a b = .ok st1) (h2 : csf r k st1 c d = .ok st2) :
    Bounded st2 ∧ Grows st st2 ∧ ∀ i, st2.sortOf i = st.sortOf i := by
  obtain ⟨b1, g1⟩ := csf_wf r k bd ha hb h1
  obtain ⟨b2, g2⟩ := csf_wf r k b1 (hc.mono g1.1) (hd.mono g1.1) h2
  exact ⟨b2, g1.trans g2, fun i => (csf_sorts r k h2 i).trans (csf_sorts r k h1 i)⟩

theorem commStates_wf (k : Nat) : ∀ (unifs : List (Dag s × Dag s)) (st : St s), Bounded st →
    (∀ p ∈ unifs, p.1.Fit st.vals.size ∧ p.2.Fit st.vals.size) → ∀ {L : List (St s)},
    commStates r k st unifs = .ok L → ∀ st' ∈ L, Bounded st' ∧ Grows st st' ∧ ∀ i, st'.sortOf i = st.sortOf i
  | [], st, bd, _, L, h => by
    simp only [commStates, Res.ok.injEq] at h; subst h
    intro st' hm; simp at hm; subst hm; exact ⟨bd, Grows.refl _, fun _ => rfl⟩
  | (l, rt) :: rest, st, bd, hu, L, h => by
    intro st' hm
    simp only [commStates] at h
    split at h
    · next f l0 l1 g r0 r1 =>
      split at h
      · have hl := fit_comm (hu _ List.mem_cons_self).1
        have hr := fit_comm (hu _ List.mem_cons_self).2
        obtain ⟨o, ho, L', e, hx⟩ := Res.mem_concatMap h hm
        have restFit : ∀ {n}, st.vals.size ≤ n → ∀ p ∈ rest, p.1.Fit n ∧ p.2.Fit n := fun le p hp =>
          ⟨(hu p (List.mem_cons_of_mem _ hp)).1.mono le, (hu p (List.mem_cons_of_mem _ hp)).2.mono le⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl
        · cases h1 : csf r k st l0 r0 with
          | ok st1 =>
            rw [h1] at e
            simp only [Res.bind] at e
            cases h2 : csf r k st1 l1 r1 with
            | ok st2 =>
              rw [h2] at e
              obtain ⟨b2, g2, s2⟩ := csf2_wf r k bd hl.1 hr.1 hl.2 hr.2 h1 h2
              obtain ⟨b', g', s'⟩ := commStates_wf k rest st2 b2 (restFit g2.1) e st' hx
              exact ⟨b', g2.trans g', fun i => (s' i).trans (s2 i)⟩
            | fail => rw [h2] at e; cases e
            | gaveUp => rw [h2] at e; cases e
          | fail => rw [h1] at e; cases e
          | gaveUp => rw [h1] at e; cases e
        · cases h1 : csf r k st l0 r1 with
          | ok st1 =>
            rw [h1] at e
            simp only [Res.bind] at e
            cases h2 : csf r k st1 l1 r0 with
            | ok st2 =>
              rw [h2] at e
              obtain ⟨b2, g2, s2⟩ := csf2_wf r k bd hl.1 hr.2 hl.2 hr.1 h1 h2
              obtain ⟨b', g', s'⟩ := commStates_wf k rest st2 b2 (restFit g2.1) e st' hx
              exact ⟨b', g2.trans g', fun i => (s' i).trans (s2 i)⟩
            | fail => rw [h2] at e; cases e
            | gaveUp => rw [h2] at e; cases e
          | fail => rw [h1] at e; cases e
          | gaveUp => rw [h1] at e; cases e
      · cases h
    · cases h

theorem commStates_sound (k : Nat) : ∀ (unifs : List (Dag s × Dag s)) (st : St s), Bounded st →
    (∀ p ∈ unifs, p.1.Fit st.vals.size ∧ p.2.Fit st.vals.size) → ∀ {L : List (St s)},
    commStates r k st unifs = .ok L → ∀ st' ∈ L, ∀ ρ, Models st' ρ →
      Models st ρ ∧ ∀ p ∈ unifs, EquivB (Dag.eval ρ p.1) (Dag.eval ρ p.2)
  | [], st, bd, _, L, h => by
    simp only [commStates, Res.ok.injEq] at h; subst h
    intro st' hm ρ m; simp at hm; subst hm; exact ⟨m, fun p hp => by cases hp⟩
  | (l, rt) :: rest, st, bd, hu, L, h => by
    intro st' hm ρ m
    simp only [commStates] at h
    split at h
    · next f l0 l1 g r0 r1 =>
      split at h
      · next fg =>
        subst fg
        have hl := fit_comm (hu _ List.mem_cons_self).1
        have hr := fit_comm (hu _ List.mem_cons_self).2
        obtain ⟨o, ho, L', e, hx⟩ := Res.mem_concatMap h hm
        have restFit : ∀ {n}, st.vals.size ≤ n → ∀ p ∈ rest, p.1.Fit n ∧ p.2.Fit n := fun le p hp =>
          ⟨(hu p (List.mem_cons_of_mem _ hp)).1.mono le, (hu p (List.mem_cons_of_mem _ hp)).2.mono le⟩
        -- the two orientations, as one statement
        have step : ∀ a b c d : Dag s, a.Fit st.vals.size → b.Fit st.vals.size → c.Fit st.vals.size →
            d.Fit st.vals.size → ((csf r k st a b).bind fun st => csf r k st c d).bind
              (fun st => commStates r k st rest) = .ok L' →
            Models st ρ ∧ EquivB (Dag.eval ρ a) (Dag.eval ρ b) ∧ EquivB (Dag.eval ρ c) (Dag.eval ρ d) ∧
              ∀ p ∈ rest, EquivB (Dag.eval ρ p.1) (Dag.eval ρ p.2) := by
          intro a b c d ha hb hc hd e
          cases h1 : csf r k st a b with
          | ok st1 =>
            rw [h1] at e
            simp only [Res.bind] at e
            cases h2 : csf r k st1 c d with
            | ok st2 =>
              rw [h2] at e
              obtain ⟨b1, g1⟩ := csf_wf r k bd ha hb h1
              obtain ⟨b2, g2⟩ := csf_wf r k b1 (hc.mono g1.1) (hd.mono g1.1) h2
              obtain ⟨m2, restEq⟩ := commStates_sound k rest st2 b2 (restFit (g1.trans g2).1) e st' hx ρ m
              obtain ⟨m1, e2⟩ := csf_sound r k b1 (hc.mono g1.1) (hd.mono g1.1) h2 m2
              obtain ⟨m0, e1⟩ := csf_sound r k bd ha hb h1 m1
              exact ⟨m0, e1, e2, restEq⟩
            | fail => rw [h2] at e; cases e
            | gaveUp => rw [h2] at e; cases e
          | fail => rw [h1] at e; cases e
          | gaveUp => rw [h1] at e; cases e
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl
        · obtain ⟨m0, e1, e2, restEq⟩ := step _ _ _ _ hl.1 hr.1 hl.2 hr.2 e
          refine ⟨m0, fun p hp => ?_⟩
          rcases List.mem_cons.mp hp with rfl | hp
          · simp only [Dag.eval_comm]; exact .comm_congr f e1 e2
          · exact restEq p hp
        · obtain ⟨m0, e1, e2, restEq⟩ := step _ _ _ _ hl.1 hr.2 hl.2 hr.1 e
          refine ⟨m0, fun p hp => ?_⟩
          rcases List.mem_cons.mp hp with rfl | hp
          · simp only [Dag.eval_comm]; exact (EquivB.comm_congr f e1 e2).trans (.comm_swap f _ _)
          · exact restEq p hp
      · cases h
    · cases h

theorem commStates_complete (k : Nat) : ∀ (unifs : List (Dag s × Dag s)) (st : St s), Bounded st →
    (∀ p ∈ unifs, p.1.Fit st.vals.size ∧ p.2.Fit st.vals.size) →
    (∀ p ∈ unifs, (∃ f a c, p.1 = .comm f a c) ∧ ∃ f a c, p.2 = .comm f a c) →
    ∀ ρ, Models st ρ → (∀ p ∈ unifs, EquivB (Dag.eval ρ p.1) (Dag.eval ρ p.2)) →
    match commStates r k st unifs with
    | .ok L => ∃ st' ∈ L, ∃ ρ', Agree st.vals.size ρ ρ' ∧ Models st' ρ'
    | .fail => False
    | .gaveUp => True
  | [], st, _, _, _, ρ, m, _ => by
    simp only [commStates]
    exact ⟨st, List.mem_singleton_self _, ρ, fun _ _ => rfl, m⟩
  | (l, rt) :: rest, st, bd, hu, shape, ρ, m, eqs => by
    obtain ⟨⟨f, l0, l1, rfl⟩, ⟨g, r0, r1, rfl⟩⟩ := shape _ List.mem_cons_self
    simp only [commStates]
    by_cases fg : f = g
    · subst fg
      simp only [ite_true]
      have hl := fit_comm (hu _ List.mem_cons_self).1
      have hr := fit_comm (hu _ List.mem_cons_self).2
      have restFit : ∀ {n}, st.vals.size ≤ n → ∀ p ∈ rest, p.1.Fit n ∧ p.2.Fit n := fun le p hp =>
        ⟨(hu p (List.mem_cons_of_mem _ hp)).1.mono le, (hu p (List.mem_cons_of_mem _ hp)).2.mono le⟩
      have restShape := fun p hp => shape p (List.mem_cons_of_mem _ hp)
      have e0 := eqs _ List.mem_cons_self
      simp only [Dag.eval_comm] at e0
      -- one orientation that holds
      have branch : ∀ a b c d : Dag s, a.Fit st.vals.size → b.Fit st.vals.size → c.Fit st.vals.size →
          d.Fit st.vals.size → EquivB (Dag.eval ρ a) (Dag.eval ρ b) → EquivB (Dag.eval ρ c) (Dag.eval ρ d) →
          match ((csf r k st a b).bind fun st => csf r k st c d).bind (fun st => commStates r k st rest) with
          | .ok L => ∃ st' ∈ L, ∃ ρ', Agree st.vals.size ρ ρ' ∧ Models st' ρ'
          | .fail => False
          | .gaveUp => True := by
        intro a b c d ha hb hc hd eab ecd
        have p1 := csf_complete r k bd ha hb m eab
        cases h1 : csf r k st a b with
        | fail => rw [h1] at p1; exact p1
        | gaveUp => simp [Res.bind]
        | ok st1 =>
          rw [h1] at p1
          obtain ⟨ρ1, a1, m1⟩ := p1
          obtain ⟨b1, g1⟩ := csf_wf r k bd ha hb h1
          have ecd1 : EquivB (Dag.eval ρ1 c) (Dag.eval ρ1 d) := by
            rw [eval_agree a1 hc.2, eval_agree a1 hd.2]; exact ecd
          have p2 := csf_complete r k b1 (hc.mono g1.1) (hd.mono g1.1) m1 ecd1
          simp only [Res.bind]
          cases h2 : csf r k st1 c d with
          | fail => rw [h2] at p2; exact p2
          | gaveUp => simp
          | ok st2 =>
            rw [h2] at p2
            obtain ⟨ρ2, a2, m2⟩ := p2
            obtain ⟨b2, g2⟩ := csf_wf r k b1 (hc.mono g1.1) (hd.mono g1.1) h2
            have restEq : ∀ p ∈ rest, EquivB (Dag.eval ρ2 p.1) (Dag.eval ρ2 p.2) := by
              intro p hp
              have a12 := a1.trans a2 g1.1
              rw [eval_agree a12 (restFit (Nat.le_refl _) p hp).1.2, eval_agree a12 (restFit (Nat.le_refl _) p hp).2.2]
              exact eqs p (List.mem_cons_of_mem _ hp)
            have ih2 := commStates_complete k rest st2 b2 (restFit (g1.trans g2).1) restShape ρ2 m2 restEq
            simp only
            split
            · next L hL =>
              rw [hL] at ih2
              obtain ⟨st', hm, ρ', a3, m3⟩ := ih2
              exact ⟨st', hm, ρ', (a1.trans a2 g1.1).trans a3 (g1.trans g2).1, m3⟩
            · next hL => rw [hL] at ih2; exact ih2
            · trivial
      -- the concatenation reaches the branch that holds
      have reach : ∀ (o : Res (St s)), o ∈ [((csf r k st l0 r0).bind fun st => csf r k st l1 r1),
            ((csf r k st l0 r1).bind fun st => csf r k st l1 r0)] →
          (match o.bind (fun st => commStates r k st rest) with
            | .ok L => ∃ st' ∈ L, ∃ ρ', Agree st.vals.size ρ ρ' ∧ Models st' ρ'
            | .fail => False
            | .gaveUp => True) →
          match Res.concatMap (fun o => o.bind fun st => commStates r k st rest)
            [((csf r k st l0 r0).bind fun st => csf r k st l1 r1),
             ((csf r k st l0 r1).bind fun st => csf r k st l1 r0)] with
          | .ok L => ∃ st' ∈ L, ∃ ρ', Agree st.vals.size ρ ρ' ∧ Models st' ρ'
          | .fail => False
          | .gaveUp => True := by
        intro o ho good
        split at good
        · next L' hL' =>
          obtain ⟨st', hm, ρ', ag, mo⟩ := good
          rcases Res.concatMap_reaches (f := fun o => o.bind fun st => commStates r k st rest) ho hL' hm with
            g | ⟨L, eq, mem⟩
          · rw [g]; trivial
          · rw [eq]; exact ⟨st', mem, ρ', ag, mo⟩
        · exact good.elim
        · rw [Res.concatMap_gaveUp (f := fun o => o.bind fun st => commStates r k st rest) ho (by assumption)]; trivial
      rcases (Commutative.equiv_iff f _ _ _ _).mp e0 with ⟨ea, eb⟩ | ⟨ea, eb⟩
      · exact reach _ (by simp) (branch _ _ _ _ hl.1 hr.1 hl.2 hr.2 ea eb)
      · exact reach _ (by simp) (branch _ _ _ _ hl.1 hr.2 hl.2 hr.1 ea eb)
    · simp only [fg, ite_false]

/-! ### The pending stack -/

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem chooseTheory_none {st : St s} (h : chooseTheory st = none) : st.pending = [] := by
  unfold chooseTheory at h
  have stays : ∀ (l : List (Pend s)) (b : Theory s), (l.foldl chooseStep (some b)).isSome := by
    intro l
    induction l with
    | nil => intro b; rfl
    | cons x xs ih =>
      intro b
      simp only [List.foldl_cons, chooseStep]
      split
      · exact ih _
      · exact ih _
  cases e : st.pending.reverse with
  | nil => exact List.reverse_eq_nil_iff.mp e
  | cons x xs =>
    rw [e, List.foldl_cons] at h
    have := stays xs x.th
    simp only [chooseStep] at h
    rw [h] at this
    cases this

theorem run_step (k : Nat) (st : St s) (th : Theory s) (h : chooseTheory st = some th) :
    run r (k + 1) st = (match th with
      | .ac f => acStates r k (take st th).2 f (take st th).1
      | .comm _ => commStates r k (take st th).2 (take st th).1).bind (Res.concatMap (run r k)) := by
  cases th <;> simp [run, h, take]

theorem run_wf : ∀ (k : Nat) (st : St s), Bounded st → ∀ {L : List (St s)}, run r k st = .ok L →
    ∀ st' ∈ L, Bounded st' ∧ Grows st st' ∧ (∀ i, st'.sortOf i = st.sortOf i) ∧ st'.pending = []
  | 0, st, _, L, h => by simp [run] at h
  | k + 1, st, bd, L, h => by
    intro st' hm
    cases hc : chooseTheory st with
    | none =>
      simp only [run, hc, Res.ok.injEq] at h
      subst h
      simp at hm; subst hm
      exact ⟨bd, Grows.refl _, fun _ => rfl, chooseTheory_none hc⟩
    | some th =>
      rw [run_step r k st th hc] at h
      obtain ⟨b1, vals1, sorts1, fit1⟩ := take_bounded bd th
      have size1 : (take st th).2.vals.size = st.vals.size := by rw [vals1]
      have sortsEq : ∀ i, (take st th).2.sortOf i = st.sortOf i := by intro i; simp [St.sortOf, sorts1]
      cases hs : (match th with
        | .ac f => acStates r k (take st th).2 f (take st th).1
        | .comm _ => commStates r k (take st th).2 (take st th).1) with
      | ok M =>
        rw [hs] at h
        simp only [Res.bind] at h
        obtain ⟨st1, h1, M', e, hx⟩ := Res.mem_concatMap h hm
        have wf1 : Bounded st1 ∧ Grows (take st th).2 st1 ∧ ∀ i, st1.sortOf i = (take st th).2.sortOf i := by
          cases th with
          | ac f => exact acStates_wf r k b1 (by rw [size1]; exact fit1) hs st1 h1
          | comm f => exact commStates_wf r k _ _ b1 (by rw [size1]; exact fit1) hs st1 h1
        obtain ⟨b2, g2, s2, p2⟩ := run_wf k st1 wf1.1 e st' hx
        have g0 : Grows st (take st th).2 := ⟨Nat.le_of_eq size1.symm, fun i _ => sortsEq i⟩
        exact ⟨b2, g0.trans (wf1.2.1.trans g2), fun i => (s2 i).trans ((wf1.2.2 i).trans (sortsEq i)), p2⟩
      | fail => rw [hs] at h; cases h
      | gaveUp => rw [hs] at h; cases h

theorem run_sound : ∀ (k : Nat) (st : St s), Bounded st → ∀ {L : List (St s)}, run r k st = .ok L →
    ∀ st' ∈ L, ∀ ρ, Models st' ρ → Models st ρ
  | 0, st, _, L, h => by simp [run] at h
  | k + 1, st, bd, L, h => by
    intro st' hm ρ m
    cases hc : chooseTheory st with
    | none =>
      simp only [run, hc, Res.ok.injEq] at h
      subst h
      simp at hm; subst hm
      exact m
    | some th =>
      rw [run_step r k st th hc] at h
      obtain ⟨b1, vals1, _, fit1⟩ := take_bounded bd th
      have size1 : (take st th).2.vals.size = st.vals.size := by rw [vals1]
      cases hs : (match th with
        | .ac f => acStates r k (take st th).2 f (take st th).1
        | .comm _ => commStates r k (take st th).2 (take st th).1) with
      | ok M =>
        rw [hs] at h
        simp only [Res.bind] at h
        obtain ⟨st1, h1, M', e, hx⟩ := Res.mem_concatMap h hm
        have wf1 : Bounded st1 := by
          cases th with
          | ac f => exact (acStates_wf r k b1 (by rw [size1]; exact fit1) hs st1 h1).1
          | comm f => exact (commStates_wf r k _ _ b1 (by rw [size1]; exact fit1) hs st1 h1).1
        have m1 := run_sound k st1 wf1 e st' hx ρ m
        have back : Models (take st th).2 ρ ∧ ∀ p ∈ (take st th).1, EquivB (Dag.eval ρ p.1) (Dag.eval ρ p.2) := by
          cases th with
          | ac f => exact acStates_sound r k b1 (by rw [size1]; exact fit1) hs h1 m1
          | comm f => exact commStates_sound r k _ _ b1 (by rw [size1]; exact fit1) hs st1 h1 ρ m1
        exact (take_models st th ρ).mpr back
      | fail => rw [hs] at h; cases h
      | gaveUp => rw [hs] at h; cases h

theorem run_complete : ∀ (k : Nat) (st : St s), Bounded st → ∀ ρ, Models st ρ → Sorted st ρ →
    match run r k st with
    | .ok L => ∃ st' ∈ L, ∃ ρ', Agree st.vals.size ρ ρ' ∧ Models st' ρ'
    | .fail => False
    | .gaveUp => True
  | 0, _, _, _, _, _ => by simp [run]
  | k + 1, st, bd, ρ, m, so => by
    cases hc : chooseTheory st with
    | none =>
      simp only [run, hc]
      exact ⟨st, List.mem_singleton_self _, ρ, fun _ _ => rfl, m⟩
    | some th =>
      rw [run_step r k st th hc]
      obtain ⟨b1, vals1, sorts1, fit1⟩ := take_bounded bd th
      have size1 : (take st th).2.vals.size = st.vals.size := by rw [vals1]
      obtain ⟨m1, eqs⟩ := (take_models st th ρ).mp m
      have so1 : Sorted (take st th).2 ρ := by
        intro i srt h; apply so i srt; simpa [St.sortOf, sorts1] using h
      have sub : match (match th with
          | .ac f => acStates r k (take st th).2 f (take st th).1
          | .comm _ => commStates r k (take st th).2 (take st th).1) with
          | .ok L => ∃ st' ∈ L, ∃ ρ', Agree (take st th).2.vals.size ρ ρ' ∧ Models st' ρ'
          | .fail => False
          | .gaveUp => True := by
        cases th with
        | ac f => exact acStates_complete r k b1 (by rw [size1]; exact fit1) m1 so1 eqs
        | comm f =>
          exact commStates_complete r k _ _ b1 (by rw [size1]; exact fit1)
            (fun p hp => by
              obtain ⟨⟨a, c, e1⟩, ⟨a', c', e2⟩⟩ := take_comm_shape bd f p hp
              exact ⟨⟨f, a, c, e1⟩, ⟨f, a', c', e2⟩⟩) ρ m1 eqs
      cases hs : (match th with
        | .ac f => acStates r k (take st th).2 f (take st th).1
        | .comm _ => commStates r k (take st th).2 (take st th).1) with
      | ok M =>
        rw [hs] at sub
        simp only [Res.bind]
        obtain ⟨st1, h1, ρ1, a1, m1'⟩ := sub
        have wf1 : Bounded st1 ∧ Grows (take st th).2 st1 ∧ ∀ i, st1.sortOf i = (take st th).2.sortOf i := by
          cases th with
          | ac f => exact acStates_wf r k b1 (by rw [size1]; exact fit1) hs st1 h1
          | comm f => exact commStates_wf r k _ _ b1 (by rw [size1]; exact fit1) hs st1 h1
        have so2 : Sorted st1 ρ1 := so1.extend a1 wf1.2.2 b1
        have ih := run_complete k st1 wf1.1 ρ1 m1' so2
        split at ih
        · next L hL =>
          obtain ⟨st', hm, ρ', a2, m2⟩ := ih
          rcases Res.concatMap_reaches h1 hL hm with g | ⟨L', eq, mem⟩
          · rw [g]; trivial
          · rw [eq]
            refine ⟨st', mem, ρ', ?_, m2⟩
            rw [← size1]
            exact a1.trans a2 wf1.2.1.1
        · exact ih.elim
        · next hL => rw [Res.concatMap_gaveUp h1 hL]; trivial
      | fail => rw [hs] at sub; exact sub.elim
      | gaveUp => simp [Res.bind]

/-! ### The whole unification -/


omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem start_value (sorts : List SortId) (i : Nat) : (start (s := s) sorts).value i = none := by
  unfold St.value start
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem start_bounded (sorts : List SortId) : Bounded (start (s := s) sorts) := by
  refine ⟨by simp [start], fun i d h => ?_, fun p hp => by simp [start] at hp⟩
  rw [start_value] at h; cases h

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem start_models (sorts : List SortId) (ρ : Nat → Term s) : Models (start (s := s) sorts) ρ := by
  refine ⟨fun i d h => ?_, fun p hp => by simp [start] at hp⟩
  rw [start_value] at h; cases h

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem start_size (sorts : List SortId) : (start (s := s) sorts).vals.size = sorts.length := by simp [start]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem start_sortOf (sorts : List SortId) (i : Nat) : (start (s := s) sorts).sortOf i = sorts[i]? := by
  simp only [start, St.sortOf, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map]
  cases sorts[i]? <;> rfl


theorem solveAll_cons (k : Nat) (st : St s) (p : Dag s × Dag s) (ps : List (Dag s × Dag s)) :
    solveAll r k st (p :: ps) = (csf r k st p.1 p.2).bind fun st => solveAll r k st ps := by
  unfold solveAll
  rw [List.foldl_cons]
  show List.foldl _ (csf r k st p.1 p.2) ps = _
  generalize csf r k st p.1 p.2 = c
  have stuck : ∀ (c : Res (St s)), c = .fail ∨ c = .gaveUp → ∀ (qs : List (Dag s × Dag s)),
      List.foldl (fun (acc : Res (St s)) (p : Dag s × Dag s) => acc.bind fun st => csf r k st p.1 p.2) c qs = c := by
    intro c hc qs
    induction qs with
    | nil => rfl
    | cons q qs ih => rcases hc with rfl | rfl <;> exact ih
  cases c with
  | ok st' => rfl
  | fail => exact stuck _ (.inl rfl) ps
  | gaveUp => exact stuck _ (.inr rfl) ps

theorem solveAll_wf (k : Nat) : ∀ (eqs : List (Dag s × Dag s)) (st : St s), Bounded st →
    (∀ p ∈ eqs, p.1.Fit st.vals.size ∧ p.2.Fit st.vals.size) → ∀ {st' : St s}, solveAll r k st eqs = .ok st' →
    Bounded st' ∧ Grows st st' ∧ (∀ i, st'.sortOf i = st.sortOf i) ∧
      ∀ ρ, Models st' ρ → Models st ρ ∧ ∀ p ∈ eqs, EquivB (Dag.eval ρ p.1) (Dag.eval ρ p.2)
  | [], st, bd, _, st', h => by
    simp only [solveAll, List.foldl_nil, Res.ok.injEq] at h; subst h
    exact ⟨bd, Grows.refl _, fun _ => rfl, fun ρ m => ⟨m, fun p hp => by cases hp⟩⟩
  | p :: ps, st, bd, hf, st', h => by
    rw [solveAll_cons] at h
    have hp := hf p List.mem_cons_self
    cases h1 : csf r k st p.1 p.2 with
    | ok st1 =>
      rw [h1] at h
      simp only [Res.bind] at h
      obtain ⟨b1, g1⟩ := csf_wf r k bd hp.1 hp.2 h1
      obtain ⟨b2, g2, s2, sound⟩ := solveAll_wf k ps st1 b1
        (fun q hq => ⟨(hf q (List.mem_cons_of_mem _ hq)).1.mono g1.1, (hf q (List.mem_cons_of_mem _ hq)).2.mono g1.1⟩) h
      refine ⟨b2, g1.trans g2, fun i => (s2 i).trans (csf_sorts r k h1 i), fun ρ m => ?_⟩
      obtain ⟨m1, rest⟩ := sound ρ m
      obtain ⟨m0, e0⟩ := csf_sound r k bd hp.1 hp.2 h1 m1
      exact ⟨m0, fun q hq => by
        rcases List.mem_cons.mp hq with rfl | hq
        · exact e0
        · exact rest q hq⟩
    | fail => rw [h1] at h; cases h
    | gaveUp => rw [h1] at h; cases h

theorem solveAll_complete (k : Nat) : ∀ (eqs : List (Dag s × Dag s)) (st : St s), Bounded st →
    (∀ p ∈ eqs, p.1.Fit st.vals.size ∧ p.2.Fit st.vals.size) → ∀ ρ, Models st ρ →
    (∀ p ∈ eqs, EquivB (Dag.eval ρ p.1) (Dag.eval ρ p.2)) → Promise st ρ (solveAll r k st eqs)
  | [], st, _, _, ρ, m, _ => ⟨ρ, fun _ _ => rfl, m⟩
  | p :: ps, st, bd, hf, ρ, m, e => by
    rw [solveAll_cons]
    have hp := hf p List.mem_cons_self
    have c1 := csf_complete r k bd hp.1 hp.2 m (e p List.mem_cons_self)
    cases h1 : csf r k st p.1 p.2 with
    | ok st1 =>
      rw [h1] at c1
      obtain ⟨ρ1, a1, m1⟩ := c1
      obtain ⟨b1, g1⟩ := csf_wf r k bd hp.1 hp.2 h1
      have fit1 : ∀ q ∈ ps, q.1.Fit st1.vals.size ∧ q.2.Fit st1.vals.size := fun q hq =>
        ⟨(hf q (List.mem_cons_of_mem _ hq)).1.mono g1.1, (hf q (List.mem_cons_of_mem _ hq)).2.mono g1.1⟩
      have e1 : ∀ q ∈ ps, EquivB (Dag.eval ρ1 q.1) (Dag.eval ρ1 q.2) := by
        intro q hq
        rw [eval_agree a1 (hf q (List.mem_cons_of_mem _ hq)).1.2, eval_agree a1 (hf q (List.mem_cons_of_mem _ hq)).2.2]
        exact e q (List.mem_cons_of_mem _ hq)
      have c2 := solveAll_complete k ps st1 b1 fit1 ρ1 m1 e1
      simp only [Res.bind]
      cases h2 : solveAll r k st1 ps with
      | ok st2 =>
        rw [h2] at c2
        obtain ⟨ρ2, a2, m2⟩ := c2
        exact ⟨ρ2, a1.trans a2 g1.1, m2⟩
      | fail => rw [h2] at c2; exact c2
      | gaveUp => trivial
    | fail => rw [h1] at c1; exact c1.elim
    | gaveUp => trivial

/-- Soundness of the whole unification, at the level of dags: an answer,
whatever terms its output variables stand for, comes from a solution of the
equations that agrees with it on the original slots; its images respect the
sorts when the output variables respect theirs; and it mentions only its
output variables. -/
theorem unify_sound (k : Nat) (sorts : List SortId) (eqs : List (Dag s × Dag s))
    (fit : ∀ p ∈ eqs, p.1.Fit sorts.length ∧ p.2.Fit sorts.length) {answers : List (Answer s)}
    (h : unify r k sorts eqs = .ok answers) {ans : Answer s} (ha : ans ∈ answers) :
    (∀ out : Nat → Term s, ∃ ρ, (∀ p ∈ eqs, EquivB (Dag.eval ρ p.1) (Dag.eval ρ p.2)) ∧
      ∀ i < sorts.length, EquivB (ρ i) (Dag.eval out (ans.image i))) ∧
    (∀ out : Nat → Term s, (∀ j, HasSort (out j) (ans.sortAt j)) →
      ∀ i (hi : i < sorts.length), HasSort (Dag.eval out (ans.image i)) sorts[i]) ∧
    ans.images.length = sorts.length ∧ (∀ i < sorts.length, ∀ j ∈ (ans.image i).vars, j < ans.sorts.length) ∧
      ∀ i < sorts.length, (ans.image i).Wf := by
  unfold unify at h
  have fit0 : ∀ p ∈ eqs, p.1.Fit (start (s := s) sorts).vals.size ∧ p.2.Fit (start (s := s) sorts).vals.size := by
    rw [start_size]; exact fit
  split at h
  · cases h
  · simp only [Res.ok.injEq] at h; subst h; cases ha
  · next st hs =>
    obtain ⟨b1, g1, s1, sound1⟩ := solveAll_wf r k eqs _ (start_bounded sorts) fit0 hs
    cases hr : run r k st with
    | ok L =>
      rw [hr] at h
      simp only [Res.bind] at h
      obtain ⟨st2, h2, L', e, hx⟩ := Res.mem_concatMap h ha
      obtain ⟨b2, g2, s2, p2⟩ := run_wf r k st b1 hr st2 h2
      cases hf : finish r k sorts.length st2 with
      | ok o =>
        rw [hf] at e
        simp only [Res.map, Res.ok.injEq] at e
        subst e
        cases o with
        | none => cases hx
        | some a =>
          simp only [Option.toList_some, List.mem_singleton] at hx
          subst hx
          have nle : sorts.length ≤ st2.vals.size := by
            have := (g1.trans g2).1; rw [start_size] at this; exact this
          refine ⟨fun out => ?_, fun out hout i hi => ?_, finish_vars r k _ b2 nle hf⟩
          · obtain ⟨ρ, m, agree⟩ := finish_sound r k sorts.length b2 p2 hf out
            have m1 := run_sound r k st b1 hr st2 h2 ρ m
            exact ⟨ρ, (sound1 ρ m1).2, agree⟩
          · apply finish_sorted r k sorts.length b2 hf out hout i hi
            rw [s2 i, s1 i, start_sortOf]
            simp [hi]
      | fail => rw [hf] at e; cases e
      | gaveUp => rw [hf] at e; cases e
    | fail => rw [hr] at h; cases h
    | gaveUp => rw [hr] at h; cases h

/-- Completeness of the whole unification, at the level of dags: a solution of
the equations that gives the original slots their sorts is an instance of
some answer, through output values that respect the output sorts; the
unification does not fail. -/
theorem unify_complete (k : Nat) (sorts : List SortId) (eqs : List (Dag s × Dag s))
    (fit : ∀ p ∈ eqs, p.1.Fit sorts.length ∧ p.2.Fit sorts.length) (ρ : Nat → Term s)
    (sol : ∀ p ∈ eqs, EquivB (Dag.eval ρ p.1) (Dag.eval ρ p.2))
    (sorted : ∀ i (hi : i < sorts.length), HasSort (ρ i) sorts[i]) :
    match unify r k sorts eqs with
    | .ok answers => ∃ ans ∈ answers, ∃ δ : Nat → Term s, (∀ j, HasSort (δ j) (ans.sortAt j)) ∧
        ∀ i < sorts.length, EquivB (ρ i) (Dag.eval δ (ans.image i))
    | .fail => False
    | .gaveUp => True := by
  have fit0 : ∀ p ∈ eqs, p.1.Fit (start (s := s) sorts).vals.size ∧ p.2.Fit (start (s := s) sorts).vals.size := by
    rw [start_size]; exact fit
  have so0 : Sorted (start (s := s) sorts) ρ := by
    intro i srt h
    rw [start_sortOf] at h
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
    exact sorted i hi
  have c1 := solveAll_complete r k eqs _ (start_bounded sorts) fit0 ρ (start_models sorts ρ) sol
  unfold unify
  cases hs : solveAll r k (start sorts) eqs with
  | gaveUp => trivial
  | fail => rw [hs] at c1; exact c1.elim
  | ok st =>
    rw [hs] at c1
    obtain ⟨ρ1, a1, m1⟩ := c1
    simp only
    obtain ⟨b1, g1, s1, _⟩ := solveAll_wf r k eqs _ (start_bounded sorts) fit0 hs
    have so1 : Sorted st ρ1 := so0.extend a1 s1 (start_bounded sorts)
    have c2 := run_complete r k st b1 ρ1 m1 so1
    cases hr : run r k st with
    | gaveUp => simp [Res.bind]
    | fail => rw [hr] at c2; exact c2.elim
    | ok L =>
      rw [hr] at c2
      obtain ⟨st2, h2, ρ2, a2, m2⟩ := c2
      obtain ⟨b2, g2, s2, p2⟩ := run_wf r k st b1 hr st2 h2
      simp only [Res.bind]
      have nle : sorts.length ≤ st2.vals.size := by
        have := (g1.trans g2).1; rw [start_size] at this; exact this
      have a12 : Agree sorts.length ρ ρ2 := by
        have := a1.trans a2 g1.1; rw [start_size] at this; exact this
      have hsorts : ∀ i < sorts.length, st2.sortOf i ≠ none := by
        intro i hi
        rw [s2 i, s1 i, start_sortOf]
        simp [hi]
      have sorted2 : ∀ i < sorts.length, ∀ srt, st2.sortOf i = some srt → HasSort (ρ2 i) srt := by
        intro i hi srt h
        rw [s2 i, s1 i, start_sortOf] at h
        obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp h
        rw [a12 i hi]
        exact sorted i hi'
      have c3 := finish_complete r k sorts.length b2 nle hsorts m2 sorted2
      cases hf : finish r k sorts.length st2 with
      | gaveUp =>
        have : Res.concatMap (fun st => (finish r k sorts.length st).map fun a => a.toList) L = .gaveUp :=
          Res.concatMap_gaveUp (f := fun st => (finish r k sorts.length st).map fun a => a.toList) h2
            (by simp [hf, Res.map])
        rw [this]; trivial
      | fail => rw [hf] at c3; exact c3.elim
      | ok o =>
        rw [hf] at c3
        cases o with
        | none => exact c3.elim
        | some ans =>
          obtain ⟨δ, hδ, inst⟩ := c3
          rcases Res.concatMap_reaches (f := fun st => (finish r k sorts.length st).map fun a => a.toList) h2
            (by simp [hf, Res.map]) (List.mem_singleton_self ans) with g | ⟨L', eq, mem⟩
          · rw [g]; trivial
          · rw [eq]
            exact ⟨ans, mem, δ, hδ, fun i hi => by rw [← a12 i hi]; exact inst i hi⟩

end Tamarin.MaudeUnify
