import Tamarin.MaudeUnifySemantics
import Tamarin.Commutative

/-!
# Proofs of the solved-form steps

Auxiliary lemmas for `Tamarin.MaudeUnifySolvedForm`: facts about states, valuations, term
sizes and heads, and the four inductions on fuel (sorts, frame,
well-formedness, soundness, completeness) over the whole mutual block.
-/
namespace Tamarin.MaudeUnify
open Cancellation

variable {s : Signature}

/-! ### Term sizes and heads -/

theorem tsize_equiv {a b : Term s} (h : EquivB a b) : tsize a = tsize b := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | free f a b _ ih =>
    simp only [tsize]
    rw [show (fun i => tsize (a i)) = (fun i => tsize (b i)) from funext ih]
  | comm_congr _ _ _ ih ik | ac_congr _ _ _ ih ik => simp only [tsize, ih, ik]
  | comm_swap | ac_swap => simp only [tsize]; omega
  | ac_assoc => simp only [tsize]; omega

theorem nat_le_sum {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := ih h; simp; omega

theorem tsize_free_arg (f : s.FreeSym) (xs : Fin (s.arity f) → Term s) (i : Fin (s.arity f)) :
    tsize (xs i) < tsize (.free f xs) := by
  have := nat_le_sum (List.mem_ofFn.mpr ⟨i, rfl⟩ : tsize (xs i) ∈ List.ofFn fun i => tsize (xs i))
  show tsize (xs i) < 1 + (List.ofFn fun i => tsize (xs i)).sum
  omega

/-- The head symbol of a term, which B does not change. -/
def hd (t : Term s) : Head s := (headModel s).eval Head.var t

theorem hd_eq {a b : Term s} (h : EquivB a b) : hd a = hd b := h.head_eq

/-- Two lists related pointwise. -/
inductive Pw {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Pw R [] []
  | cons {a b as bs} : R a b → Pw R as bs → Pw R (a :: as) (b :: bs)

theorem Pw.length_eq {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β} (h : Pw R as bs) :
    as.length = bs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-! ### Dags -/

namespace Dag

theorem Fit.mono {n m : Nat} {d : Dag s} (h : d.Fit n) (le : n ≤ m) : d.Fit m :=
  ⟨h.1, fun j hj => Nat.lt_of_lt_of_le (h.2 j hj) le⟩

theorem below_var {n i : Nat} : (Dag.var i : Dag s).Below n ↔ i < n := by
  simp [Below, vars]

theorem fit_var {n i : Nat} : (Dag.var i : Dag s).Fit n ↔ i < n := by
  simp [Fit, Wf, below_var]

theorem eval_agree {n : Nat} {ρ ρ' : Nat → Term s} {d : Dag s} (h : d.Below n)
    (a : ∀ i < n, ρ' i = ρ i) : eval ρ' d = eval ρ d :=
  eval_congr d fun i hi => a i (h i hi)

theorem below_free {n : Nat} {f : s.FreeSym} {args : List (Dag s)} :
    (Dag.free f args).Below n ↔ ∀ d ∈ args, d.Below n := by
  simp only [Below, vars_free, List.mem_flatMap]
  constructor
  · intro h d hd j hj; exact h j ⟨d, hd, hj⟩
  · rintro h j ⟨d, hd, hj⟩; exact h d hd j hj

theorem below_ac {n : Nat} {f : s.ACSym} {args : List (Dag s)} :
    (Dag.ac f args).Below n ↔ ∀ d ∈ args, d.Below n := by
  simp only [Below, vars_ac, List.mem_flatMap]
  constructor
  · intro h d hd j hj; exact h j ⟨d, hd, hj⟩
  · rintro h j ⟨d, hd, hj⟩; exact h d hd j hj

theorem below_comm {n : Nat} {f : s.CSym} {a b : Dag s} :
    (Dag.comm f a b).Below n ↔ a.Below n ∧ b.Below n := by
  simp only [Below, vars, List.mem_append]
  constructor
  · intro h; exact ⟨fun j hj => h j (.inl hj), fun j hj => h j (.inr hj)⟩
  · rintro ⟨ha, hb⟩ j (hj | hj)
    · exact ha j hj
    · exact hb j hj

theorem fit_free {n : Nat} {f : s.FreeSym} {args : List (Dag s)} :
    (Dag.free f args).Fit n ↔ args.length = s.arity f ∧ ∀ d ∈ args, d.Fit n := by
  simp only [Fit, Wf, below_free]
  constructor
  · rintro ⟨⟨hl, hw⟩, hb⟩; exact ⟨hl, fun d hd => ⟨hw d hd, hb d hd⟩⟩
  · rintro ⟨hl, h⟩; exact ⟨⟨hl, fun d hd => (h d hd).1⟩, fun d hd => (h d hd).2⟩

theorem fit_comm {n : Nat} {f : s.CSym} {a b : Dag s} :
    (Dag.comm f a b).Fit n ↔ a.Fit n ∧ b.Fit n := by
  simp only [Fit, Wf, below_comm]
  constructor
  · rintro ⟨⟨wa, wb⟩, ba, bb⟩; exact ⟨⟨wa, ba⟩, wb, bb⟩
  · rintro ⟨⟨wa, ba⟩, wb, bb⟩; exact ⟨⟨wa, wb⟩, ba, bb⟩

theorem fit_ac {n : Nat} {f : s.ACSym} {args : List (Dag s)} :
    (Dag.ac f args).Fit n ↔ 2 ≤ args.length ∧ ∀ d ∈ args, d.Fit n := by
  simp only [Fit, Wf, below_ac]
  constructor
  · rintro ⟨⟨hl, hw⟩, hb⟩; exact ⟨hl, fun d hd => ⟨hw d hd, hb d hd⟩⟩
  · rintro ⟨hl, h⟩; exact ⟨⟨hl, fun d hd => (h d hd).1⟩, fun d hd => (h d hd).2⟩

theorem fit_atom {n : Nat} {a : s.Atom} : (Dag.atom a : Dag s).Fit n := by
  simp [Fit, Wf, Below, vars]

theorem hd_eval_atom (ρ : Nat → Term s) (a : s.Atom) : hd (eval ρ (.atom a)) = .atom a := by
  rw [eval_atom]; rfl

theorem hd_eval_free (ρ : Nat → Term s) (f : s.FreeSym) (args : List (Dag s)) :
    hd (eval ρ (.free f args)) = .free f := by
  rw [eval_free]; rfl

theorem hd_eval_comm (ρ : Nat → Term s) (f : s.CSym) (a b : Dag s) :
    hd (eval ρ (.comm f a b)) = .comm f := by
  rw [eval_comm]; rfl

theorem hd_eval_ac (ρ : Nat → Term s) (f : s.ACSym) {args : List (Dag s)} (h : 2 ≤ args.length) :
    hd (eval ρ (.ac f args)) = .ac f := by
  rw [eval_ac]
  match args, h with
  | a :: b :: rest, _ => rfl

/-- Every argument of a well-formed free node denotes a strictly smaller term. -/
theorem tsize_arg {ρ : Nat → Term s} {f : s.FreeSym} {args : List (Dag s)}
    (hl : args.length = s.arity f) {d : Dag s} (hd : d ∈ args) :
    tsize (eval ρ d) < tsize (eval ρ (.free f args)) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
  rw [eval_free]
  have := tsize_free_arg f (fun i : Fin (s.arity f) => (args.map (eval ρ)).getD i.val dflt) ⟨i, hl ▸ hi⟩
  simpa [List.getD_eq_getElem?_getD, hi] using this

/-- Pointwise equal argument lists give equal free nodes. -/
theorem eval_free_congr {ρ ρ' : Nat → Term s} {f : s.FreeSym} {as bs : List (Dag s)}
    (h : Pw (fun a b => EquivB (eval ρ a) (eval ρ' b)) as bs) :
    EquivB (eval ρ (.free f as)) (eval ρ' (.free f bs)) := by
  rw [eval_free, eval_free]
  apply EquivB.free
  intro i
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  generalize i.val = j
  induction h generalizing j with
  | nil => exact .refl _
  | cons hab _ ih =>
    cases j with
    | zero => exact hab
    | succ j => exact ih j

/-- Equal free nodes of well-formed argument lists have pointwise equal arguments. -/
theorem free_args_equiv {ρ ρ' : Nat → Term s} {f : s.FreeSym} {as bs : List (Dag s)}
    (ha : as.length = s.arity f) (hb : bs.length = s.arity f)
    (h : EquivB (eval ρ (.free f as)) (eval ρ' (.free f bs))) :
    Pw (fun a b => EquivB (eval ρ a) (eval ρ' b)) as bs := by
  rw [eval_free, eval_free, Matching.free_equiv_iff] at h
  have hi : ∀ i (h1 : i < as.length) (h2 : i < bs.length), EquivB (eval ρ as[i]) (eval ρ' bs[i]) := by
    intro i h1 h2
    have := h ⟨i, ha ▸ h1⟩
    simpa [List.getD_eq_getElem?_getD, h1, h2] using this
  have hlen : as.length = bs.length := ha.trans hb.symm
  clear h ha hb
  induction as generalizing bs with
  | nil => cases bs with
    | nil => exact .nil
    | cons => simp at hlen
  | cons a as ih => cases bs with
    | nil => simp at hlen
    | cons b bs =>
      refine .cons (hi 0 (by simp) (by simp)) (ih (bs := bs) (fun i h1 h2 => ?_) (by simpa using hlen))
      exact hi (i + 1) (by simpa using h1) (by simpa using h2)

end Dag

/-! ### States -/

namespace St

theorem value_lt {st : St s} {i : Nat} {d : Dag s} (h : st.value i = some d) : i < st.vals.size := by
  unfold value at h
  rw [Array.getD_eq_getD_getElem?] at h
  refine Classical.byContradiction fun hn => ?_
  rw [Array.getElem?_eq_none (by omega)] at h
  cases h

theorem value_fresh (st : St s) : st.fresh.1.value = st.value := by
  funext i
  simp only [value, fresh, Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split
  · next h => subst h; simp
  · rfl

theorem size_fresh (st : St s) : st.fresh.1.vals.size = st.vals.size + 1 := by
  simp [fresh]

theorem fresh_snd (st : St s) : st.fresh.2 = st.vals.size := rfl

theorem pending_fresh (st : St s) : st.fresh.1.pending = st.pending := rfl

theorem sortOf_fresh (st : St s) : st.fresh.1.sortOf = st.sortOf := by
  funext i
  simp only [sortOf, fresh, Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split
  · next h => subst h; simp
  · rfl

theorem size_bind (st : St s) (i : Nat) (v : Option (Dag s)) : (st.bind i v).vals.size = st.vals.size := by
  simp [bind]

theorem sortOf_bind (st : St s) (i : Nat) (v : Option (Dag s)) : (st.bind i v).sortOf = st.sortOf := rfl

theorem pending_bind (st : St s) (i : Nat) (v : Option (Dag s)) : (st.bind i v).pending = st.pending := rfl

theorem value_bind_ne (st : St s) {i j : Nat} (v : Option (Dag s)) (h : j ≠ i) :
    (st.bind i v).value j = st.value j := by
  simp only [value, bind, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  simp [Ne.symm h]

theorem value_bind_self (st : St s) {i : Nat} (v : Option (Dag s)) (h : i < st.vals.size) :
    (st.bind i v).value i = v := by
  simp only [value, bind, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  simp [h]

theorem value_bind_le (st : St s) (i j : Nat) (v : Option (Dag s)) :
    (st.bind i v).value j = st.value j ∨ (j = i ∧ (st.bind i v).value j = v) := by
  by_cases h : j = i
  · subst h
    by_cases hi : j < st.vals.size
    · exact .inr ⟨rfl, value_bind_self st v hi⟩
    · left
      simp only [value, bind, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
      simp [hi]
  · exact .inl (value_bind_ne st v h)

theorem value_push (st : St s) (th : Theory s) (l r : Dag s) : (st.push th l r).value = st.value := rfl

theorem size_push (st : St s) (th : Theory s) (l r : Dag s) :
    (st.push th l r).vals.size = st.vals.size := rfl

theorem sortOf_push (st : St s) (th : Theory s) (l r : Dag s) : (st.push th l r).sortOf = st.sortOf := rfl

theorem follow_none (st : St s) {x : Nat} (h : st.value x = none) (n : Nat) : st.follow n x = x := by
  cases n with
  | zero => rfl
  | succ n => simp [follow, h]

theorem lastVar_none (st : St s) {x : Nat} (h : st.value x = none) : st.lastVar x = x :=
  follow_none st h _

/-- The end of a chain is the start or the target of a variable binding. -/
theorem follow_cases (st : St s) (n x : Nat) :
    st.follow n x = x ∨ ∃ i, st.value i = some (.var (st.follow n x)) := by
  induction n generalizing x with
  | zero => exact .inl rfl
  | succ n ih =>
    simp only [follow]
    split
    · next y hy =>
      rcases ih y with h | ⟨i, hi⟩
      · exact .inr ⟨x, by rw [h]; exact hy⟩
      · exact .inr ⟨i, hi⟩
    · exact .inl rfl

theorem follow_equiv (st : St s) {ρ : Nat → Term s}
    (m : ∀ i d, st.value i = some d → EquivB (ρ i) (Dag.eval ρ d)) (n x : Nat) :
    EquivB (ρ x) (ρ (st.follow n x)) := by
  induction n generalizing x with
  | zero => exact .refl _
  | succ n ih =>
    simp only [follow]
    split
    · next y hy =>
      have := m x _ hy
      rw [Dag.eval_var] at this
      exact this.trans (ih y)
    · exact .refl _

end St

theorem models_lastVar {st : St s} {ρ : Nat → Term s} (m : Models st ρ) (x : Nat) :
    EquivB (ρ x) (ρ (st.lastVar x)) := st.follow_equiv m.binds _ _

theorem lastVar_lt {st : St s} (b : Bounded st) {x : Nat} (h : x < st.vals.size) :
    st.lastVar x < st.vals.size := by
  rcases st.follow_cases st.vals.size x with e | ⟨i, hi⟩
  · rw [St.lastVar, e]; exact h
  · exact Dag.fit_var.mp (b.vals _ _ hi)

/-! ### Models -/

theorem Models.except {st : St s} {ρ : Nat → Term s} (m : Models st ρ) (i : Nat) :
    ModelsExcept st ρ i := ⟨fun j d _ h => m.binds j d h, m.pend⟩

theorem ModelsExcept.models {st : St s} {ρ : Nat → Term s} {i : Nat} (m : ModelsExcept st ρ i)
    (h : ∀ d, st.value i = some d → EquivB (ρ i) (Dag.eval ρ d)) : Models st ρ :=
  ⟨fun j d hd => if e : j = i then by subst e; exact h d hd else m.binds j d e hd, m.pend⟩

theorem ModelsExcept.models_none {st : St s} {ρ : Nat → Term s} {i : Nat} (m : ModelsExcept st ρ i)
    (h : st.value i = none) : Models st ρ :=
  m.models fun d hd => by rw [h] at hd; cases hd

theorem models_bind_except {st : St s} {ρ : Nat → Term s} {i : Nat} {v : Option (Dag s)}
    (m : Models (st.bind i v) ρ) : ModelsExcept st ρ i :=
  ⟨fun j d hj hd => m.binds j d (by rw [St.value_bind_ne _ _ hj]; exact hd), m.pend⟩

theorem models_bind_some {st : St s} {ρ : Nat → Term s} {i : Nat} {d : Dag s}
    (m : Models (st.bind i (some d)) ρ) (h : i < st.vals.size) : EquivB (ρ i) (Dag.eval ρ d) :=
  m.binds i d (St.value_bind_self _ _ h)

theorem models_bind {st : St s} {ρ : Nat → Term s} {i : Nat} {v : Option (Dag s)}
    (m : ModelsExcept st ρ i) (h : ∀ d, v = some d → EquivB (ρ i) (Dag.eval ρ d)) :
    Models (st.bind i v) ρ := by
  refine ⟨fun j d hd => ?_, m.pend⟩
  rcases St.value_bind_le st i j v with e | ⟨rfl, e⟩
  · by_cases hj : j = i
    · subst hj
      have hd' := hd
      rw [e] at hd'
      rw [St.value_bind_self _ _ (St.value_lt hd')] at hd
      exact h d hd
    · rw [e] at hd; exact m.binds j d hj hd
  · exact h d (by rw [← e]; exact hd)

theorem models_fresh {st : St s} {ρ : Nat → Term s} : Models st.fresh.1 ρ ↔ Models st ρ := by
  constructor
  · intro m; exact ⟨fun i d h => m.binds i d (by rw [St.value_fresh]; exact h), m.pend⟩
  · intro m; exact ⟨fun i d h => m.binds i d (by rw [St.value_fresh] at h; exact h), m.pend⟩

theorem models_push {st : St s} {ρ : Nat → Term s} {th : Theory s} {l rt : Dag s} :
    Models (st.push th l rt) ρ ↔ Models st ρ ∧ EquivB (Dag.eval ρ l) (Dag.eval ρ rt) := by
  constructor
  · intro m
    exact ⟨⟨m.binds, fun p hp => m.pend p (List.mem_cons_of_mem _ hp)⟩, m.pend _ List.mem_cons_self⟩
  · rintro ⟨m, e⟩
    refine ⟨m.binds, fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact e
    · exact m.pend p hp

/-- A model of a bounded state is a model under any valuation that agrees on its slots. -/
theorem Models.agree {st : St s} {ρ ρ' : Nat → Term s} (b : Bounded st) (m : Models st ρ)
    (a : Agree st.vals.size ρ ρ') : Models st ρ' := by
  refine ⟨fun i d h => ?_, fun p hp => ?_⟩
  · rw [a i (St.value_lt h), Dag.eval_agree (b.vals i d h).2 a]
    exact m.binds i d h
  · obtain ⟨hl, hr, _⟩ := b.pend p hp
    rw [Dag.eval_agree hl.2 a, Dag.eval_agree hr.2 a]
    exact m.pend p hp

theorem Agree.refl (n : Nat) (ρ : Nat → Term s) : Agree n ρ ρ := fun _ _ => rfl

theorem Agree.trans {n m : Nat} {ρ ρ' ρ'' : Nat → Term s} (a : Agree n ρ ρ') (a' : Agree m ρ' ρ'')
    (le : n ≤ m) : Agree n ρ ρ'' := fun i hi => (a' i (by omega)).trans (a i hi)

/-! ### Bounded states -/

theorem Bounded.fresh {st : St s} (b : Bounded st) : Bounded st.fresh.1 := by
  refine ⟨by simp [St.fresh, b.sizes], fun i d h => ?_, fun p hp => ?_⟩
  · rw [St.value_fresh] at h
    exact (b.vals i d h).mono (by rw [St.size_fresh]; omega)
  · obtain ⟨hl, hr, sh⟩ := b.pend p hp
    exact ⟨hl.mono (by rw [St.size_fresh]; omega), hr.mono (by rw [St.size_fresh]; omega), sh⟩

theorem Bounded.bind {st : St s} (b : Bounded st) (i : Nat) {v : Option (Dag s)}
    (h : ∀ d, v = some d → d.Fit st.vals.size) : Bounded (st.bind i v) := by
  refine ⟨by rw [St.size_bind]; exact b.sizes, fun j d hd => ?_, fun p hp => ?_⟩
  · rw [St.size_bind]
    rcases St.value_bind_le st i j v with e | ⟨_, e⟩
    · rw [e] at hd; exact b.vals j d hd
    · rw [e] at hd; exact h d hd
  · rw [St.size_bind]; exact b.pend p hp

theorem Bounded.push {st : St s} (b : Bounded st) {th : Theory s} {l rt : Dag s}
    (hl : l.Fit st.vals.size) (hr : rt.Fit st.vals.size) (sh : Pend.Shaped ⟨th, l, rt⟩) :
    Bounded (st.push th l rt) := by
  refine ⟨b.sizes, b.vals, fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨hl, hr, sh⟩
  · exact b.pend p hp

/-! ### Outcomes -/

namespace Res
variable {α β : Type}

theorem bind_ok {x : Res α} {f : α → Res β} {b : β} :
    x.bind f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind]

theorem map_ok {x : Res α} {f : α → β} {b : β} :
    x.map f = .ok b ↔ ∃ a, x = .ok a ∧ f a = b := by
  cases x <;> simp [map]

/-- What completeness promises of an outcome: `Q` of a success, no failure. -/
def Prom (Q : α → Prop) : Res α → Prop
  | .ok a => Q a
  | .fail => False
  | .gaveUp => True

theorem Prom.bind {Q : α → Prop} {R : β → Prop} {x : Res α} {f : α → Res β} (h : Prom Q x)
    (k : ∀ a, x = .ok a → Q a → Prom R (f a)) : Prom R (x.bind f) := by
  cases x with
  | ok a => exact k a rfl h
  | fail => exact h.elim
  | gaveUp => trivial

theorem Prom.map {Q : α → Prop} {R : β → Prop} {x : Res α} {f : α → β} (h : Prom Q x)
    (k : ∀ a, x = .ok a → Q a → R (f a)) : Prom R (x.map f) := by
  cases x with
  | ok a => exact k a rfl h
  | fail => exact h.elim
  | gaveUp => trivial

theorem Prom.mono {Q R : α → Prop} {x : Res α} (h : Prom Q x) (k : ∀ a, x = .ok a → Q a → R a) :
    Prom R x := by
  cases x with
  | ok a => exact k a rfl h
  | fail => exact h.elim
  | gaveUp => trivial

end Res

theorem promise_iff {st : St s} {ρ : Nat → Term s} {x : Res (St s)} :
    Promise st ρ x ↔ Res.Prom (fun st' => ∃ ρ', Agree st.vals.size ρ ρ' ∧ Models st' ρ') x := by
  cases x <;> rfl

/-! ### Shapes of the steps -/

variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]
variable (r : Ranks s)

def freshCsf (k : Nat) (st : St s) (a : Dag s) : Res (St s × Dag s) :=
  (csf r k st.fresh.1 a (.var st.vals.size)).map fun st' => (st', .var st.vals.size)

def pHead (k : Nat) (st : St s) (a : Dag s) (rep : Nat) : Res (St s × Dag s) :=
  match a with
  | .var y => if st.lastVar y = rep then .fail else .ok (st, .var y)
  | .atom c => .ok (st, .atom c)
  | .free g bs => if (Dag.free g bs).ground then .ok (st, .free g bs)
      else (purifyArgs r k st bs rep).map fun q => (q.1, .free g q.2)
  | .ac g bs => freshCsf r k st (.ac g bs)
  | .comm g a b => freshCsf r k st (.comm g a b)

theorem purifyArgs_cons (k : Nat) (st : St s) (a : Dag s) (as : List (Dag s)) (rep : Nat) :
    purifyArgs r (k+1) st (a :: as) rep =
    (pHead r k st a rep).bind fun p => (purifyArgs r k p.1 as rep).map fun q => (q.1, p.2 :: q.2) := by
  rw [purifyArgs.eq_def]; try rfl
  cases a <;> rfl

def varBody (k : Nat) (st : St s) (lv rv : Nat) : Res (St s) :=
  match st.value lv with
  | none => safeRepl r k st lv rv
  | some lt => match st.value rv with
    | none => safeRepl r k st rv lv
    | some rt' => (safeRepl r k st lv rv).bind fun st => csf r k st lt rt'

theorem varCsf_var (k : Nat) (st : St s) (x y : Nat) : varCsf r (k+1) st x (.var y) =
    if st.lastVar x = st.lastVar y then .ok st
    else if r.sortIndex (st.sortOf (st.lastVar x)) > r.sortIndex (st.sortOf (st.lastVar y))
    then varBody r k st (st.lastVar y) (st.lastVar x) else varBody r k st (st.lastVar x) (st.lastVar y) := by
  rw [varCsf.eq_def]; try rfl
  by_cases h0 : st.lastVar x = st.lastVar y
  · simp only [h0, ite_true]
  · simp only [h0, ite_false]
    by_cases hc : r.sortIndex (st.sortOf (st.lastVar x)) > r.sortIndex (st.sortOf (st.lastVar y))
    · simp only [hc, ite_true]; rfl
    · simp only [hc, ite_false]; rfl

theorem varCsf_nonvar (k : Nat) (st : St s) (x : Nat) (rt : Dag s) (h : ∀ y, rt ≠ .var y) :
    varCsf r (k+1) st x rt = csf2 r k st rt (.var x) := by
  rw [varCsf.eq_def]; try rfl
  cases rt <;> first | exact absurd rfl (h _) | rfl

def commBody (k : Nat) (st : St s) (f : s.CSym) (l0 l1 r0 r1 : Dag s) : Res (St s) :=
  let both := fun (st : St s) => (csf r k st l0 r0).bind fun st => csf r k st l1 r1
  let pushed := Res.ok (st.push (.comm f) (.comm f l0 l1) (.comm f r0 r1))
  if l0 = r0 then csf r k st l1 r1 else
  match orderEq r st l1 r0 with
  | .eq => csf r k st l0 r1
  | .lt => if l0 = l1 ∨ r0 = r1 then both st else pushed
  | .gt =>
    match orderEq r st l1 r1 with
    | .eq => csf r k st l0 r0
    | .lt => pushed
    | .gt => if r0 = r1 then both st else pushed

theorem commCsf_comm (k : Nat) (st : St s) (f g : s.CSym) (l0 l1 r0 r1 : Dag s) :
    commCsf r (k+1) st f l0 l1 (.comm g r0 r1) =
    if f ≠ g then .fail else if orderEq r st l0 r0 = .gt then commBody r k st f r0 r1 l0 l1
    else commBody r k st f l0 l1 r0 r1 := by
  rw [commCsf.eq_def]; try rfl
  by_cases h0 : f = g
  · subst h0
    simp only [ne_eq, not_true_eq_false, ite_false]
    by_cases hc : orderEq r st l0 r0 = .gt
    · simp only [hc, ite_true]; rfl
    · simp only [hc, ite_false]; rfl
  · simp only [ne_eq, h0, not_false_eq_true, ite_true]

def pLeft (k : Nat) (st : St s) (a : Dag s) : Res (St s × Dag s) :=
  match a with
  | .var y => .ok (st, .var y)
  | a => freshCsf r k st a

def pRight (k : Nat) (st : St s) (a b a' : Dag s) : Res (St s × Dag s) :=
  if b = a then .ok (st, a') else
  match b with
  | .var y => .ok (st, .var y)
  | b => freshCsf r k st b

theorem purifyC_succ (k : Nat) (st : St s) (f : s.CSym) (a b : Dag s) :
    purifyC r (k+1) st f a b =
    (pLeft r k st a).bind fun p => (pRight r k p.1 a b p.2).map fun q => (q.1, mkComm' r q.1 f p.2 q.2) := by
  rw [purifyC.eq_def]; try rfl
  cases a <;> cases b <;> rfl

theorem pHead_var (k : Nat) (st : St s) (y rep : Nat) :
    pHead r k st (.var y) rep = if st.lastVar y = rep then .fail else .ok (st, .var y) := rfl
theorem pHead_atom (k : Nat) (st : St s) (c : s.Atom) (rep : Nat) :
    pHead r k st (.atom c) rep = .ok (st, .atom c) := rfl
theorem pHead_free (k : Nat) (st : St s) (g : s.FreeSym) (bs : List (Dag s)) (rep : Nat) :
    pHead r k st (.free g bs) rep = if (Dag.free g bs).ground then .ok (st, .free g bs)
      else (purifyArgs r k st bs rep).map fun q => (q.1, .free g q.2) := rfl
theorem pHead_ac (k : Nat) (st : St s) (g : s.ACSym) (bs : List (Dag s)) (rep : Nat) :
    pHead r k st (.ac g bs) rep = freshCsf r k st (.ac g bs) := rfl
theorem pHead_comm (k : Nat) (st : St s) (g : s.CSym) (c d : Dag s) (rep : Nat) :
    pHead r k st (.comm g c d) rep = freshCsf r k st (.comm g c d) := rfl

theorem pLeft_cases (k : Nat) (st : St s) (a : Dag s) :
    ((∃ y, a = .var y) ∧ pLeft r k st a = .ok (st, a)) ∨
    ((∀ y, a ≠ .var y) ∧ pLeft r k st a = freshCsf r k st a) := by
  cases a with
  | var y => exact .inl ⟨⟨y, rfl⟩, rfl⟩
  | _ => exact .inr ⟨fun _ => nofun, rfl⟩

theorem pRight_cases (k : Nat) (st : St s) (a b a' : Dag s) :
    (b = a ∧ pRight r k st a b a' = .ok (st, a')) ∨
    ((∃ y, b = .var y) ∧ pRight r k st a b a' = .ok (st, b)) ∨
    ((∀ y, b ≠ .var y) ∧ pRight r k st a b a' = freshCsf r k st b) := by
  unfold pRight
  by_cases h : b = a
  · exact .inl ⟨h, by simp [h]⟩
  · simp only [h, ite_false]
    cases b with
    | var y => exact .inr (.inl ⟨⟨y, rfl⟩, rfl⟩)
    | _ => exact .inr (.inr ⟨fun _ => nofun, rfl⟩)

theorem csf_succ (k : Nat) (st : St s) (l rt : Dag s) : csf r (k+1) st l rt =
    if !l.ground then csf2 r k st l rt else if !rt.ground then csf2 r k st rt l
    else if Dag.same l rt then .ok st else .fail := by
  rw [csf.eq_def]; try rfl

theorem csf2_var (k : Nat) (st : St s) (x : Nat) (rt : Dag s) :
    csf2 r (k+1) st (.var x) rt = varCsf r k st x rt := by rw [csf2.eq_def]; try rfl
theorem csf2_atom (k : Nat) (st : St s) (a : s.Atom) (rt : Dag s) :
    csf2 r (k+1) st (.atom a) rt = constCsf r k st (.atom a) rt := by rw [csf2.eq_def]; try rfl
theorem csf2_free (k : Nat) (st : St s) (f : s.FreeSym) (args : List (Dag s)) (rt : Dag s) :
    csf2 r (k+1) st (.free f args) rt = freeCsf r k st f args rt := by rw [csf2.eq_def]; try rfl
theorem csf2_ac (k : Nat) (st : St s) (f : s.ACSym) (args : List (Dag s)) (rt : Dag s) :
    csf2 r (k+1) st (.ac f args) rt = acCsf r k st f args rt := by rw [csf2.eq_def]; try rfl
theorem csf2_comm (k : Nat) (st : St s) (f : s.CSym) (a b : Dag s) (rt : Dag s) :
    csf2 r (k+1) st (.comm f a b) rt = commCsf r k st f a b rt := by rw [csf2.eq_def]; try rfl

theorem safeRepl_succ (k : Nat) (st : St s) (old new : Nat) : safeRepl r (k+1) st old new =
    match (st.bind old (some (.var new))).value new with
    | none => .ok (st.bind old (some (.var new)))
    | some nb =>
      if nb.ground then .ok (st.bind old (some (.var new)))
      else if chainsTo (st.bind old (some (.var new))) nb new then
        csf2 r k ((st.bind old (some (.var new))).bind new none) nb (.var new)
      else .ok (st.bind old (some (.var new))) := by
  rw [safeRepl.eq_def]; try rfl

theorem constCsf_var (k : Nat) (st : St s) (c : Dag s) (y : Nat) : constCsf r (k+1) st c (.var y) =
    match st.value (st.lastVar y) with
    | some val => csf r k st c val
    | none => .ok (st.bind (st.lastVar y) (some c)) := by
  rw [constCsf.eq_def]; try rfl

theorem constCsf_nonvar (k : Nat) (st : St s) (c rt : Dag s) (h : ∀ y, rt ≠ .var y) :
    constCsf r (k+1) st c rt = .fail := by
  rw [constCsf.eq_def]; try rfl
  cases rt <;> first | exact absurd rfl (h _) | rfl

theorem freeCsf_free (k : Nat) (st : St s) (f g : s.FreeSym) (args bs : List (Dag s)) :
    freeCsf r (k+1) st f args (.free g bs) = if f = g then csfList r k st args bs else .fail := by
  rw [freeCsf.eq_def]; try rfl

theorem freeCsf_var (k : Nat) (st : St s) (f : s.FreeSym) (args : List (Dag s)) (y : Nat) :
    freeCsf r (k+1) st f args (.var y) =
    match st.value (st.lastVar y) with
    | some val => csf r k st (.free f args) val
    | none =>
      if (Dag.free f args).ground then .ok (st.bind (st.lastVar y) (some (.free f args)))
      else (purifyArgs r k st args (st.lastVar y)).bind fun p =>
        .ok (p.1.bind (st.lastVar y) (some (.free f p.2))) := by
  rw [freeCsf.eq_def]; try rfl

theorem freeCsf_other (k : Nat) (st : St s) (f : s.FreeSym) (args : List (Dag s)) (rt : Dag s)
    (h1 : ∀ y, rt ≠ .var y) (h2 : ∀ g bs, rt ≠ .free g bs) : freeCsf r (k+1) st f args rt = .fail := by
  rw [freeCsf.eq_def]; try rfl
  cases rt <;> first | exact absurd rfl (h1 _) | exact absurd rfl (h2 _ _) | rfl

theorem csfList_nil (k : Nat) (st : St s) : csfList r (k+1) st [] [] = .ok st := by
  rw [csfList.eq_def]; try rfl
theorem csfList_cons (k : Nat) (st : St s) (a b : Dag s) (as bs : List (Dag s)) :
    csfList r (k+1) st (a :: as) (b :: bs) = (csf r k st a b).bind fun st => csfList r k st as bs := by
  rw [csfList.eq_def]; try rfl
theorem csfList_nil_cons (k : Nat) (st : St s) (b : Dag s) (bs : List (Dag s)) :
    csfList r (k+1) st [] (b :: bs) = .fail := by
  rw [csfList.eq_def]; try rfl
theorem csfList_cons_nil (k : Nat) (st : St s) (a : Dag s) (as : List (Dag s)) :
    csfList r (k+1) st (a :: as) [] = .fail := by
  rw [csfList.eq_def]; try rfl

theorem purifyArgs_nil (k : Nat) (st : St s) (rep : Nat) : purifyArgs r (k+1) st [] rep = .ok (st, []) := by
  rw [purifyArgs.eq_def]; try rfl

theorem acCsf_ac (k : Nat) (st : St s) (f g : s.ACSym) (args bs : List (Dag s)) :
    acCsf r (k+1) st f args (.ac g bs) =
    if f = g then .ok (st.push (.ac f) (.ac f args) (.ac g bs)) else .fail := by
  rw [acCsf.eq_def]; try rfl

theorem acCsf_var (k : Nat) (st : St s) (f : s.ACSym) (args : List (Dag s)) (y : Nat) :
    acCsf r (k+1) st f args (.var y) =
    match st.value (st.lastVar y) with
    | some val => csf2 r k st (.ac f args) val
    | none => .ok (st.push (.ac f) (.ac f args) (.var y)) := by
  rw [acCsf.eq_def]; try rfl

theorem acCsf_other (k : Nat) (st : St s) (f : s.ACSym) (args : List (Dag s)) (rt : Dag s)
    (h1 : ∀ y, rt ≠ .var y) (h2 : ∀ g bs, rt ≠ .ac g bs) : acCsf r (k+1) st f args rt = .fail := by
  rw [acCsf.eq_def]; try rfl
  cases rt <;> first | exact absurd rfl (h1 _) | exact absurd rfl (h2 _ _) | rfl

theorem commCsf_var (k : Nat) (st : St s) (f : s.CSym) (a b : Dag s) (y : Nat) :
    commCsf r (k+1) st f a b (.var y) =
    match st.value (st.lastVar y) with
    | some val => commCsf r k st f a b val
    | none => (purifyC r k st f a b).bind fun p => .ok (p.1.bind (st.lastVar y) (some p.2)) := by
  rw [commCsf.eq_def]; try rfl

theorem commCsf_other (k : Nat) (st : St s) (f : s.CSym) (a b rt : Dag s)
    (h1 : ∀ y, rt ≠ .var y) (h2 : ∀ g c d, rt ≠ .comm g c d) : commCsf r (k+1) st f a b rt = .fail := by
  rw [commCsf.eq_def]; try rfl
  cases rt <;> first | exact absurd rfl (h1 _) | exact absurd rfl (h2 _ _ _) | rfl

theorem orderEq_eq {st : St s} {x y : Dag s} (h : orderEq r st x y = .eq) : x = y := by
  unfold orderEq at h
  split at h
  · assumption
  · split at h <;> first | cases h | (next o h1 h2 => exact absurd h h2)

/-- The branches of the C case. -/
theorem commBody_cases (k : Nat) (st : St s) (f : s.CSym) (l0 l1 r0 r1 : Dag s) :
    (l0 = r0 ∧ commBody r k st f l0 l1 r0 r1 = csf r k st l1 r1) ∨
    (l1 = r0 ∧ commBody r k st f l0 l1 r0 r1 = csf r k st l0 r1) ∨
    (l1 = r1 ∧ commBody r k st f l0 l1 r0 r1 = csf r k st l0 r0) ∨
    ((l0 = l1 ∨ r0 = r1) ∧
      commBody r k st f l0 l1 r0 r1 = (csf r k st l0 r0).bind fun st => csf r k st l1 r1) ∨
    commBody r k st f l0 l1 r0 r1 = .ok (st.push (.comm f) (.comm f l0 l1) (.comm f r0 r1)) := by
  unfold commBody
  by_cases h0 : l0 = r0
  · exact .inl ⟨h0, by simp [h0]⟩
  · simp only [h0, ite_false]
    split
    · next he => exact .inr (.inl ⟨orderEq_eq r he, rfl⟩)
    · split
      · next hc => exact .inr (.inr (.inr (.inl ⟨hc, rfl⟩)))
      · exact .inr (.inr (.inr (.inr rfl)))
    · split
      · next he => exact .inr (.inr (.inl ⟨orderEq_eq r he, rfl⟩))
      · exact .inr (.inr (.inr (.inr rfl)))
      · split
        · next hc => exact .inr (.inr (.inr (.inl ⟨.inr hc, rfl⟩)))
        · exact .inr (.inr (.inr (.inr rfl)))

/-- The branches of a variable against a variable. -/
theorem varBody_cases (k : Nat) (st : St s) (lv rv : Nat) :
    (st.value lv = none ∧ varBody r k st lv rv = safeRepl r k st lv rv) ∨
    (∃ lt, st.value lv = some lt ∧ st.value rv = none ∧ varBody r k st lv rv = safeRepl r k st rv lv) ∨
    (∃ lt rt', st.value lv = some lt ∧ st.value rv = some rt' ∧
      varBody r k st lv rv = (safeRepl r k st lv rv).bind fun st => csf r k st lt rt') := by
  unfold varBody
  split
  · next h => exact .inl ⟨h, rfl⟩
  · next lt h =>
    split
    · next h' => exact .inr (.inl ⟨lt, h, h', rfl⟩)
    · next rt' h' => exact .inr (.inr ⟨lt, rt', h, h', rfl⟩)

theorem varCsf_var_cases (k : Nat) (st : St s) (x y : Nat) :
    (st.lastVar x = st.lastVar y ∧ varCsf r (k+1) st x (.var y) = .ok st) ∨
    ∃ lv rv, ((lv = st.lastVar x ∧ rv = st.lastVar y) ∨ (lv = st.lastVar y ∧ rv = st.lastVar x)) ∧
      lv ≠ rv ∧ varCsf r (k+1) st x (.var y) = varBody r k st lv rv := by
  rw [varCsf_var]
  by_cases h0 : st.lastVar x = st.lastVar y
  · exact .inl ⟨h0, by simp [h0]⟩
  · simp only [h0, ite_false]
    split
    · exact .inr ⟨_, _, .inr ⟨rfl, rfl⟩, Ne.symm h0, rfl⟩
    · exact .inr ⟨_, _, .inl ⟨rfl, rfl⟩, h0, rfl⟩


/-! ### Slots and sorts only grow -/

/-- A later state keeps the slots and all sorts of an earlier one. -/
def Ext (st st' : St s) : Prop := st.vals.size ≤ st'.vals.size ∧ ∀ i, st'.sortOf i = st.sortOf i

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem Ext.refl (st : St s) : Ext st st := ⟨Nat.le_refl _, fun _ => rfl⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem Ext.trans {a b c : St s} (h : Ext a b) (h' : Ext b c) : Ext a c :=
  ⟨Nat.le_trans h.1 h'.1, fun i => (h'.2 i).trans (h.2 i)⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem Ext.bind (st : St s) (i : Nat) (v : Option (Dag s)) : Ext st (st.bind i v) :=
  ⟨Nat.le_of_eq (St.size_bind st i v).symm, fun _ => rfl⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem Ext.push (st : St s) (th : Theory s) (l rt : Dag s) : Ext st (st.push th l rt) :=
  ⟨Nat.le_refl _, fun _ => rfl⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem Ext.fresh (st : St s) : Ext st st.fresh.1 :=
  ⟨by rw [St.size_fresh]; omega, fun i => by rw [St.sortOf_fresh]⟩

structure ExtK (k : Nat) : Prop where
  csf : ∀ {st st' l rt}, csf r k st l rt = .ok st' → Ext st st'
  csf2 : ∀ {st st' l rt}, csf2 r k st l rt = .ok st' → Ext st st'
  var : ∀ {st st' x rt}, varCsf r k st x rt = .ok st' → Ext st st'
  safe : ∀ {st st' o n}, safeRepl r k st o n = .ok st' → Ext st st'
  const : ∀ {st st' c rt}, constCsf r k st c rt = .ok st' → Ext st st'
  free : ∀ {st st' f args rt}, freeCsf r k st f args rt = .ok st' → Ext st st'
  list : ∀ {st st' as bs}, csfList r k st as bs = .ok st' → Ext st st'
  pArgs : ∀ {st st' args rep ps}, purifyArgs r k st args rep = .ok (st', ps) → Ext st st'
  ac : ∀ {st st' f args rt}, acCsf r k st f args rt = .ok st' → Ext st st'
  pC : ∀ {st st' f a b p}, purifyC r k st f a b = .ok (st', p) → Ext st st'
  comm : ∀ {st st' f a b rt}, commCsf r k st f a b rt = .ok st' → Ext st st'

theorem extK_zero : ExtK r 0 where
  csf h := by rw [csf.eq_def] at h; cases h
  csf2 h := by rw [csf2.eq_def] at h; cases h
  var h := by rw [varCsf.eq_def] at h; cases h
  safe h := by rw [safeRepl.eq_def] at h; cases h
  const h := by rw [constCsf.eq_def] at h; cases h
  free h := by rw [freeCsf.eq_def] at h; cases h
  list h := by rw [csfList.eq_def] at h; cases h
  pArgs h := by rw [purifyArgs.eq_def] at h; cases h
  ac h := by rw [acCsf.eq_def] at h; cases h
  pC h := by rw [purifyC.eq_def] at h; cases h
  comm h := by rw [commCsf.eq_def] at h; cases h

theorem ext_freshCsf {k : Nat} (ih : ExtK r k) {st st' : St s} {a a' : Dag s}
    (h : freshCsf r k st a = .ok (st', a')) : Ext st st' := by
  obtain ⟨st1, h1, e⟩ := Res.map_ok.mp h
  cases e
  exact (Ext.fresh st).trans (ih.csf h1)

theorem ext_pHead {k : Nat} (ih : ExtK r k) {st st1 : St s} {a a' : Dag s} {rep : Nat}
    (h1 : pHead r k st a rep = .ok (st1, a')) : Ext st st1 := by
  cases a with
  | var y =>
    rw [pHead_var] at h1
    split at h1
    · cases h1
    · cases h1; exact .refl _
  | atom c => cases h1; exact .refl _
  | free g bs =>
    rw [pHead_free] at h1
    split at h1
    · cases h1; exact .refl _
    · obtain ⟨⟨st3, ps3⟩, h4, e⟩ := Res.map_ok.mp h1
      cases e
      exact ih.pArgs h4
  | ac g bs => exact ext_freshCsf r ih h1
  | comm g c d => exact ext_freshCsf r ih h1

theorem extK_succ {k : Nat} (ih : ExtK r k) : ExtK r (k + 1) where
  csf {st st' l rt} h := by
    rw [csf_succ] at h
    split at h
    · exact ih.csf2 h
    · split at h
      · exact ih.csf2 h
      · split at h
        · cases h; exact .refl _
        · cases h
  csf2 {st st' l rt} h := by
    cases l with
    | var x => rw [csf2_var] at h; exact ih.var h
    | atom a => rw [csf2_atom] at h; exact ih.const h
    | free f args => rw [csf2_free] at h; exact ih.free h
    | ac f args => rw [csf2_ac] at h; exact ih.ac h
    | comm f a b => rw [csf2_comm] at h; exact ih.comm h
  var {st st' x rt} h := by
    by_cases hv : ∃ y, rt = .var y
    · obtain ⟨y, rfl⟩ := hv
      rcases varCsf_var_cases r k st x y with ⟨_, e⟩ | ⟨lv, rv, _, _, e⟩
      · rw [e] at h; cases h; exact .refl _
      · rw [e] at h
        rcases varBody_cases r k st lv rv with ⟨_, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, _, _, e⟩ <;> rw [e] at h
        · exact ih.safe h
        · exact ih.safe h
        · obtain ⟨st1, h1, h2⟩ := Res.bind_ok.mp h
          exact (ih.safe h1).trans (ih.csf h2)
    · rw [varCsf_nonvar r k st x rt fun y e => hv ⟨y, e⟩] at h
      exact ih.csf2 h
  safe {st st' o n} h := by
    rw [safeRepl_succ] at h
    have e1 := Ext.bind st o (some (.var n))
    split at h
    · cases h; exact e1
    · split at h
      · cases h; exact e1
      · split at h
        · exact (e1.trans (Ext.bind _ _ _)).trans (ih.csf2 h)
        · cases h; exact e1
  const {st st' c rt} h := by
    by_cases hv : ∃ y, rt = .var y
    · obtain ⟨y, rfl⟩ := hv
      rw [constCsf_var] at h
      split at h
      · exact ih.csf h
      · cases h; exact Ext.bind _ _ _
    · rw [constCsf_nonvar r k st c rt fun y e => hv ⟨y, e⟩] at h; cases h
  free {st st' f args rt} h := by
    cases rt with
    | free g bs =>
      rw [freeCsf_free] at h
      split at h
      · exact ih.list h
      · cases h
    | var y =>
      rw [freeCsf_var] at h
      split at h
      · exact ih.csf h
      · split at h
        · cases h; exact Ext.bind _ _ _
        · obtain ⟨⟨st1, ps⟩, h1, h2⟩ := Res.bind_ok.mp h
          cases h2
          exact (ih.pArgs h1).trans (Ext.bind _ _ _)
    | atom | ac | comm => rw [freeCsf_other] at h <;> first | cases h | simp
  list {st st' as bs} h := by
    cases as with
    | nil => cases bs with
      | nil => rw [csfList_nil] at h; cases h; exact .refl _
      | cons => rw [csfList_nil_cons] at h; cases h
    | cons a as => cases bs with
      | nil => rw [csfList_cons_nil] at h; cases h
      | cons b bs =>
        rw [csfList_cons] at h
        obtain ⟨st1, h1, h2⟩ := Res.bind_ok.mp h
        exact (ih.csf h1).trans (ih.list h2)
  pArgs {st st' args rep ps} h := by
    cases args with
    | nil => rw [purifyArgs_nil] at h; cases h; exact .refl _
    | cons a as =>
      rw [purifyArgs_cons] at h
      obtain ⟨⟨st1, a'⟩, h1, h2⟩ := Res.bind_ok.mp h
      obtain ⟨⟨st2, ps'⟩, h3, e⟩ := Res.map_ok.mp h2
      cases e
      exact (ext_pHead r ih h1).trans (ih.pArgs h3)
  ac {st st' f args rt} h := by
    cases rt with
    | ac g bs =>
      rw [acCsf_ac] at h
      split at h
      · cases h; exact Ext.push _ _ _ _
      · cases h
    | var y =>
      rw [acCsf_var] at h
      split at h
      · exact ih.csf2 h
      · cases h; exact Ext.push _ _ _ _
    | atom | free | comm => rw [acCsf_other] at h <;> first | cases h | simp
  pC {st st' f a b p} h := by
    rw [purifyC_succ] at h
    obtain ⟨⟨st1, a'⟩, h1, h2⟩ := Res.bind_ok.mp h
    obtain ⟨⟨st2, b'⟩, h3, e⟩ := Res.map_ok.mp h2
    cases e
    have e1 : Ext st st1 := by
      rcases pLeft_cases r k st a with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] at h1
      · cases h1; exact .refl _
      · exact ext_freshCsf r ih h1
    refine e1.trans ?_
    rcases pRight_cases r k st1 a b a' with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] at h3
    · cases h3; exact .refl _
    · cases h3; exact .refl _
    · exact ext_freshCsf r ih h3
  comm {st st' f a b rt} h := by
    cases rt with
    | comm g c d =>
      rw [commCsf_comm] at h
      split at h
      · cases h
      · have body : ∀ {l0 l1 r0 r1}, commBody r k st f l0 l1 r0 r1 = .ok st' → Ext st st' := by
          intro l0 l1 r0 r1 h
          rcases commBody_cases r k st f l0 l1 r0 r1 with
            ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ | e <;> rw [e] at h
          · exact ih.csf h
          · exact ih.csf h
          · exact ih.csf h
          · obtain ⟨st1, h1, h2⟩ := Res.bind_ok.mp h
            exact (ih.csf h1).trans (ih.csf h2)
          · cases h; exact Ext.push _ _ _ _
        split at h <;> exact body h
    | var y =>
      rw [commCsf_var] at h
      split at h
      · exact ih.comm h
      · obtain ⟨⟨st1, p⟩, h1, h2⟩ := Res.bind_ok.mp h
        cases h2
        exact (ih.pC h1).trans (Ext.bind _ _ _)
    | atom | free | ac => rw [commCsf_other] at h <;> first | cases h | simp

theorem extK : ∀ k, ExtK r k
  | 0 => extK_zero r
  | k + 1 => extK_succ r (extK k)


/-! ### Abstracting a term by a fresh variable binds no older slot -/

/-- The slots of `st` other than `av` keep their values in `st'`. -/
def Frame (st st' : St s) (av : Nat) : Prop := ∀ i < st.vals.size, i ≠ av → st'.value i = st.value i

/-- All slots of `st` keep their values in `st'`. -/
def FrameAll (st st' : St s) : Prop := ∀ i < st.vals.size, st'.value i = st.value i

structure FrameK (k : Nat) : Prop where
  csf : ∀ {st st' a av}, (∀ y, a ≠ .var y) → st.value av = none →
    csf r k st a (.var av) = .ok st' → Frame st st' av
  csf2a : ∀ {st st' a av}, (∀ y, a ≠ .var y) → st.value av = none →
    csf2 r k st a (.var av) = .ok st' → Frame st st' av
  csf2v : ∀ {st st' a av}, (∀ y, a ≠ .var y) → st.value av = none →
    csf2 r k st (.var av) a = .ok st' → Frame st st' av
  var : ∀ {st st' a av}, (∀ y, a ≠ .var y) → st.value av = none →
    varCsf r k st av a = .ok st' → Frame st st' av
  const : ∀ {st st' c av}, st.value av = none → constCsf r k st c (.var av) = .ok st' → Frame st st' av
  free : ∀ {st st' f args av}, st.value av = none →
    freeCsf r k st f args (.var av) = .ok st' → Frame st st' av
  pArgs : ∀ {st st' args rep ps}, purifyArgs r k st args rep = .ok (st', ps) → FrameAll st st'
  ac : ∀ {st st' f args av}, st.value av = none → acCsf r k st f args (.var av) = .ok st' → Frame st st' av
  pC : ∀ {st st' f a b p}, purifyC r k st f a b = .ok (st', p) → FrameAll st st'
  comm : ∀ {st st' f a b av}, st.value av = none →
    commCsf r k st f a b (.var av) = .ok st' → Frame st st' av

theorem frameK_zero : FrameK r 0 where
  csf _ _ h := by rw [csf.eq_def] at h; cases h
  csf2a _ _ h := by rw [csf2.eq_def] at h; cases h
  csf2v _ _ h := by rw [csf2.eq_def] at h; cases h
  var _ _ h := by rw [varCsf.eq_def] at h; cases h
  const _ h := by rw [constCsf.eq_def] at h; cases h
  free _ h := by rw [freeCsf.eq_def] at h; cases h
  pArgs h := by rw [purifyArgs.eq_def] at h; cases h
  ac _ h := by rw [acCsf.eq_def] at h; cases h
  pC h := by rw [purifyC.eq_def] at h; cases h
  comm _ h := by rw [commCsf.eq_def] at h; cases h

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem St.value_size_none (st : St s) : st.value st.vals.size = none := by
  cases h : st.value st.vals.size with
  | none => rfl
  | some d => exact absurd (St.value_lt h) (Nat.lt_irrefl _)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem frame_bind {st : St s} {av : Nat} (v : Option (Dag s)) : Frame st (st.bind av v) av :=
  fun _ _ hi => St.value_bind_ne _ _ hi

theorem frame_freshCsf {k : Nat} (ih : FrameK r k) {st st' : St s} {a a' : Dag s}
    (hv : ∀ y, a ≠ .var y) (h : freshCsf r k st a = .ok (st', a')) : FrameAll st st' := by
  obtain ⟨st1, h1, e⟩ := Res.map_ok.mp h
  cases e
  have := ih.csf hv (by rw [St.value_fresh]; exact St.value_size_none st) h1
  intro i hi
  rw [this i (by rw [St.size_fresh]; omega) (by omega), St.value_fresh]

theorem frameK_succ {k : Nat} (ih : FrameK r k) : FrameK r (k + 1) where
  csf {st st' a av} hv hn h := by
    rw [csf_succ] at h
    split at h
    · exact ih.csf2a hv hn h
    · split at h
      · exact ih.csf2v hv hn h
      · next h1 h2 => simp [Dag.ground, Dag.vars] at h2
  csf2a {st st' a av} hv hn h := by
    cases a with
    | var x => exact absurd rfl (hv x)
    | atom c => rw [csf2_atom] at h; exact ih.const hn h
    | free f args => rw [csf2_free] at h; exact ih.free hn h
    | ac f args => rw [csf2_ac] at h; exact ih.ac hn h
    | comm f c d => rw [csf2_comm] at h; exact ih.comm hn h
  csf2v {st st' a av} hv hn h := by
    rw [csf2_var] at h; exact ih.var hv hn h
  var {st st' a av} hv hn h := by
    rw [varCsf_nonvar r k st av a hv] at h; exact ih.csf2a hv hn h
  const {st st' c av} hn h := by
    rw [constCsf_var] at h
    simp only [St.lastVar_none st hn, hn] at h
    cases h; exact frame_bind _
  free {st st' f args av} hn h := by
    rw [freeCsf_var] at h
    simp only [St.lastVar_none st hn, hn] at h
    split at h
    · cases h; exact frame_bind _
    · obtain ⟨⟨st1, ps⟩, h1, h2⟩ := Res.bind_ok.mp h
      cases h2
      intro i hi hne
      rw [St.value_bind_ne _ _ hne, ih.pArgs h1 i hi]
  pArgs {st st' args rep ps} h := by
    cases args with
    | nil => rw [purifyArgs_nil] at h; cases h; intro i _; rfl
    | cons a as =>
      rw [purifyArgs_cons] at h
      obtain ⟨⟨st1, a'⟩, h1, h2⟩ := Res.bind_ok.mp h
      obtain ⟨⟨st2, ps'⟩, h3, e⟩ := Res.map_ok.mp h2
      cases e
      have f1 : FrameAll st st1 := by
        cases a with
        | var y =>
          rw [pHead_var] at h1
          split at h1
          · cases h1
          · cases h1; intro i _; rfl
        | atom c => cases h1; intro i _; rfl
        | free g bs =>
          rw [pHead_free] at h1
          split at h1
          · cases h1; intro i _; rfl
          · obtain ⟨⟨st3, ps3⟩, h4, e⟩ := Res.map_ok.mp h1
            cases e
            exact ih.pArgs h4
        | ac g bs => exact frame_freshCsf r ih (fun _ h => by cases h) h1
        | comm g c d => exact frame_freshCsf r ih (fun _ h => by cases h) h1
      intro i hi
      rw [ih.pArgs h3 i (Nat.lt_of_lt_of_le hi (ext_pHead r (extK r k) h1).1), f1 i hi]
  ac {st st' f args av} hn h := by
    rw [acCsf_var] at h
    simp only [St.lastVar_none st hn, hn] at h
    cases h; intro i _ _; rfl
  pC {st st' f a b p} h := by
    rw [purifyC_succ] at h
    obtain ⟨⟨st1, a'⟩, h1, h2⟩ := Res.bind_ok.mp h
    obtain ⟨⟨st2, b'⟩, h3, e⟩ := Res.map_ok.mp h2
    cases e
    have f1 : FrameAll st st1 := by
      rcases pLeft_cases r k st a with ⟨_, e⟩ | ⟨hv, e⟩ <;> rw [e] at h1
      · cases h1; intro i _; rfl
      · exact frame_freshCsf r ih hv h1
    have f2 : FrameAll st1 st2 := by
      rcases pRight_cases r k st1 a b a' with ⟨_, e⟩ | ⟨_, e⟩ | ⟨hv, e⟩ <;> rw [e] at h3
      · cases h3; intro i _; rfl
      · cases h3; intro i _; rfl
      · exact frame_freshCsf r ih hv h3
    have le : st.vals.size ≤ st1.vals.size := by
      rcases pLeft_cases r k st a with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] at h1
      · cases h1; exact Nat.le_refl _
      · exact (ext_freshCsf r (extK r k) h1).1
    intro i hi
    rw [f2 i (Nat.lt_of_lt_of_le hi le), f1 i hi]
  comm {st st' f a b av} hn h := by
    rw [commCsf_var] at h
    simp only [St.lastVar_none st hn, hn] at h
    obtain ⟨⟨st1, p⟩, h1, h2⟩ := Res.bind_ok.mp h
    cases h2
    intro i hi hne
    rw [St.value_bind_ne _ _ hne, ih.pC h1 i hi]

theorem frameK : ∀ k, FrameK r k
  | 0 => frameK_zero r
  | k + 1 => frameK_succ r (frameK k)


/-! ### Well-formedness -/

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem shaped_ac_ac (f : s.ACSym) (args bs : List (Dag s)) : Pend.Shaped ⟨.ac f, .ac f args, .ac f bs⟩ :=
  ⟨⟨_, rfl⟩, .inl ⟨_, rfl⟩⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem shaped_ac_var (f : s.ACSym) (args : List (Dag s)) (y : Nat) :
    Pend.Shaped ⟨.ac f, .ac f args, .var y⟩ :=
  ⟨⟨_, rfl⟩, .inr ⟨_, rfl⟩⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem shaped_comm (f : s.CSym) (a b c d : Dag s) : Pend.Shaped ⟨.comm f, .comm f a b, .comm f c d⟩ :=
  ⟨⟨_, _, rfl⟩, _, _, rfl⟩

theorem fit_mkComm {n : Nat} (st : St s) (f : s.CSym) {a b : Dag s} (ha : a.Fit n) (hb : b.Fit n) :
    (mkComm' r st f a b).Fit n := by
  unfold mkComm' Dag.mkComm
  split
  · exact Dag.fit_comm.mpr ⟨hb, ha⟩
  · exact Dag.fit_comm.mpr ⟨ha, hb⟩

structure WfK (k : Nat) : Prop where
  csf : ∀ {st st' l rt}, Bounded st → l.Fit st.vals.size → rt.Fit st.vals.size →
    csf r k st l rt = .ok st' → Bounded st'
  csf2 : ∀ {st st' l rt}, Bounded st → l.Fit st.vals.size → rt.Fit st.vals.size →
    csf2 r k st l rt = .ok st' → Bounded st'
  var : ∀ {st st' x rt}, Bounded st → x < st.vals.size → rt.Fit st.vals.size →
    varCsf r k st x rt = .ok st' → Bounded st'
  safe : ∀ {st st' o n}, Bounded st → o < st.vals.size → n < st.vals.size →
    safeRepl r k st o n = .ok st' → Bounded st'
  const : ∀ {st st' c rt}, Bounded st → c.Fit st.vals.size → rt.Fit st.vals.size →
    constCsf r k st c rt = .ok st' → Bounded st'
  free : ∀ {st st' f args rt}, Bounded st → (Dag.free f args).Fit st.vals.size → rt.Fit st.vals.size →
    freeCsf r k st f args rt = .ok st' → Bounded st'
  list : ∀ {st st' as bs}, Bounded st → (∀ a ∈ as, a.Fit st.vals.size) → (∀ b ∈ bs, b.Fit st.vals.size) →
    csfList r k st as bs = .ok st' → Bounded st'
  pArgs : ∀ {st st' args rep ps}, Bounded st → (∀ a ∈ args, a.Fit st.vals.size) →
    purifyArgs r k st args rep = .ok (st', ps) →
    Bounded st' ∧ (∀ p ∈ ps, p.Fit st'.vals.size) ∧ ps.length = args.length
  ac : ∀ {st st' f args rt}, Bounded st → (Dag.ac f args).Fit st.vals.size → rt.Fit st.vals.size →
    acCsf r k st f args rt = .ok st' → Bounded st'
  pC : ∀ {st st' f a b p}, Bounded st → a.Fit st.vals.size → b.Fit st.vals.size →
    purifyC r k st f a b = .ok (st', p) → Bounded st' ∧ p.Fit st'.vals.size
  comm : ∀ {st st' f a b rt}, Bounded st → a.Fit st.vals.size → b.Fit st.vals.size → rt.Fit st.vals.size →
    commCsf r k st f a b rt = .ok st' → Bounded st'

theorem wfK_zero : WfK r 0 where
  csf _ _ _ h := by rw [csf.eq_def] at h; cases h
  csf2 _ _ _ h := by rw [csf2.eq_def] at h; cases h
  var _ _ _ h := by rw [varCsf.eq_def] at h; cases h
  safe _ _ _ h := by rw [safeRepl.eq_def] at h; cases h
  const _ _ _ h := by rw [constCsf.eq_def] at h; cases h
  free _ _ _ h := by rw [freeCsf.eq_def] at h; cases h
  list _ _ _ h := by rw [csfList.eq_def] at h; cases h
  pArgs _ _ h := by rw [purifyArgs.eq_def] at h; cases h
  ac _ _ _ h := by rw [acCsf.eq_def] at h; cases h
  pC _ _ _ h := by rw [purifyC.eq_def] at h; cases h
  comm _ _ _ _ h := by rw [commCsf.eq_def] at h; cases h

theorem wf_freshCsf {k : Nat} (ih : WfK r k) {st st' : St s} {a a' : Dag s} (b : Bounded st)
    (ha : a.Fit st.vals.size) (h : freshCsf r k st a = .ok (st', a')) : Bounded st' ∧ a'.Fit st'.vals.size := by
  obtain ⟨st1, h1, e⟩ := Res.map_ok.mp h
  cases e
  have le := ((extK r k).csf h1).1
  rw [St.size_fresh] at le
  refine ⟨ih.csf b.fresh (ha.mono (by rw [St.size_fresh]; omega))
    (Dag.fit_var.mpr (by rw [St.size_fresh]; omega)) h1, Dag.fit_var.mpr (by omega)⟩

theorem wf_pHead {k : Nat} (ih : WfK r k) {st st1 : St s} {a a' : Dag s} {rep : Nat} (b : Bounded st)
    (ha : a.Fit st.vals.size) (h1 : pHead r k st a rep = .ok (st1, a')) :
    Bounded st1 ∧ a'.Fit st1.vals.size := by
  cases a with
  | var y =>
    rw [pHead_var] at h1
    split at h1
    · cases h1
    · cases h1; exact ⟨b, ha⟩
  | atom c => cases h1; exact ⟨b, ha⟩
  | free g bs =>
    rw [pHead_free] at h1
    split at h1
    · cases h1; exact ⟨b, ha⟩
    · obtain ⟨⟨st3, ps3⟩, h4, e⟩ := Res.map_ok.mp h1
      cases e
      obtain ⟨hl, hf⟩ := Dag.fit_free.mp ha
      obtain ⟨b3, f3, l3⟩ := ih.pArgs b hf h4
      exact ⟨b3, Dag.fit_free.mpr ⟨l3.trans hl, f3⟩⟩
  | ac g bs => exact wf_freshCsf r ih b ha h1
  | comm g c d => exact wf_freshCsf r ih b ha h1

theorem wf_pLeft {k : Nat} (ih : WfK r k) {st st1 : St s} {a a' : Dag s} (b : Bounded st)
    (ha : a.Fit st.vals.size) (h1 : pLeft r k st a = .ok (st1, a')) :
    Bounded st1 ∧ a'.Fit st1.vals.size ∧ st.vals.size ≤ st1.vals.size := by
  rcases pLeft_cases r k st a with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] at h1
  · cases h1; exact ⟨b, ha, Nat.le_refl _⟩
  · exact ⟨(wf_freshCsf r ih b ha h1).1, (wf_freshCsf r ih b ha h1).2,
      (ext_freshCsf r (extK r k) h1).1⟩

theorem wf_pRight {k : Nat} (ih : WfK r k) {st1 st2 : St s} {a c a' b' : Dag s} (b1 : Bounded st1)
    (ha' : a'.Fit st1.vals.size) (hc : c.Fit st1.vals.size) (h3 : pRight r k st1 a c a' = .ok (st2, b')) :
    Bounded st2 ∧ b'.Fit st2.vals.size ∧ st1.vals.size ≤ st2.vals.size := by
  rcases pRight_cases r k st1 a c a' with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] at h3
  · cases h3; exact ⟨b1, ha', Nat.le_refl _⟩
  · cases h3; exact ⟨b1, hc, Nat.le_refl _⟩
  · exact ⟨(wf_freshCsf r ih b1 hc h3).1, (wf_freshCsf r ih b1 hc h3).2,
      (ext_freshCsf r (extK r k) h3).1⟩

theorem wfK_succ {k : Nat} (ih : WfK r k) : WfK r (k + 1) where
  csf {st st' l rt} b hl hr h := by
    rw [csf_succ] at h
    split at h
    · exact ih.csf2 b hl hr h
    · split at h
      · exact ih.csf2 b hr hl h
      · split at h
        · cases h; exact b
        · cases h
  csf2 {st st' l rt} b hl hr h := by
    cases l with
    | var x => rw [csf2_var] at h; exact ih.var b (Dag.fit_var.mp hl) hr h
    | atom a => rw [csf2_atom] at h; exact ih.const b hl hr h
    | free f args => rw [csf2_free] at h; exact ih.free b hl hr h
    | ac f args => rw [csf2_ac] at h; exact ih.ac b hl hr h
    | comm f a c =>
      rw [csf2_comm] at h
      exact ih.comm b (Dag.fit_comm.mp hl).1 (Dag.fit_comm.mp hl).2 hr h
  var {st st' x rt} b hx hr h := by
    by_cases hv : ∃ y, rt = .var y
    · obtain ⟨y, rfl⟩ := hv
      have hy := Dag.fit_var.mp hr
      rcases varCsf_var_cases r k st x y with ⟨_, e⟩ | ⟨lv, rv, hlr, _, e⟩
      · rw [e] at h; cases h; exact b
      · rw [e] at h
        have hlv : lv < st.vals.size ∧ rv < st.vals.size := by
          rcases hlr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨lastVar_lt b hx, lastVar_lt b hy⟩
          · exact ⟨lastVar_lt b hy, lastVar_lt b hx⟩
        rcases varBody_cases r k st lv rv with ⟨_, e⟩ | ⟨_, _, _, e⟩ | ⟨lt, rt', hlt, hrt, e⟩ <;>
          rw [e] at h
        · exact ih.safe b hlv.1 hlv.2 h
        · exact ih.safe b hlv.2 hlv.1 h
        · obtain ⟨st1, h1, h2⟩ := Res.bind_ok.mp h
          have le := ((extK r k).safe h1).1
          exact ih.csf (ih.safe b hlv.1 hlv.2 h1) ((b.vals _ _ hlt).mono le) ((b.vals _ _ hrt).mono le) h2
    · rw [varCsf_nonvar r k st x rt fun y e => hv ⟨y, e⟩] at h
      exact ih.csf2 b hr (Dag.fit_var.mpr hx) h
  safe {st st' o n} b ho hn h := by
    rw [safeRepl_succ] at h
    have b1 : Bounded (st.bind o (some (.var n))) :=
      b.bind o fun d e => by cases e; exact Dag.fit_var.mpr hn
    split at h
    · cases h; exact b1
    · next nb hnb =>
      split at h
      · cases h; exact b1
      · split at h
        · refine ih.csf2 (b1.bind n fun _ e => by cases e) ?_ ?_ h
          · rw [St.size_bind]; exact b1.vals _ _ hnb
          · rw [St.size_bind, St.size_bind]; exact Dag.fit_var.mpr hn
        · cases h; exact b1
  const {st st' c rt} b hc hr h := by
    by_cases hv : ∃ y, rt = .var y
    · obtain ⟨y, rfl⟩ := hv
      rw [constCsf_var] at h
      split at h
      · next val hval => exact ih.csf b hc (b.vals _ _ hval) h
      · cases h; exact b.bind _ fun d e => by cases e; exact hc
    · rw [constCsf_nonvar r k st c rt fun y e => hv ⟨y, e⟩] at h; cases h
  free {st st' f args rt} b hl hr h := by
    cases rt with
    | free g bs =>
      rw [freeCsf_free] at h
      split at h
      · exact ih.list b (Dag.fit_free.mp hl).2 (Dag.fit_free.mp hr).2 h
      · cases h
    | var y =>
      rw [freeCsf_var] at h
      split at h
      · next val hval => exact ih.csf b hl (b.vals _ _ hval) h
      · split at h
        · cases h; exact b.bind _ fun d e => by cases e; exact hl
        · obtain ⟨⟨st1, ps⟩, h1, h2⟩ := Res.bind_ok.mp h
          cases h2
          obtain ⟨hlen, hf⟩ := Dag.fit_free.mp hl
          obtain ⟨b1, f1, l1⟩ := ih.pArgs b hf h1
          exact b1.bind _ fun d e => by cases e; exact Dag.fit_free.mpr ⟨l1.trans hlen, f1⟩
    | atom | ac | comm => rw [freeCsf_other] at h <;> first | cases h | simp
  list {st st' as bs} b ha hb h := by
    cases as with
    | nil => cases bs with
      | nil => rw [csfList_nil] at h; cases h; exact b
      | cons => rw [csfList_nil_cons] at h; cases h
    | cons a as => cases bs with
      | nil => rw [csfList_cons_nil] at h; cases h
      | cons c bs =>
        rw [csfList_cons] at h
        obtain ⟨st1, h1, h2⟩ := Res.bind_ok.mp h
        have le := ((extK r k).csf h1).1
        exact ih.list (ih.csf b (ha a List.mem_cons_self) (hb c List.mem_cons_self) h1)
          (fun x hx => (ha x (List.mem_cons_of_mem _ hx)).mono le)
          (fun x hx => (hb x (List.mem_cons_of_mem _ hx)).mono le) h2
  pArgs {st st' args rep ps} b ha h := by
    cases args with
    | nil => rw [purifyArgs_nil] at h; cases h; exact ⟨b, by simp, rfl⟩
    | cons a as =>
      rw [purifyArgs_cons] at h
      obtain ⟨⟨st1, a'⟩, h1, h2⟩ := Res.bind_ok.mp h
      obtain ⟨⟨st2, ps'⟩, h3, e⟩ := Res.map_ok.mp h2
      cases e
      obtain ⟨b1, f1⟩ := wf_pHead r ih b (ha a List.mem_cons_self) h1
      have le := (ext_pHead r (extK r k) h1).1
      obtain ⟨b2, f2, l2⟩ := ih.pArgs b1 (fun x hx => (ha x (List.mem_cons_of_mem _ hx)).mono le) h3
      have le2 := ((extK r k).pArgs h3).1
      refine ⟨b2, fun p hp => ?_, by simp [l2]⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · exact f1.mono le2
      · exact f2 p hp
  ac {st st' f args rt} b hl hr h := by
    cases rt with
    | ac g bs =>
      rw [acCsf_ac] at h
      split at h
      · next e => cases h; subst e; exact b.push hl hr (shaped_ac_ac f args bs)
      · cases h
    | var y =>
      rw [acCsf_var] at h
      split at h
      · next val hval => exact ih.csf2 b hl (b.vals _ _ hval) h
      · cases h; exact b.push hl hr (shaped_ac_var f args y)
    | atom | free | comm => rw [acCsf_other] at h <;> first | cases h | simp
  pC {st st' f a c p} b ha hc h := by
    rw [purifyC_succ] at h
    obtain ⟨⟨st1, a'⟩, h1, h2⟩ := Res.bind_ok.mp h
    obtain ⟨⟨st2, b'⟩, h3, e⟩ := Res.map_ok.mp h2
    cases e
    have w1 : Bounded st1 ∧ a'.Fit st1.vals.size ∧ st.vals.size ≤ st1.vals.size := by
      rcases pLeft_cases r k st a with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] at h1
      · cases h1; exact ⟨b, ha, Nat.le_refl _⟩
      · exact ⟨(wf_freshCsf r ih b ha h1).1, (wf_freshCsf r ih b ha h1).2,
          (ext_freshCsf r (extK r k) h1).1⟩
    obtain ⟨b1, f1, le1⟩ := w1
    have w2 : Bounded st2 ∧ b'.Fit st2.vals.size ∧ st1.vals.size ≤ st2.vals.size := by
      rcases pRight_cases r k st1 a c a' with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] at h3
      · cases h3; exact ⟨b1, f1, Nat.le_refl _⟩
      · cases h3; exact ⟨b1, hc.mono le1, Nat.le_refl _⟩
      · exact ⟨(wf_freshCsf r ih b1 (hc.mono le1) h3).1, (wf_freshCsf r ih b1 (hc.mono le1) h3).2,
          (ext_freshCsf r (extK r k) h3).1⟩
    obtain ⟨b2, f2, le2⟩ := w2
    exact ⟨b2, fit_mkComm r _ f (f1.mono le2) f2⟩
  comm {st st' f a c rt} b ha hc hr h := by
    cases rt with
    | comm g c0 c1 =>
      rw [commCsf_comm] at h
      obtain ⟨h0, h1⟩ := Dag.fit_comm.mp hr
      split at h
      · cases h
      · have body : ∀ {l0 l1 r0 r1 : Dag s}, l0.Fit st.vals.size → l1.Fit st.vals.size →
            r0.Fit st.vals.size → r1.Fit st.vals.size →
            commBody r k st f l0 l1 r0 r1 = .ok st' → Bounded st' := by
          intro l0 l1 r0 r1 f0 f1 g0 g1 h
          rcases commBody_cases r k st f l0 l1 r0 r1 with
            ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ | e <;> rw [e] at h
          · exact ih.csf b f1 g1 h
          · exact ih.csf b f0 g1 h
          · exact ih.csf b f0 g0 h
          · obtain ⟨st1, h1, h2⟩ := Res.bind_ok.mp h
            have le := ((extK r k).csf h1).1
            exact ih.csf (ih.csf b f0 g0 h1) (f1.mono le) (g1.mono le) h2
          · cases h
            exact b.push (Dag.fit_comm.mpr ⟨f0, f1⟩) (Dag.fit_comm.mpr ⟨g0, g1⟩) (shaped_comm f _ _ _ _)
        split at h
        · exact body h0 h1 ha hc h
        · exact body ha hc h0 h1 h
    | var y =>
      rw [commCsf_var] at h
      split at h
      · next val hval => exact ih.comm b ha hc (b.vals _ _ hval) h
      · obtain ⟨⟨st1, p⟩, h1, h2⟩ := Res.bind_ok.mp h
        cases h2
        obtain ⟨b1, f1⟩ := ih.pC b ha hc h1
        exact b1.bind _ fun d e => by cases e; exact f1
    | atom | free | ac => rw [commCsf_other] at h <;> first | cases h | simp

theorem wfK : ∀ k, WfK r k
  | 0 => wfK_zero r
  | k + 1 => wfK_succ r (wfK k)


/-! ### Soundness -/

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem var_val_equiv {st : St s} {ρ : Nat → Term s} (m : Models st ρ) {y : Nat} {val : Dag s}
    (h : st.value (st.lastVar y) = some val) : EquivB (ρ y) (Dag.eval ρ val) :=
  (models_lastVar m y).trans (m.binds _ _ h)

structure SoundK (k : Nat) : Prop where
  csf : ∀ {st st' l rt ρ}, Bounded st → l.Fit st.vals.size → rt.Fit st.vals.size →
    csf r k st l rt = .ok st' → Models st' ρ → Models st ρ ∧ EquivB (Dag.eval ρ l) (Dag.eval ρ rt)
  csf2 : ∀ {st st' l rt ρ}, Bounded st → l.Fit st.vals.size → rt.Fit st.vals.size →
    csf2 r k st l rt = .ok st' → Models st' ρ → Models st ρ ∧ EquivB (Dag.eval ρ l) (Dag.eval ρ rt)
  var : ∀ {st st' x rt ρ}, Bounded st → x < st.vals.size → rt.Fit st.vals.size →
    varCsf r k st x rt = .ok st' → Models st' ρ → Models st ρ ∧ EquivB (ρ x) (Dag.eval ρ rt)
  safe : ∀ {st st' o n ρ}, Bounded st → o < st.vals.size → n < st.vals.size →
    safeRepl r k st o n = .ok st' → Models st' ρ → ModelsExcept st ρ o ∧ EquivB (ρ o) (ρ n)
  const : ∀ {st st' c rt ρ}, Bounded st → c.Fit st.vals.size → rt.Fit st.vals.size →
    constCsf r k st c rt = .ok st' → Models st' ρ → Models st ρ ∧ EquivB (Dag.eval ρ c) (Dag.eval ρ rt)
  free : ∀ {st st' f args rt ρ}, Bounded st → (Dag.free f args).Fit st.vals.size → rt.Fit st.vals.size →
    freeCsf r k st f args rt = .ok st' → Models st' ρ →
    Models st ρ ∧ EquivB (Dag.eval ρ (.free f args)) (Dag.eval ρ rt)
  list : ∀ {st st' as bs ρ}, Bounded st → (∀ a ∈ as, a.Fit st.vals.size) → (∀ b ∈ bs, b.Fit st.vals.size) →
    csfList r k st as bs = .ok st' → Models st' ρ →
    Models st ρ ∧ Pw (fun a b => EquivB (Dag.eval ρ a) (Dag.eval ρ b)) as bs
  pArgs : ∀ {st st' args rep ps ρ}, Bounded st → (∀ a ∈ args, a.Fit st.vals.size) →
    purifyArgs r k st args rep = .ok (st', ps) → Models st' ρ →
    Models st ρ ∧ Pw (fun p a => EquivB (Dag.eval ρ p) (Dag.eval ρ a)) ps args
  ac : ∀ {st st' f args rt ρ}, Bounded st → (Dag.ac f args).Fit st.vals.size → rt.Fit st.vals.size →
    acCsf r k st f args rt = .ok st' → Models st' ρ →
    Models st ρ ∧ EquivB (Dag.eval ρ (.ac f args)) (Dag.eval ρ rt)
  pC : ∀ {st st' f a b p ρ}, Bounded st → a.Fit st.vals.size → b.Fit st.vals.size →
    purifyC r k st f a b = .ok (st', p) → Models st' ρ →
    Models st ρ ∧ EquivB (Dag.eval ρ p) (Dag.eval ρ (.comm f a b))
  comm : ∀ {st st' f a b rt ρ}, Bounded st → a.Fit st.vals.size → b.Fit st.vals.size →
    rt.Fit st.vals.size → commCsf r k st f a b rt = .ok st' → Models st' ρ →
    Models st ρ ∧ EquivB (Dag.eval ρ (.comm f a b)) (Dag.eval ρ rt)

theorem soundK_zero : SoundK r 0 where
  csf _ _ _ h := by rw [csf.eq_def] at h; cases h
  csf2 _ _ _ h := by rw [csf2.eq_def] at h; cases h
  var _ _ _ h := by rw [varCsf.eq_def] at h; cases h
  safe _ _ _ h := by rw [safeRepl.eq_def] at h; cases h
  const _ _ _ h := by rw [constCsf.eq_def] at h; cases h
  free _ _ _ h := by rw [freeCsf.eq_def] at h; cases h
  list _ _ _ h := by rw [csfList.eq_def] at h; cases h
  pArgs _ _ h := by rw [purifyArgs.eq_def] at h; cases h
  ac _ _ _ h := by rw [acCsf.eq_def] at h; cases h
  pC _ _ _ h := by rw [purifyC.eq_def] at h; cases h
  comm _ _ _ _ h := by rw [commCsf.eq_def] at h; cases h

theorem sound_freshCsf {k : Nat} (ih : SoundK r k) {st st' : St s} {a a' : Dag s} {ρ : Nat → Term s}
    (b : Bounded st) (ha : a.Fit st.vals.size) (h : freshCsf r k st a = .ok (st', a')) (m : Models st' ρ) :
    Models st ρ ∧ EquivB (Dag.eval ρ a') (Dag.eval ρ a) := by
  obtain ⟨st1, h1, e⟩ := Res.map_ok.mp h
  cases e
  obtain ⟨m1, e1⟩ := ih.csf b.fresh (ha.mono (by rw [St.size_fresh]; omega))
    (Dag.fit_var.mpr (by rw [St.size_fresh]; omega)) h1 m
  exact ⟨models_fresh.mp m1, e1.symm⟩

theorem sound_pHead {k : Nat} (ih : SoundK r k) {st st1 : St s} {a a' : Dag s} {rep : Nat}
    {ρ : Nat → Term s} (b : Bounded st) (ha : a.Fit st.vals.size) (h1 : pHead r k st a rep = .ok (st1, a'))
    (m : Models st1 ρ) : Models st ρ ∧ EquivB (Dag.eval ρ a') (Dag.eval ρ a) := by
  cases a with
  | var y =>
    rw [pHead_var] at h1
    split at h1
    · cases h1
    · cases h1; exact ⟨m, .refl _⟩
  | atom c => cases h1; exact ⟨m, .refl _⟩
  | free g bs =>
    rw [pHead_free] at h1
    split at h1
    · cases h1; exact ⟨m, .refl _⟩
    · obtain ⟨⟨st3, ps3⟩, h4, e⟩ := Res.map_ok.mp h1
      cases e
      obtain ⟨m3, pw⟩ := ih.pArgs b (Dag.fit_free.mp ha).2 h4 m
      exact ⟨m3, Dag.eval_free_congr pw⟩
  | ac g bs => exact sound_freshCsf r ih b ha h1 m
  | comm g c d => exact sound_freshCsf r ih b ha h1 m

theorem soundK_succ {k : Nat} (ih : SoundK r k) : SoundK r (k + 1) where
  csf {st st' l rt ρ} b hl hr h m := by
    rw [csf_succ] at h
    split at h
    · exact ih.csf2 b hl hr h m
    · split at h
      · obtain ⟨m1, e⟩ := ih.csf2 b hr hl h m
        exact ⟨m1, e.symm⟩
      · next g1 g2 =>
        split at h
        · next hs =>
          cases h
          have gl : l.ground = true := by simpa using g1
          have gr : rt.ground = true := by simpa using g2
          exact ⟨m, (Dag.same_iff gl gr ρ).mp hs⟩
        · cases h
  csf2 {st st' l rt ρ} b hl hr h m := by
    cases l with
    | var x =>
      rw [csf2_var] at h
      rw [Dag.eval_var]
      exact ih.var b (Dag.fit_var.mp hl) hr h m
    | atom a => rw [csf2_atom] at h; exact ih.const b hl hr h m
    | free f args => rw [csf2_free] at h; exact ih.free b hl hr h m
    | ac f args => rw [csf2_ac] at h; exact ih.ac b hl hr h m
    | comm f a c =>
      rw [csf2_comm] at h
      exact ih.comm b (Dag.fit_comm.mp hl).1 (Dag.fit_comm.mp hl).2 hr h m
  var {st st' x rt ρ} b hx hr h m := by
    by_cases hv : ∃ y, rt = .var y
    · obtain ⟨y, rfl⟩ := hv
      have hy := Dag.fit_var.mp hr
      rw [Dag.eval_var]
      rcases varCsf_var_cases r k st x y with ⟨he, e⟩ | ⟨lv, rv, hlr, hne, e⟩
      · rw [e] at h; cases h
        exact ⟨m, (models_lastVar m x).trans (he ▸ (models_lastVar m y).symm)⟩
      · rw [e] at h
        have hlv : lv < st.vals.size ∧ rv < st.vals.size := by
          rcases hlr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨lastVar_lt b hx, lastVar_lt b hy⟩
          · exact ⟨lastVar_lt b hy, lastVar_lt b hx⟩
        have body : Models st ρ ∧ EquivB (ρ lv) (ρ rv) := by
          rcases varBody_cases r k st lv rv with ⟨hn, e⟩ | ⟨_, _, hn, e⟩ | ⟨lt, rt', hlt, hrt, e⟩ <;>
            rw [e] at h
          · obtain ⟨m1, e1⟩ := ih.safe b hlv.1 hlv.2 h m
            exact ⟨m1.models_none hn, e1⟩
          · obtain ⟨m1, e1⟩ := ih.safe b hlv.2 hlv.1 h m
            exact ⟨m1.models_none hn, e1.symm⟩
          · obtain ⟨st1, h1, h2⟩ := Res.bind_ok.mp h
            have le := ((extK r k).safe h1).1
            obtain ⟨m1, e1⟩ := ih.csf ((wfK r k).safe b hlv.1 hlv.2 h1) ((b.vals _ _ hlt).mono le)
              ((b.vals _ _ hrt).mono le) h2 m
            obtain ⟨m2, e2⟩ := ih.safe b hlv.1 hlv.2 h1 m1
            refine ⟨m2.models fun d hd => ?_, e2⟩
            rw [hlt] at hd; cases hd
            exact e2.trans ((m2.binds rv rt' (Ne.symm hne) hrt).trans e1.symm)
        refine ⟨body.1, ?_⟩
        rcases hlr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact (models_lastVar body.1 x).trans (body.2.trans (models_lastVar body.1 y).symm)
        · exact (models_lastVar body.1 x).trans (body.2.symm.trans (models_lastVar body.1 y).symm)
    · rw [varCsf_nonvar r k st x rt fun y e => hv ⟨y, e⟩] at h
      obtain ⟨m1, e⟩ := ih.csf2 b hr (Dag.fit_var.mpr hx) h m
      rw [Dag.eval_var] at e
      exact ⟨m1, e.symm⟩
  safe {st st' o n ρ} b ho hn h m := by
    rw [safeRepl_succ] at h
    have b1 : Bounded (st.bind o (some (.var n))) :=
      b.bind o fun d e => by cases e; exact Dag.fit_var.mpr hn
    have m1 : Models (st.bind o (some (.var n))) ρ → ModelsExcept st ρ o ∧ EquivB (ρ o) (ρ n) :=
      fun m1 => ⟨models_bind_except m1, by simpa [Dag.eval_var] using models_bind_some m1 ho⟩
    split at h
    · cases h; exact m1 m
    · next nb hnb =>
      split at h
      · cases h; exact m1 m
      · split at h
        · obtain ⟨m2, e2⟩ := ih.csf2 (b1.bind n fun _ e => by cases e)
            (by rw [St.size_bind]; exact b1.vals _ _ hnb)
            (by rw [St.size_bind, St.size_bind]; exact Dag.fit_var.mpr hn) h m
          rw [Dag.eval_var] at e2
          exact m1 ((models_bind_except m2).models fun d hd => by
            rw [hnb] at hd; cases hd; exact e2.symm)
        · cases h; exact m1 m
  const {st st' c rt ρ} b hc hr h m := by
    by_cases hv : ∃ y, rt = .var y
    · obtain ⟨y, rfl⟩ := hv
      rw [Dag.eval_var]
      rw [constCsf_var] at h
      split at h
      · next val hval =>
        obtain ⟨m1, e⟩ := ih.csf b hc (b.vals _ _ hval) h m
        exact ⟨m1, e.trans (var_val_equiv m1 hval).symm⟩
      · next hval =>
        cases h
        have m1 := (models_bind_except m).models_none hval
        exact ⟨m1, ((models_lastVar m1 y).trans
          (models_bind_some m (lastVar_lt b (Dag.fit_var.mp hr)))).symm⟩
    · rw [constCsf_nonvar r k st c rt fun y e => hv ⟨y, e⟩] at h; cases h
  free {st st' f args rt ρ} b hl hr h m := by
    cases rt with
    | free g bs =>
      rw [freeCsf_free] at h
      split at h
      · next e =>
        subst e
        obtain ⟨m1, pw⟩ := ih.list b (Dag.fit_free.mp hl).2 (Dag.fit_free.mp hr).2 h m
        exact ⟨m1, Dag.eval_free_congr pw⟩
      · cases h
    | var y =>
      rw [Dag.eval_var]
      have hrv := lastVar_lt b (Dag.fit_var.mp hr)
      rw [freeCsf_var] at h
      split at h
      · next val hval =>
        obtain ⟨m1, e⟩ := ih.csf b hl (b.vals _ _ hval) h m
        exact ⟨m1, e.trans (var_val_equiv m1 hval).symm⟩
      · next hval =>
        split at h
        · cases h
          have m1 := (models_bind_except m).models_none hval
          exact ⟨m1, ((models_lastVar m1 y).trans (models_bind_some m hrv)).symm⟩
        · obtain ⟨⟨st1, ps⟩, h1, h2⟩ := Res.bind_ok.mp h
          cases h2
          have hn1 : st1.value (st.lastVar y) = none := by
            rw [(frameK r k).pArgs h1 _ hrv, hval]
          have m1 := (models_bind_except m).models_none hn1
          obtain ⟨m2, pw⟩ := ih.pArgs b (Dag.fit_free.mp hl).2 h1 m1
          have e1 := models_bind_some m (Nat.lt_of_lt_of_le hrv ((extK r k).pArgs h1).1)
          exact ⟨m2, ((Dag.eval_free_congr pw).symm.trans e1.symm).trans
            (models_lastVar m2 y).symm⟩
    | atom | ac | comm => rw [freeCsf_other] at h <;> first | cases h | simp
  list {st st' as bs ρ} b ha hb h m := by
    cases as with
    | nil => cases bs with
      | nil => rw [csfList_nil] at h; cases h; exact ⟨m, .nil⟩
      | cons => rw [csfList_nil_cons] at h; cases h
    | cons a as => cases bs with
      | nil => rw [csfList_cons_nil] at h; cases h
      | cons c bs =>
        rw [csfList_cons] at h
        obtain ⟨st1, h1, h2⟩ := Res.bind_ok.mp h
        have le := ((extK r k).csf h1).1
        have b1 := (wfK r k).csf b (ha a List.mem_cons_self) (hb c List.mem_cons_self) h1
        obtain ⟨m1, pw⟩ := ih.list b1 (fun x hx => (ha x (List.mem_cons_of_mem _ hx)).mono le)
          (fun x hx => (hb x (List.mem_cons_of_mem _ hx)).mono le) h2 m
        obtain ⟨m2, e⟩ := ih.csf b (ha a List.mem_cons_self) (hb c List.mem_cons_self) h1 m1
        exact ⟨m2, .cons e pw⟩
  pArgs {st st' args rep ps ρ} b ha h m := by
    cases args with
    | nil => rw [purifyArgs_nil] at h; cases h; exact ⟨m, .nil⟩
    | cons a as =>
      rw [purifyArgs_cons] at h
      obtain ⟨⟨st1, a'⟩, h1, h2⟩ := Res.bind_ok.mp h
      obtain ⟨⟨st2, ps'⟩, h3, e⟩ := Res.map_ok.mp h2
      cases e
      obtain ⟨b1, _⟩ := wf_pHead r (wfK r k) b (ha a List.mem_cons_self) h1
      have le := (ext_pHead r (extK r k) h1).1
      obtain ⟨m1, pw⟩ := ih.pArgs b1 (fun x hx => (ha x (List.mem_cons_of_mem _ hx)).mono le) h3 m
      obtain ⟨m2, e⟩ := sound_pHead r ih b (ha a List.mem_cons_self) h1 m1
      exact ⟨m2, .cons e pw⟩
  ac {st st' f args rt ρ} b hl hr h m := by
    cases rt with
    | ac g bs =>
      rw [acCsf_ac] at h
      split at h
      · cases h; exact models_push.mp m
      · cases h
    | var y =>
      rw [Dag.eval_var]
      rw [acCsf_var] at h
      split at h
      · next val hval =>
        obtain ⟨m1, e⟩ := ih.csf2 b hl (b.vals _ _ hval) h m
        exact ⟨m1, e.trans (var_val_equiv m1 hval).symm⟩
      · cases h; rw [← Dag.eval_var ρ y]; exact models_push.mp m
    | atom | free | comm => rw [acCsf_other] at h <;> first | cases h | simp
  pC {st st' f a c p ρ} b ha hc h m := by
    rw [purifyC_succ] at h
    obtain ⟨⟨st1, a'⟩, h1, h2⟩ := Res.bind_ok.mp h
    obtain ⟨⟨st2, b'⟩, h3, e⟩ := Res.map_ok.mp h2
    cases e
    have w1 : Bounded st1 ∧ st.vals.size ≤ st1.vals.size := by
      rcases pLeft_cases r k st a with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] at h1
      · cases h1; exact ⟨b, Nat.le_refl _⟩
      · exact ⟨(wf_freshCsf r (wfK r k) b ha h1).1, (ext_freshCsf r (extK r k) h1).1⟩
    obtain ⟨b1, le1⟩ := w1
    have s2 : Models st1 ρ ∧ ((c = a ∧ b' = a') ∨ EquivB (Dag.eval ρ b') (Dag.eval ρ c)) := by
      rcases pRight_cases r k st1 a c a' with ⟨hca, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] at h3
      · cases h3; exact ⟨m, .inl ⟨hca, rfl⟩⟩
      · cases h3; exact ⟨m, .inr (.refl _)⟩
      · obtain ⟨m1, e1⟩ := sound_freshCsf r ih b1 (hc.mono le1) h3 m
        exact ⟨m1, .inr e1⟩
    obtain ⟨m1, e2⟩ := s2
    have s1 : Models st ρ ∧ EquivB (Dag.eval ρ a') (Dag.eval ρ a) := by
      rcases pLeft_cases r k st a with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] at h1
      · cases h1; exact ⟨m1, .refl _⟩
      · exact sound_freshCsf r ih b ha h1 m1
    obtain ⟨m0, e1⟩ := s1
    refine ⟨m0, (Dag.eval_mkComm r _ ρ f a' b').trans ?_⟩
    rw [Dag.eval_comm, Dag.eval_comm]
    refine .comm_congr f e1 ?_
    rcases e2 with ⟨rfl, rfl⟩ | e2
    · exact e1
    · exact e2
  comm {st st' f a c rt ρ} b ha hc hr h m := by
    cases rt with
    | comm g c0 c1 =>
      rw [commCsf_comm] at h
      obtain ⟨h0, h1⟩ := Dag.fit_comm.mp hr
      split at h
      · cases h
      · next hfg =>
        have hfg : f = g := Classical.byContradiction hfg
        subst hfg
        have body : ∀ {l0 l1 r0 r1 : Dag s}, l0.Fit st.vals.size → l1.Fit st.vals.size →
            r0.Fit st.vals.size → r1.Fit st.vals.size →
            commBody r k st f l0 l1 r0 r1 = .ok st' →
            Models st ρ ∧ EquivB (Dag.eval ρ (.comm f l0 l1)) (Dag.eval ρ (.comm f r0 r1)) := by
          intro l0 l1 r0 r1 f0 f1 g0 g1 h
          simp only [Dag.eval_comm]
          rcases commBody_cases r k st f l0 l1 r0 r1 with
            ⟨he, e⟩ | ⟨he, e⟩ | ⟨he, e⟩ | ⟨_, e⟩ | e <;> rw [e] at h
          · obtain ⟨m1, e1⟩ := ih.csf b f1 g1 h m
            subst he
            exact ⟨m1, .comm_congr f (.refl _) e1⟩
          · obtain ⟨m1, e1⟩ := ih.csf b f0 g1 h m
            subst he
            exact ⟨m1, (EquivB.comm_swap f _ _).trans (.comm_congr f (.refl _) e1)⟩
          · obtain ⟨m1, e1⟩ := ih.csf b f0 g0 h m
            subst he
            exact ⟨m1, .comm_congr f e1 (.refl _)⟩
          · obtain ⟨st1, h1, h2⟩ := Res.bind_ok.mp h
            have le := ((extK r k).csf h1).1
            obtain ⟨m1, e1⟩ := ih.csf ((wfK r k).csf b f0 g0 h1) (f1.mono le) (g1.mono le) h2 m
            obtain ⟨m2, e2⟩ := ih.csf b f0 g0 h1 m1
            exact ⟨m2, .comm_congr f e2 e1⟩
          · cases h
            obtain ⟨m1, e1⟩ := models_push.mp m
            simp only [Dag.eval_comm] at e1
            exact ⟨m1, e1⟩
        split at h
        · obtain ⟨m1, e1⟩ := body h0 h1 ha hc h
          exact ⟨m1, e1.symm⟩
        · exact body ha hc h0 h1 h
    | var y =>
      rw [Dag.eval_var]
      have hrv := lastVar_lt b (Dag.fit_var.mp hr)
      rw [commCsf_var] at h
      split at h
      · next val hval =>
        obtain ⟨m1, e⟩ := ih.comm b ha hc (b.vals _ _ hval) h m
        exact ⟨m1, e.trans (var_val_equiv m1 hval).symm⟩
      · next hval =>
        obtain ⟨⟨st1, p⟩, h1, h2⟩ := Res.bind_ok.mp h
        cases h2
        have hn1 : st1.value (st.lastVar y) = none := by
          rw [(frameK r k).pC h1 _ hrv, hval]
        have m1 := (models_bind_except m).models_none hn1
        obtain ⟨m2, e⟩ := ih.pC b ha hc h1 m1
        have e1 := models_bind_some m (Nat.lt_of_lt_of_le hrv ((extK r k).pC h1).1)
        exact ⟨m2, (e.symm.trans e1.symm).trans (models_lastVar m2 y).symm⟩
    | atom | free | ac => rw [commCsf_other] at h <;> first | cases h | simp

theorem soundK : ∀ k, SoundK r k
  | 0 => soundK_zero r
  | k + 1 => soundK_succ r (soundK k)


/-! ### Completeness -/

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem comm_cancel {f : s.CSym} {a b d : Term s} (h : EquivB (.comm f a b) (.comm f a d)) : EquivB b d := by
  rcases (Commutative.equiv_iff f a b a d).mp h with ⟨_, e⟩ | ⟨e1, e2⟩
  · exact e
  · exact e2.trans e1

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem no_equiv {a b : Term s} (e : EquivB a b) (h : hd a ≠ hd b) : False := h (hd_eq e)

/-- What completeness promises of a successful step from `st` under `ρ`. -/
def PS (st : St s) (ρ : Nat → Term s) (st' : St s) : Prop := ∃ ρ', Agree st.vals.size ρ ρ' ∧ Models st' ρ'

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem PS.lift {st st1 : St s} {ρ ρ1 : Nat → Term s} {x : Res (St s)} (a : Agree st.vals.size ρ ρ1)
    (le : st.vals.size ≤ st1.vals.size) (h : Res.Prom (PS st1 ρ1) x) : Res.Prom (PS st ρ) x :=
  h.mono fun _ _ ⟨ρ2, a2, m2⟩ => ⟨ρ2, a.trans a2 le, m2⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem Pw.imp {α β : Type} {R S : α → β → Prop} {as : List α} {bs : List β} (h : Pw R as bs)
    (k : ∀ a ∈ as, ∀ b ∈ bs, R a b → S a b) : Pw S as bs := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih =>
    exact .cons (k _ List.mem_cons_self _ List.mem_cons_self hab)
      (ih fun a ha b hb => k a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
/-- The valuation extended at the fresh slot of `st` by `t`. -/
theorem fresh_models {st : St s} {ρ : Nat → Term s} (b : Bounded st) (m : Models st ρ) (t : Term s) :
    Models st.fresh.1 (fun i => if i = st.vals.size then t else ρ i) ∧
    Agree st.vals.size ρ (fun i => if i = st.vals.size then t else ρ i) := by
  have a : Agree st.vals.size ρ (fun i => if i = st.vals.size then t else ρ i) :=
    fun i hi => by simp [Nat.ne_of_lt hi]
  exact ⟨models_fresh.mpr (m.agree b a), a⟩

structure CompK (k : Nat) : Prop where
  csf : ∀ {st l rt ρ}, Bounded st → l.Fit st.vals.size → rt.Fit st.vals.size → Models st ρ →
    EquivB (Dag.eval ρ l) (Dag.eval ρ rt) → Res.Prom (PS st ρ) (csf r k st l rt)
  csf2 : ∀ {st l rt ρ}, Bounded st → l.Fit st.vals.size → rt.Fit st.vals.size → Models st ρ →
    (∀ a, l = .atom a → ∃ y, rt = .var y) →
    EquivB (Dag.eval ρ l) (Dag.eval ρ rt) → Res.Prom (PS st ρ) (csf2 r k st l rt)
  var : ∀ {st x rt ρ}, Bounded st → x < st.vals.size → rt.Fit st.vals.size → Models st ρ →
    EquivB (ρ x) (Dag.eval ρ rt) → Res.Prom (PS st ρ) (varCsf r k st x rt)
  safe : ∀ {st o n ρ}, Bounded st → o < st.vals.size → n < st.vals.size → ModelsExcept st ρ o →
    EquivB (ρ o) (ρ n) → Res.Prom (PS st ρ) (safeRepl r k st o n)
  const : ∀ {st c y ρ}, Bounded st → c.Fit st.vals.size → y < st.vals.size → Models st ρ →
    EquivB (Dag.eval ρ c) (ρ y) → Res.Prom (PS st ρ) (constCsf r k st c (.var y))
  free : ∀ {st f args rt ρ}, Bounded st → (Dag.free f args).Fit st.vals.size → rt.Fit st.vals.size →
    Models st ρ → EquivB (Dag.eval ρ (.free f args)) (Dag.eval ρ rt) →
    Res.Prom (PS st ρ) (freeCsf r k st f args rt)
  list : ∀ {st as bs ρ}, Bounded st → (∀ a ∈ as, a.Fit st.vals.size) → (∀ b ∈ bs, b.Fit st.vals.size) →
    Models st ρ → Pw (fun a b => EquivB (Dag.eval ρ a) (Dag.eval ρ b)) as bs →
    Res.Prom (PS st ρ) (csfList r k st as bs)
  pArgs : ∀ {st args rep ρ}, Bounded st → (∀ a ∈ args, a.Fit st.vals.size) → rep < st.vals.size →
    Models st ρ → (∀ a ∈ args, tsize (Dag.eval ρ a) < tsize (ρ rep)) →
    Res.Prom (fun q : St s × List (Dag s) => ∃ ρ', Agree st.vals.size ρ ρ' ∧ Models q.1 ρ' ∧
      Pw (fun p a => EquivB (Dag.eval ρ' p) (Dag.eval ρ a)) q.2 args) (purifyArgs r k st args rep)
  ac : ∀ {st f args rt ρ}, Bounded st → (Dag.ac f args).Fit st.vals.size → rt.Fit st.vals.size →
    Models st ρ → EquivB (Dag.eval ρ (.ac f args)) (Dag.eval ρ rt) →
    Res.Prom (PS st ρ) (acCsf r k st f args rt)
  pC : ∀ {st f a b ρ}, Bounded st → a.Fit st.vals.size → b.Fit st.vals.size → Models st ρ →
    Res.Prom (fun q : St s × Dag s => ∃ ρ', Agree st.vals.size ρ ρ' ∧ Models q.1 ρ' ∧
      EquivB (Dag.eval ρ' q.2) (Dag.eval ρ (.comm f a b))) (purifyC r k st f a b)
  comm : ∀ {st f a b rt ρ}, Bounded st → a.Fit st.vals.size → b.Fit st.vals.size →
    rt.Fit st.vals.size → Models st ρ → EquivB (Dag.eval ρ (.comm f a b)) (Dag.eval ρ rt) →
    Res.Prom (PS st ρ) (commCsf r k st f a b rt)

theorem compK_zero : CompK r 0 where
  csf _ _ _ _ _ := by rw [csf.eq_def]; trivial
  csf2 _ _ _ _ _ _ := by rw [csf2.eq_def]; trivial
  var _ _ _ _ _ := by rw [varCsf.eq_def]; trivial
  safe _ _ _ _ _ := by rw [safeRepl.eq_def]; trivial
  const _ _ _ _ _ := by rw [constCsf.eq_def]; trivial
  free _ _ _ _ _ := by rw [freeCsf.eq_def]; trivial
  list _ _ _ _ _ := by rw [csfList.eq_def]; trivial
  pArgs _ _ _ _ _ := by rw [purifyArgs.eq_def]; trivial
  ac _ _ _ _ _ := by rw [acCsf.eq_def]; trivial
  pC _ _ _ _ := by rw [purifyC.eq_def]; trivial
  comm _ _ _ _ _ _ := by rw [commCsf.eq_def]; trivial

theorem comp_freshCsf {k : Nat} (ih : CompK r k) {st : St s} {a : Dag s} {ρ : Nat → Term s}
    (b : Bounded st) (ha : a.Fit st.vals.size) (m : Models st ρ) :
    Res.Prom (fun q : St s × Dag s => ∃ ρ', Agree st.vals.size ρ ρ' ∧ Models q.1 ρ' ∧
      EquivB (Dag.eval ρ' q.2) (Dag.eval ρ a)) (freshCsf r k st a) := by
  obtain ⟨m1, a1⟩ := fresh_models b m (Dag.eval ρ a)
  unfold freshCsf
  have hc := ih.csf (st := st.fresh.1) (l := a) (rt := .var st.vals.size)
    (ρ := fun i => if i = st.vals.size then Dag.eval ρ a else ρ i) b.fresh
    (ha.mono (by rw [St.size_fresh]; omega)) (Dag.fit_var.mpr (by rw [St.size_fresh]; omega)) m1
    (by rw [Dag.eval_agree ha.2 a1, Dag.eval_var]; simp only; exact .refl _)
  refine hc.map fun st2 _ ⟨ρ2, a2, m2⟩ => ⟨ρ2, a1.trans a2 (by rw [St.size_fresh]; omega), m2, ?_⟩
  show EquivB (Dag.eval ρ2 (.var st.vals.size)) (Dag.eval ρ a)
  rw [Dag.eval_var, a2 _ (by rw [St.size_fresh]; omega)]
  simp only
  exact .refl _

theorem comp_pHead {k : Nat} (ih : CompK r k) {st : St s} {a : Dag s} {rep : Nat} {ρ : Nat → Term s}
    (b : Bounded st) (ha : a.Fit st.vals.size) (hrep : rep < st.vals.size) (m : Models st ρ)
    (hs : tsize (Dag.eval ρ a) < tsize (ρ rep)) :
    Res.Prom (fun q : St s × Dag s => ∃ ρ', Agree st.vals.size ρ ρ' ∧ Models q.1 ρ' ∧
      EquivB (Dag.eval ρ' q.2) (Dag.eval ρ a)) (pHead r k st a rep) := by
  cases a with
  | var y =>
    rw [pHead_var]
    split
    · next he =>
      have := tsize_equiv (models_lastVar m y)
      rw [he, ← Dag.eval_var ρ y] at this
      omega
    · exact ⟨ρ, Agree.refl _ _, m, .refl _⟩
  | atom c => exact ⟨ρ, Agree.refl _ _, m, .refl _⟩
  | free g bs =>
    rw [pHead_free]
    split
    · exact ⟨ρ, Agree.refl _ _, m, .refl _⟩
    · obtain ⟨hl, hf⟩ := Dag.fit_free.mp ha
      exact (ih.pArgs b hf hrep m fun x hx => Nat.lt_trans (Dag.tsize_arg hl hx) hs).map
        fun _ _ ⟨ρ3, a3, m3, pw⟩ => ⟨ρ3, a3, m3, Dag.eval_free_congr pw⟩
  | ac g bs => exact comp_freshCsf r ih b ha m
  | comm g c d => exact comp_freshCsf r ih b ha m

theorem comp_commBody {k : Nat} (ih : CompK r k) {st : St s} {f : s.CSym} {l0 l1 r0 r1 : Dag s}
    {ρ : Nat → Term s} (b : Bounded st) (f0 : l0.Fit st.vals.size) (f1 : l1.Fit st.vals.size)
    (g0 : r0.Fit st.vals.size) (g1 : r1.Fit st.vals.size) (m : Models st ρ)
    (e : EquivB (.comm f (Dag.eval ρ l0) (Dag.eval ρ l1)) (.comm f (Dag.eval ρ r0) (Dag.eval ρ r1))) :
    Res.Prom (PS st ρ) (commBody r k st f l0 l1 r0 r1) := by
  rcases commBody_cases r k st f l0 l1 r0 r1 with
    ⟨he, e'⟩ | ⟨he, e'⟩ | ⟨he, e'⟩ | ⟨hc, e'⟩ | e' <;> rw [e']
  · subst he
    exact ih.csf b f1 g1 m (comm_cancel e)
  · subst he
    exact ih.csf b f0 g1 m (comm_cancel ((EquivB.comm_swap f _ _).trans e))
  · subst he
    exact ih.csf b f0 g0 m (comm_cancel ((EquivB.comm_swap f _ _).trans (e.trans (.comm_swap f _ _))))
  · have both : EquivB (Dag.eval ρ l0) (Dag.eval ρ r0) ∧ EquivB (Dag.eval ρ l1) (Dag.eval ρ r1) := by
      rcases (Commutative.equiv_iff f _ _ _ _).mp e with h | ⟨e1, e2⟩
      · exact h
      · rcases hc with rfl | rfl
        · exact ⟨e2, e1⟩
        · exact ⟨e1, e2⟩
    refine (ih.csf b f0 g0 m both.1).bind fun st1 h1 ⟨ρ1, a1, m1⟩ => ?_
    have le := ((extK r k).csf h1).1
    refine PS.lift a1 le (ih.csf ((wfK r k).csf b f0 g0 h1) (f1.mono le) (g1.mono le) m1 ?_)
    rw [Dag.eval_agree f1.2 a1, Dag.eval_agree g1.2 a1]
    exact both.2
  · exact ⟨ρ, Agree.refl _ _, models_push.mpr ⟨m, by simpa only [Dag.eval_comm] using e⟩⟩

theorem compK_succ {k : Nat} (ih : CompK r k) : CompK r (k + 1) where
  csf {st l rt ρ} b hl hr m e := by
    rw [csf_succ]
    have natom : ∀ d : Dag s, (!d.ground) = true → ∀ a, d ≠ .atom a := by
      intro d hd a he
      subst he
      simp [Dag.ground, Dag.vars] at hd
    split
    · next g1 => exact ih.csf2 b hl hr m (fun a he => absurd he (natom l g1 a)) e
    · split
      · next g2 => exact ih.csf2 b hr hl m (fun a he => absurd he (natom rt g2 a)) e.symm
      · next g1 g2 =>
        have gl : l.ground = true := by simpa using g1
        have gr : rt.ground = true := by simpa using g2
        have hs := (Dag.same_iff gl gr ρ).mpr e
        rw [ite_eq_left_of_eq_true _ _ (eq_true hs)]
        exact ⟨ρ, Agree.refl _ _, m⟩
  csf2 {st l rt ρ} b hl hr m hat e := by
    cases l with
    | var x =>
      rw [csf2_var]
      rw [Dag.eval_var] at e
      exact ih.var b (Dag.fit_var.mp hl) hr m e
    | atom a =>
      obtain ⟨y, rfl⟩ := hat a rfl
      rw [csf2_atom]
      rw [Dag.eval_var] at e
      exact ih.const b hl (Dag.fit_var.mp hr) m e
    | free f args => rw [csf2_free]; exact ih.free b hl hr m e
    | ac f args => rw [csf2_ac]; exact ih.ac b hl hr m e
    | comm f a c =>
      rw [csf2_comm]
      exact ih.comm b (Dag.fit_comm.mp hl).1 (Dag.fit_comm.mp hl).2 hr m e
  var {st x rt ρ} b hx hr m e := by
    by_cases hv : ∃ y, rt = .var y
    · obtain ⟨y, rfl⟩ := hv
      have hy := Dag.fit_var.mp hr
      rw [Dag.eval_var] at e
      rcases varCsf_var_cases r k st x y with ⟨_, e'⟩ | ⟨lv, rv, hlr, hne, e'⟩
      · rw [e']; exact ⟨ρ, Agree.refl _ _, m⟩
      · rw [e']
        have hlv : lv < st.vals.size ∧ rv < st.vals.size := by
          rcases hlr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨lastVar_lt b hx, lastVar_lt b hy⟩
          · exact ⟨lastVar_lt b hy, lastVar_lt b hx⟩
        have elr : EquivB (ρ lv) (ρ rv) := by
          rcases hlr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact (models_lastVar m x).symm.trans (e.trans (models_lastVar m y))
          · exact (models_lastVar m y).symm.trans (e.symm.trans (models_lastVar m x))
        rcases varBody_cases r k st lv rv with ⟨_, e''⟩ | ⟨_, _, _, e''⟩ | ⟨lt, rt', hlt, hrt, e''⟩ <;>
          rw [e'']
        · exact ih.safe b hlv.1 hlv.2 (m.except lv) elr
        · exact ih.safe b hlv.2 hlv.1 (m.except rv) elr.symm
        · refine (ih.safe b hlv.1 hlv.2 (m.except lv) elr).bind fun st1 h1 ⟨ρ1, a1, m1⟩ => ?_
          have le := ((extK r k).safe h1).1
          have flt := b.vals _ _ hlt
          have frt := b.vals _ _ hrt
          refine PS.lift a1 le (ih.csf ((wfK r k).safe b hlv.1 hlv.2 h1) (flt.mono le) (frt.mono le) m1 ?_)
          rw [Dag.eval_agree flt.2 a1, Dag.eval_agree frt.2 a1]
          exact (m.binds _ _ hlt).symm.trans (elr.trans (m.binds _ _ hrt))
    · rw [varCsf_nonvar r k st x rt fun y e => hv ⟨y, e⟩]
      exact ih.csf2 b hr (Dag.fit_var.mpr hx) m (fun _ _ => ⟨x, rfl⟩) (by rw [Dag.eval_var]; exact e.symm)
  safe {st o n ρ} b ho hn m e := by
    rw [safeRepl_succ]
    have b1 : Bounded (st.bind o (some (.var n))) :=
      b.bind o fun d e => by cases e; exact Dag.fit_var.mpr hn
    have m1 : Models (st.bind o (some (.var n))) ρ :=
      models_bind m fun d e' => by cases e'; rw [Dag.eval_var]; exact e
    have ok1 : PS st ρ (st.bind o (some (.var n))) := ⟨ρ, Agree.refl _ _, m1⟩
    split
    · exact ok1
    · next nb hnb =>
      split
      · exact ok1
      · split
        · have hsz : ((st.bind o (some (.var n))).bind n none).vals.size = st.vals.size := by
            rw [St.size_bind, St.size_bind]
          refine PS.lift (Agree.refl _ _) (Nat.le_of_eq hsz.symm) (ih.csf2 (b1.bind n fun _ e => by cases e)
            (by rw [St.size_bind]; exact b1.vals _ _ hnb)
            (by rw [hsz]; exact Dag.fit_var.mpr hn)
            (models_bind (m1.except n) fun _ e => by cases e) (fun _ _ => ⟨n, rfl⟩) ?_)
          rw [Dag.eval_var]
          exact (m1.binds _ _ hnb).symm
        · exact ok1
  const {st c y ρ} b hc hy m e := by
    rw [constCsf_var]
    split
    · next val hval => exact ih.csf b hc (b.vals _ _ hval) m (e.trans (var_val_equiv m hval))
    · exact ⟨ρ, Agree.refl _ _, models_bind (m.except _) fun d e' => by
        cases e'; exact (models_lastVar m y).symm.trans e.symm⟩
  free {st f args rt ρ} b hl hr m e := by
    obtain ⟨hlen, hfa⟩ := Dag.fit_free.mp hl
    cases rt with
    | free g bs =>
      have hfg : f = g := by
        have := hd_eq e
        rw [Dag.hd_eval_free, Dag.hd_eval_free] at this
        exact Head.free.inj this
      subst hfg
      rw [freeCsf_free, ite_eq_left_of_eq_true _ _ (eq_self f)]
      obtain ⟨hlen', hfb⟩ := Dag.fit_free.mp hr
      exact ih.list b hfa hfb m (Dag.free_args_equiv hlen hlen' e)
    | var y =>
      have hy := Dag.fit_var.mp hr
      have hrv := lastVar_lt b hy
      rw [Dag.eval_var] at e
      rw [freeCsf_var]
      split
      · next val hval => exact ih.csf b hl (b.vals _ _ hval) m (e.trans (var_val_equiv m hval))
      · split
        · exact ⟨ρ, Agree.refl _ _, models_bind (m.except _) fun d e' => by
            cases e'; exact (models_lastVar m y).symm.trans e.symm⟩
        · have erv : EquivB (ρ (st.lastVar y)) (Dag.eval ρ (.free f args)) :=
            (models_lastVar m y).symm.trans e.symm
          refine (ih.pArgs b hfa hrv m fun x hx => ?_).bind fun q _ ⟨ρ1, a1, m1, pw⟩ => ?_
          · rw [tsize_equiv erv]; exact Dag.tsize_arg hlen hx
          · refine ⟨ρ1, a1, models_bind (m1.except _) fun d e' => ?_⟩
            cases e'
            rw [a1 _ hrv]
            exact erv.trans (Dag.eval_free_congr pw).symm
    | atom c =>
      exact (no_equiv e (by rw [Dag.hd_eval_free, Dag.hd_eval_atom]; intro h; cases h)).elim
    | ac g bs =>
      exact (no_equiv e (by
        rw [Dag.hd_eval_free, Dag.hd_eval_ac _ _ (Dag.fit_ac.mp hr).1]; intro h; cases h)).elim
    | comm g c d =>
      exact (no_equiv e (by rw [Dag.hd_eval_free, Dag.hd_eval_comm]; intro h; cases h)).elim
  list {st as bs ρ} b ha hb m pw := by
    cases pw with
    | nil => rw [csfList_nil]; exact ⟨ρ, Agree.refl _ _, m⟩
    | @cons a c as bs hab pw =>
      rw [csfList_cons]
      refine (ih.csf b (ha a List.mem_cons_self) (hb c List.mem_cons_self) m hab).bind
        fun st1 h1 ⟨ρ1, a1, m1⟩ => ?_
      have le := ((extK r k).csf h1).1
      have fa : ∀ x ∈ as, x.Fit st.vals.size := fun x hx => ha x (List.mem_cons_of_mem _ hx)
      have fb : ∀ x ∈ bs, x.Fit st.vals.size := fun x hx => hb x (List.mem_cons_of_mem _ hx)
      refine PS.lift a1 le (ih.list ((wfK r k).csf b (ha a List.mem_cons_self) (hb c List.mem_cons_self) h1)
        (fun x hx => (fa x hx).mono le) (fun x hx => (fb x hx).mono le) m1 (pw.imp fun x hx y hy hxy => ?_))
      rw [Dag.eval_agree (fa x hx).2 a1, Dag.eval_agree (fb y hy).2 a1]
      exact hxy
  pArgs {st args rep ρ} b ha hrep m hs := by
    cases args with
    | nil => rw [purifyArgs_nil]; exact ⟨ρ, Agree.refl _ _, m, .nil⟩
    | cons a as =>
      rw [purifyArgs_cons]
      have fas : ∀ x ∈ as, x.Fit st.vals.size := fun x hx => ha x (List.mem_cons_of_mem _ hx)
      refine (comp_pHead r ih b (ha a List.mem_cons_self) hrep m (hs a List.mem_cons_self)).bind
        fun ⟨st1, a'⟩ h1 ⟨ρ1, a1, m1, ea⟩ => ?_
      obtain ⟨b1, fa'⟩ := wf_pHead r (wfK r k) b (ha a List.mem_cons_self) h1
      have le := (ext_pHead r (extK r k) h1).1
      refine (ih.pArgs b1 (fun x hx => (fas x hx).mono le) (Nat.lt_of_lt_of_le hrep le) m1
        fun x hx => ?_).map fun ⟨st2, ps'⟩ h3 ⟨ρ2, a2, m2, pw⟩ => ⟨ρ2, a1.trans a2 le, m2, .cons ?_ ?_⟩
      · rw [Dag.eval_agree (fas x hx).2 a1, a1 _ hrep]
        exact hs x (List.mem_cons_of_mem _ hx)
      · rw [Dag.eval_agree fa'.2 a2]; exact ea
      · exact pw.imp fun p _ x hx hpx => by rw [Dag.eval_agree (fas x hx).2 a1] at hpx; exact hpx
  ac {st f args rt ρ} b hl hr m e := by
    have h2 := (Dag.fit_ac.mp hl).1
    cases rt with
    | ac g bs =>
      have hfg : f = g := by
        have := hd_eq e
        rw [Dag.hd_eval_ac _ _ h2, Dag.hd_eval_ac _ _ (Dag.fit_ac.mp hr).1] at this
        exact Head.ac.inj this
      subst hfg
      rw [acCsf_ac, ite_eq_left_of_eq_true _ _ (eq_self f)]
      exact ⟨ρ, Agree.refl _ _, models_push.mpr ⟨m, e⟩⟩
    | var y =>
      rw [acCsf_var]
      split
      · next val hval =>
        rw [Dag.eval_var] at e
        exact ih.csf2 b hl (b.vals _ _ hval) m (fun _ h => by cases h) (e.trans (var_val_equiv m hval))
      · exact ⟨ρ, Agree.refl _ _, models_push.mpr ⟨m, e⟩⟩
    | atom c =>
      exact (no_equiv e (by rw [Dag.hd_eval_ac _ _ h2, Dag.hd_eval_atom]; intro h; cases h)).elim
    | free g bs =>
      exact (no_equiv e (by rw [Dag.hd_eval_ac _ _ h2, Dag.hd_eval_free]; intro h; cases h)).elim
    | comm g c d =>
      exact (no_equiv e (by rw [Dag.hd_eval_ac _ _ h2, Dag.hd_eval_comm]; intro h; cases h)).elim
  pC {st f a c ρ} b ha hc m := by
    rw [purifyC_succ]
    have left : Res.Prom (fun q : St s × Dag s => ∃ ρ', Agree st.vals.size ρ ρ' ∧ Models q.1 ρ' ∧
        EquivB (Dag.eval ρ' q.2) (Dag.eval ρ a)) (pLeft r k st a) := by
      rcases pLeft_cases r k st a with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e]
      · exact ⟨ρ, Agree.refl _ _, m, .refl _⟩
      · exact comp_freshCsf r ih b ha m
    refine left.bind fun ⟨st1, a'⟩ h1 ⟨ρ1, a1, m1, ea⟩ => ?_
    obtain ⟨b1, fa', le1⟩ := wf_pLeft r (wfK r k) b ha h1
    have right : Res.Prom (fun q : St s × Dag s => ∃ ρ', Agree st1.vals.size ρ1 ρ' ∧ Models q.1 ρ' ∧
        EquivB (Dag.eval ρ' q.2) (Dag.eval ρ c)) (pRight r k st1 a c a') := by
      rcases pRight_cases r k st1 a c a' with ⟨hca, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e]
      · subst hca; exact ⟨ρ1, Agree.refl _ _, m1, ea⟩
      · exact ⟨ρ1, Agree.refl _ _, m1, by rw [Dag.eval_agree hc.2 a1]; exact .refl _⟩
      · refine (comp_freshCsf r ih b1 (hc.mono le1) m1).mono fun _ _ ⟨ρ2, a2, m2, e2⟩ => ⟨ρ2, a2, m2, ?_⟩
        rw [Dag.eval_agree hc.2 a1] at e2
        exact e2
    refine right.map fun ⟨st2, b'⟩ h3 ⟨ρ2, a2, m2, eb⟩ => ⟨ρ2, a1.trans a2 le1, m2, ?_⟩
    refine (Dag.eval_mkComm r _ ρ2 f a' b').trans ?_
    rw [Dag.eval_comm, Dag.eval_comm, Dag.eval_agree fa'.2 a2]
    exact .comm_congr f ea eb
  comm {st f a c rt ρ} b ha hc hr m e := by
    cases rt with
    | comm g c0 c1 =>
      have hfg : f = g := by
        have := hd_eq e
        rw [Dag.hd_eval_comm, Dag.hd_eval_comm] at this
        exact Head.comm.inj this
      subst hfg
      obtain ⟨h0, h1⟩ := Dag.fit_comm.mp hr
      rw [commCsf_comm, ite_eq_right_of_eq_false _ _ (eq_false (fun h => h rfl))]
      rw [Dag.eval_comm, Dag.eval_comm] at e
      split
      · exact comp_commBody r ih b h0 h1 ha hc m e.symm
      · exact comp_commBody r ih b ha hc h0 h1 m e
    | var y =>
      have hy := Dag.fit_var.mp hr
      have hrv := lastVar_lt b hy
      rw [Dag.eval_var] at e
      rw [commCsf_var]
      split
      · next val hval =>
        exact ih.comm b ha hc (b.vals _ _ hval) m (e.trans (var_val_equiv m hval))
      · refine (ih.pC b ha hc m).bind fun q _ ⟨ρ1, a1, m1, ep⟩ => ?_
        refine ⟨ρ1, a1, models_bind (m1.except _) fun d e' => ?_⟩
        cases e'
        rw [a1 _ hrv]
        exact (models_lastVar m y).symm.trans (e.symm.trans ep.symm)
    | atom x =>
      exact (no_equiv e (by rw [Dag.hd_eval_comm, Dag.hd_eval_atom]; intro h; cases h)).elim
    | free g bs =>
      exact (no_equiv e (by rw [Dag.hd_eval_comm, Dag.hd_eval_free]; intro h; cases h)).elim
    | ac g bs =>
      exact (no_equiv e (by
        rw [Dag.hd_eval_comm, Dag.hd_eval_ac _ _ (Dag.fit_ac.mp hr).1]; intro h; cases h)).elim

theorem compK : ∀ k, CompK r k
  | 0 => compK_zero r
  | k + 1 => compK_succ r (compK k)

end Tamarin.MaudeUnify
