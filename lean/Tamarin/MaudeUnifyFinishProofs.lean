import Tamarin.MaudeUnifySemantics

/-!
# Lemmas for the specification of `finish`

Term sizes, the slots and well-formedness of instantiated dags, the
instantiation of a checked order, the sort bounds, and the naming of free
slots.
-/
namespace Tamarin.MaudeUnify
open Cancellation

variable {s : Signature}

/-! ### Lists of numbers -/

theorem FinishProofs.le_sum_of_mem {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := ih h; simp; omega

theorem FinishProofs.sum_le_sum {α : Type} (l : List α) (g h : α → Nat)
    (le : ∀ x ∈ l, g x ≤ h x) : (l.map g).sum ≤ (l.map h).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := ih (fun y hy => le y (List.mem_cons_of_mem _ hy))
    have := le a (by simp)
    omega

theorem FinishProofs.sum_lt_sum {α : Type} (l : List α) (g h : α → Nat)
    (le : ∀ x ∈ l, g x ≤ h x) (lt : ∃ x ∈ l, g x < h x) : (l.map g).sum < (l.map h).sum := by
  induction l with
  | nil => obtain ⟨x, hx, _⟩ := lt; cases hx
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    obtain ⟨x, hx, hlt⟩ := lt
    have := FinishProofs.sum_le_sum l g h (fun y hy => le y (List.mem_cons_of_mem _ hy))
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have := ih (fun y hy => le y (List.mem_cons_of_mem _ hy)) ⟨x, hx, hlt⟩
      have := le a (by simp)
      omega

/-! ### Term sizes -/

theorem tsize_equiv {a b : Term s} (h : EquivB a b) : tsize a = tsize b := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | free f a b _ ih =>
    simp only [tsize]
    have : (fun i => tsize (a i)) = fun i => tsize (b i) := funext ih
    rw [this]
  | comm_congr _ _ _ ia ib | ac_congr _ _ _ ia ib => simp only [tsize, ia, ib]
  | comm_swap | ac_swap => simp only [tsize]; omega
  | ac_assoc => simp only [tsize]; omega

theorem tsize_fold_le (f : s.ACSym) (a : Term s) (bs : List (Term s)) (u : Term s)
    (hu : u ∈ a :: bs) : tsize u ≤ tsize (ACRepresentation.fold f a bs) := by
  induction bs generalizing a with
  | nil => simp at hu; subst hu; simp [ACRepresentation.fold]
  | cons b bs ih =>
    simp only [ACRepresentation.fold, tsize]
    rcases List.mem_cons.mp hu with rfl | hu
    · omega
    · have := ih b hu; omega

theorem tsize_fold_lt (f : s.ACSym) (a : Term s) (bs : List (Term s)) (u : Term s)
    (hu : u ∈ a :: bs) (hb : bs ≠ []) : tsize u < tsize (ACRepresentation.fold f a bs) := by
  obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hb
  simp only [ACRepresentation.fold, tsize]
  rcases List.mem_cons.mp hu with rfl | hu
  · omega
  · have := tsize_fold_le f b bs u hu; omega

theorem tsize_product_lt (f : s.ACSym) (ts : List (Term s)) (u : Term s) (hu : u ∈ ts)
    (hl : 2 ≤ ts.length) : tsize u < tsize (Dag.product f ts) := by
  match ts, hl with
  | a :: b :: bs, _ => exact tsize_fold_lt f a (b :: bs) u hu (by simp)

theorem tsize_free_lt (f : s.FreeSym) (xs : Fin (s.arity f) → Term s) (i : Fin (s.arity f)) :
    tsize (xs i) < tsize (.free f xs) := by
  simp only [tsize]
  have := FinishProofs.le_sum_of_mem (List.mem_ofFn.mpr ⟨i, rfl⟩ :
    tsize (xs i) ∈ List.ofFn fun i => tsize (xs i))
  omega

/-- The value of a slot a well-formed dag mentions is no larger than the dag's
value, and strictly smaller when the dag is not a slot. -/
theorem tsize_eval (ρ : Nat → Term s) (d : Dag s) (wf : d.Wf) (x : Nat) (hx : x ∈ d.vars) :
    tsize (ρ x) ≤ tsize (Dag.eval ρ d) ∧ ((∀ y, d ≠ .var y) → tsize (ρ x) < tsize (Dag.eval ρ d)) := by
  induction d using Dag.induct' with
  | var i =>
    simp [Dag.vars] at hx; subst hx
    exact ⟨by simp [Dag.eval_var], fun h => absurd rfl (h x)⟩
  | atom a => simp [Dag.vars] at hx
  | free f args ih =>
    rw [Dag.Wf] at wf
    rw [Dag.vars_free, List.mem_flatMap] at hx
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
    have hlen : args.length = s.arity f := wf.1
    have := (ih _ hd (wf.2 _ hd) hx).1
    have step : tsize (Dag.eval ρ args[k]) < tsize (Dag.eval ρ (.free f args)) := by
      rw [Dag.eval_free]
      have := tsize_free_lt f (fun i => (args.map (Dag.eval ρ)).getD i.val Dag.dflt) ⟨k, hlen ▸ hk⟩
      simpa [List.getD_eq_getElem?_getD, hk] using this
    exact ⟨by omega, fun _ => by omega⟩
  | comm f l r il ir =>
    rw [Dag.Wf] at wf
    simp only [Dag.vars, List.mem_append] at hx
    rw [Dag.eval_comm]
    rcases hx with hx | hx
    · have := (il wf.1 hx).1; simp only [tsize]; exact ⟨by omega, fun _ => by omega⟩
    · have := (ir wf.2 hx).1; simp only [tsize]; exact ⟨by omega, fun _ => by omega⟩
  | ac f args ih =>
    rw [Dag.Wf] at wf
    rw [Dag.vars_ac, List.mem_flatMap] at hx
    obtain ⟨d, hd, hx⟩ := hx
    have := (ih _ hd (wf.2 _ hd) hx).1
    have step : tsize (Dag.eval ρ d) < tsize (Dag.eval ρ (.ac f args)) := by
      rw [Dag.eval_ac]
      exact tsize_product_lt f _ _ (List.mem_map_of_mem hd) (by simpa using wf.1)
    exact ⟨by omega, fun _ => by omega⟩


/-! ### Sorts -/

namespace FinishProofs

theorem hasSort_free_inv {f : s.FreeSym} {xs : Fin (s.arity f) → Term s} {srt : SortId}
    (h : HasSort (.free f xs) srt) : Subsort (s.outputSort f) srt ∧ ∀ i, HasSort (xs i) (s.inputSort f i) := by
  have := Term.checkSort_complete h
  simp only [Term.checkSort, Bool.and_eq_true, List.all_eq_true] at this
  exact ⟨(Subsort.check_iff _ _).mp this.1,
    fun i => Term.checkSort_sound _ _ (this.2 i (List.mem_finRange i))⟩

theorem hasSort_comm_inv {f : s.CSym} {a b : Term s} {srt : SortId} (h : HasSort (.comm f a b) srt) :
    Subsort (s.cSort f) srt ∧ HasSort a (s.cSort f) ∧ HasSort b (s.cSort f) := by
  have := Term.checkSort_complete h
  simp only [Term.checkSort, Bool.and_eq_true] at this
  exact ⟨(Subsort.check_iff _ _).mp this.1.1, Term.checkSort_sound _ _ this.1.2,
    Term.checkSort_sound _ _ this.2⟩

theorem hasSort_ac_inv {f : s.ACSym} {a b : Term s} {srt : SortId} (h : HasSort (.ac f a b) srt) :
    Subsort (s.acSort f) srt ∧ HasSort a (s.acSort f) ∧ HasSort b (s.acSort f) := by
  have := Term.checkSort_complete h
  simp only [Term.checkSort, Bool.and_eq_true] at this
  exact ⟨(Subsort.check_iff _ _).mp this.1.1, Term.checkSort_sound _ _ this.1.2,
    Term.checkSort_sound _ _ this.2⟩

/-- Sorts transport along B. -/
theorem hasSort_equiv {a b : Term s} (e : EquivB a b) {srt : SortId} (h : HasSort a srt) : HasSort b srt :=
  Term.checkSort_sound _ _ (SortClash.check_equiv e srt ▸ Term.checkSort_complete h)

theorem hasSort_fold {f : s.ACSym} (a : Term s) (bs : List (Term s))
    (h : ∀ t ∈ a :: bs, HasSort t (s.acSort f)) : HasSort (ACRepresentation.fold f a bs) (s.acSort f) := by
  induction bs generalizing a with
  | nil => exact h a (by simp)
  | cons b bs ih =>
    exact .ac f _ _ (h a (by simp)) (ih b fun t ht => h t (List.mem_cons_of_mem _ ht))

theorem hasSort_fold_inv {f : s.ACSym} (a : Term s) (bs : List (Term s))
    (h : HasSort (ACRepresentation.fold f a bs) (s.acSort f)) : ∀ t ∈ a :: bs, HasSort t (s.acSort f) := by
  induction bs generalizing a with
  | nil => intro t ht; simp at ht; subst ht; exact h
  | cons b bs ih =>
    have := hasSort_ac_inv h
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact this.2.1
    · exact ih b this.2.2 t ht

theorem hasSort_product {f : s.ACSym} {ts : List (Term s)} (hl : 2 ≤ ts.length) {srt : SortId}
    (hs : Subsort (s.acSort f) srt) (h : ∀ t ∈ ts, HasSort t (s.acSort f)) :
    HasSort (Dag.product f ts) srt := by
  match ts, hl with
  | a :: b :: bs, _ =>
    exact .widen (.ac f _ _ (h a (by simp)) (hasSort_fold b bs fun t ht => h t (List.mem_cons_of_mem _ ht))) hs

theorem hasSort_product_inv {f : s.ACSym} {ts : List (Term s)} (hl : 2 ≤ ts.length) {srt : SortId}
    (h : HasSort (Dag.product f ts) srt) :
    Subsort (s.acSort f) srt ∧ ∀ t ∈ ts, HasSort t (s.acSort f) := by
  match ts, hl with
  | a :: b :: bs, _ =>
    have := hasSort_ac_inv h
    refine ⟨this.1, fun t ht => ?_⟩
    rcases List.mem_cons.mp ht with rfl | ht
    · exact this.2.1
    · exact hasSort_fold_inv b bs this.2.2 t ht

theorem meet_sound {a b m : SortId} (h : meet a b = some m) : Subsort m a ∧ Subsort m b := by
  unfold meet at h
  split at h
  · next hab => cases h; exact ⟨.refl _, (Subsort.check_iff _ _).mp hab⟩
  · split at h
    · next hba => cases h; exact ⟨(Subsort.check_iff _ _).mp hba, .refl _⟩
    · cases h

theorem meet_complete {t : Term s} {a b : SortId} (ha : HasSort t a) (hb : HasSort t b) :
    ∃ m, meet a b = some m ∧ HasSort t m := by
  have ra := Term.rootSort_le ha
  have rb := Term.rootSort_le hb
  have : Subsort a b ∨ Subsort b a := by
    revert ra rb; generalize t.rootSort = q
    intro ra rb
    cases ra <;> cases rb <;> first | exact .inl (.refl _) | exact .inl (by constructor) | exact .inr (by constructor)
  unfold meet
  rcases this with h | h
  · rw [(Subsort.check_iff _ _).mpr h]; exact ⟨a, rfl, ha⟩
  · by_cases hab : Subsort.check a b = true
    · rw [hab]; exact ⟨a, rfl, ha⟩
    · rw [Bool.eq_false_iff.mpr hab, (Subsort.check_iff _ _).mpr h]; exact ⟨b, rfl, hb⟩

/-! ### Sort bounds -/

/-- A valuation meets the bounds on the slots satisfying `P`. -/
def SatP (P : Nat → Prop) (ν : Nat → Term s) (ub : Array (Option SortId)) : Prop :=
  ∀ x c, P x → ub.getD x none = some c → HasSort (ν x) c

/-- What a successful computation of bounds guarantees. -/
def SoundStep (P : Nat → Prop) (n : Nat) (ub ub' : Array (Option SortId)) (Q : (Nat → Term s) → Prop) : Prop :=
  ub'.size = n ∧ ∀ ν, SatP P ν ub' → SatP P ν ub ∧ Q ν

theorem foldBind_none {α : Type} (F : Array (Option SortId) → α → Option (Array (Option SortId))) (L : List α) :
    L.foldl (fun acc a => acc.bind fun ub => F ub a) none = none := by
  induction L with
  | nil => rfl
  | cons a L ih => exact ih

theorem foldBind_sound {α : Type} (P : Nat → Prop) (n : Nat)
    (F : Array (Option SortId) → α → Option (Array (Option SortId))) (Q : (Nat → Term s) → α → Prop)
    (L : List α)
    (hF : ∀ a ∈ L, ∀ ub ub', ub.size = n → F ub a = some ub' → SoundStep P n ub ub' fun ν => Q ν a) :
    ∀ ub ub', ub.size = n → L.foldl (fun acc a => acc.bind fun ub => F ub a) (some ub) = some ub' →
      SoundStep P n ub ub' fun ν => ∀ a ∈ L, Q ν a := by
  induction L with
  | nil => intro ub ub' hn h; cases h; exact ⟨hn, fun ν h => ⟨h, by simp⟩⟩
  | cons a L ih =>
    intro ub ub' hn h
    simp only [List.foldl_cons, Option.bind_some] at h
    cases hs : F ub a with
    | none => rw [hs, foldBind_none] at h; cases h
    | some ub1 =>
      rw [hs] at h
      obtain ⟨n1, s1⟩ := hF a (by simp) ub ub1 hn hs
      obtain ⟨n2, s2⟩ := ih (fun b hb => hF b (List.mem_cons_of_mem _ hb)) ub1 ub' n1 h
      refine ⟨n2, fun ν h => ?_⟩
      obtain ⟨h1, q2⟩ := s2 ν h
      obtain ⟨h0, q1⟩ := s1 ν h1
      exact ⟨h0, fun b hb => by
        rcases List.mem_cons.mp hb with rfl | hb
        · exact q1
        · exact q2 b hb⟩

/-- What a computation of bounds from bounds a model meets guarantees. -/
def Mono (ub ub' : Array (Option SortId)) : Prop := ∀ x, (ub.getD x none).isSome → (ub'.getD x none).isSome

theorem foldBind_complete {α : Type} (Good : Array (Option SortId) → Prop)
    (F : Array (Option SortId) → α → Option (Array (Option SortId))) (S : α → List Nat) (L : List α)
    (hF : ∀ a ∈ L, ∀ ub, Good ub → ∃ ub', F ub a = some ub' ∧ Good ub' ∧ Mono ub ub' ∧
      ∀ x ∈ S a, (ub'.getD x none).isSome) :
    ∀ ub, Good ub → ∃ ub', L.foldl (fun acc a => acc.bind fun ub => F ub a) (some ub) = some ub' ∧
      Good ub' ∧ Mono ub ub' ∧ ∀ a ∈ L, ∀ x ∈ S a, (ub'.getD x none).isSome := by
  induction L with
  | nil => intro ub g; exact ⟨ub, rfl, g, fun _ h => h, by simp⟩
  | cons a L ih =>
    intro ub g
    obtain ⟨ub1, h1, g1, m1, v1⟩ := hF a (by simp) ub g
    obtain ⟨ub2, h2, g2, m2, v2⟩ := ih (fun b hb => hF b (List.mem_cons_of_mem _ hb)) ub1 g1
    refine ⟨ub2, by simp only [List.foldl_cons, Option.bind_some, h1]; exact h2, g2,
      fun x h => m2 x (m1 x h), fun b hb x hx => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact m2 x (v1 x hx)
    · exact v2 b hb x hx

end FinishProofs

/-! ### Cycles -/

/-- A checked cycle has no model: sizes decrease weakly along its links and
strictly along its non-variable binding. -/
theorem isCycle_false {st : St s} (b : Bounded st) {ρ : Nat → Term s}
    (m : ∀ i d, st.value i = some d → EquivB (ρ i) (Dag.eval ρ d)) (c : List Nat) :
    isCycle st c = false := by
  cases c with
  | nil => rfl
  | cons first rest =>
    rw [Bool.eq_false_iff]
    intro h
    simp only [isCycle, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at h
    obtain ⟨hl, a, ha, hn⟩ := h
    let links := (first :: rest).zip ((first :: rest).drop 1 ++ [first])
    have len : ((first :: rest).drop 1 ++ [first]).length = (first :: rest).length := by simp
    have fst : links.map Prod.fst = first :: rest := List.map_fst_zip (by omega)
    have snd : links.map Prod.snd = (first :: rest).drop 1 ++ [first] := List.map_snd_zip (by omega)
    let f := fun x => tsize (ρ x)
    have le : ∀ p ∈ links, f p.2 ≤ f p.1 := by
      intro p hp
      have := hl p hp
      split at this
      · next d hd =>
        have e := tsize_equiv (m _ _ hd)
        have := (tsize_eval ρ d (b.vals _ _ hd).1 p.2 (by simpa using this)).1
        simp only [f]; omega
      · cases this
    have lt : ∃ p ∈ links, f p.2 < f p.1 := by
      have : a ∈ links.map Prod.fst := by rw [fst]; exact ha
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp this
      refine ⟨p, hp, ?_⟩
      have hb := hl p hp
      split at hb
      · next d hd =>
        have e := tsize_equiv (m _ _ hd)
        have nv : ∀ y, d ≠ .var y := by
          rintro y rfl
          simp [hd] at hn
        have := (tsize_eval ρ d (b.vals _ _ hd).1 p.2 (by simpa using hb)).2 nv
        simp only [f]; omega
      · cases hb
    have := FinishProofs.sum_lt_sum links (fun p => f p.2) (fun p => f p.1) le lt
    have e1 : (links.map fun p => f p.1) = (first :: rest).map f := by
      rw [← fst, List.map_map]; rfl
    have e2 : (links.map fun p => f p.2) = ((first :: rest).drop 1 ++ [first]).map f := by
      rw [← snd, List.map_map]; rfl
    rw [e1, e2] at this
    simp at this
    omega

/-! ### Slots of a state -/

namespace St

theorem lt_of_value_some {st : St s} {i : Nat} {d : Dag s} (h : st.value i = some d) :
    i < st.vals.size := by
  unfold value at h
  rw [Array.getD_eq_getD_getElem?] at h
  rcases Nat.lt_or_ge i st.vals.size with hi | hi
  · exact hi
  · rw [Array.getElem?_eq_none hi] at h
    cases h

theorem lt_of_sortOf_some {st : St s} {i : Nat} {srt : SortId} (h : st.sortOf i = some srt) :
    i < st.sorts.size := by
  unfold sortOf at h
  rw [Array.getD_eq_getD_getElem?] at h
  rcases Nat.lt_or_ge i st.sorts.size with hi | hi
  · exact hi
  · rw [Array.getElem?_eq_none hi] at h
    cases h

theorem value_bind (st : St s) {i : Nat} (v : Option (Dag s)) (hi : i < st.vals.size) (j : Nat) :
    (st.bind i v).value j = if j = i then v else st.value j := by
  unfold value bind
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h : j = i
  · subst h; simp [hi]
  · simp [h, Ne.symm h]

end St

/-! ### Slots and well-formedness of rebuilt dags -/

namespace Dag

theorem vars_comm (f : s.CSym) (a b : Dag s) : vars (.comm f a b) = vars a ++ vars b := by
  rw [vars]

variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

theorem inst_var (r : Ranks s) (so : Nat → Option SortId) (σ : Nat → Option (Dag s)) (i : Nat) :
    inst r so σ (.var i) = (σ i).getD (.var i) := by rw [inst]

theorem inst_free (r : Ranks s) (so : Nat → Option SortId) (σ : Nat → Option (Dag s)) (f : s.FreeSym)
    (args : List (Dag s)) : inst r so σ (.free f args) =
      if touched σ (.free f args) then .free f (args.map (inst r so σ)) else .free f args := by
  rw [inst]; simp

theorem inst_comm (r : Ranks s) (so : Nat → Option SortId) (σ : Nat → Option (Dag s)) (f : s.CSym)
    (a b : Dag s) : inst r so σ (.comm f a b) =
      if touched σ (.comm f a b) then mkComm r so f (inst r so σ a) (inst r so σ b) else .comm f a b := by
  rw [inst]

theorem inst_ac (r : Ranks s) (so : Nat → Option SortId) (σ : Nat → Option (Dag s)) (f : s.ACSym)
    (args : List (Dag s)) : inst r so σ (.ac f args) =
      if touched σ (.ac f args) then .ac f (normAC r so f (args.map (inst r so σ))) else .ac f args := by
  rw [inst]; simp

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
/-- An untouched dag is its own instance. -/
theorem mem_vars_untouched {σ : Nat → Option (Dag s)} {d : Dag s} (h : touched σ d = false) {x : Nat}
    (hx : x ∈ d.vars) : ∃ j ∈ d.vars, (σ j = none ∧ x = j) ∨ ∃ e, σ j = some e ∧ x ∈ e.vars :=
  ⟨x, hx, .inl ⟨untouched d h x hx, rfl⟩⟩

theorem mem_vars_mkComm {r : Ranks s} {so : Nat → Option SortId} {f : s.CSym} {a b : Dag s} {x : Nat}
    (h : x ∈ (mkComm r so f a b).vars) : x ∈ a.vars ∨ x ∈ b.vars := by
  unfold mkComm at h
  split at h <;> simp only [vars_comm, List.mem_append] at h
  · exact h.symm
  · exact h

theorem wf_mkComm (r : Ranks s) (so : Nat → Option SortId) (f : s.CSym) {a b : Dag s}
    (ha : a.Wf) (hb : b.Wf) : (mkComm r so f a b).Wf := by
  unfold mkComm
  split <;> rw [Wf]
  · exact ⟨hb, ha⟩
  · exact ⟨ha, hb⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] in
theorem mem_flat {f : s.ACSym} {args : List (Dag s)} {e : Dag s} (h : e ∈ flat f args) :
    e ∈ args ∨ ∃ inner, Dag.ac f inner ∈ args ∧ e ∈ inner := by
  induction args with
  | nil => simp [flat] at h
  | cons d rest ih =>
    have tail : e ∈ flat f rest → e ∈ d :: rest ∨ ∃ inner, Dag.ac f inner ∈ d :: rest ∧ e ∈ inner := by
      intro he
      rcases ih he with he | ⟨inner, hi, he⟩
      · exact .inl (List.mem_cons_of_mem _ he)
      · exact .inr ⟨inner, List.mem_cons_of_mem _ hi, he⟩
    cases d with
    | ac g inner =>
      unfold flat at h
      split at h
      · next hg =>
        obtain ⟨rfl, _⟩ := hg
        rcases List.mem_append.mp h with h | h
        · exact .inr ⟨inner, by simp, h⟩
        · exact tail h
      · rcases List.mem_cons.mp h with rfl | h
        · exact .inl (by simp)
        · exact tail h
    | _ =>
      simp only [flat, List.mem_cons] at h
      rcases h with rfl | h
      · exact .inl (by simp)
      · exact tail h

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] in
theorem length_flat (f : s.ACSym) (args : List (Dag s)) : args.length ≤ (flat f args).length := by
  induction args with
  | nil => simp
  | cons d rest ih =>
    cases d with
    | ac g inner =>
      unfold flat
      split
      · next hg =>
        have : 1 ≤ inner.length := by
          cases inner with
          | nil => exact absurd rfl hg.2
          | cons => simp
        simp; omega
      · simp; omega
    | _ => simp [flat]; omega

theorem mem_vars_normAC {r : Ranks s} {so : Nat → Option SortId} {f : s.ACSym} {args : List (Dag s)}
    {x : Nat} (h : x ∈ (Dag.ac f (normAC r so f args)).vars) : ∃ a ∈ args, x ∈ a.vars := by
  rw [vars_ac, List.mem_flatMap] at h
  obtain ⟨e, he, hx⟩ := h
  rw [normAC, (List.mergeSort_perm _ _).mem_iff] at he
  rcases mem_flat he with he | ⟨inner, hi, he⟩
  · exact ⟨e, he, hx⟩
  · refine ⟨_, hi, ?_⟩
    rw [vars_ac, List.mem_flatMap]
    exact ⟨e, he, hx⟩

theorem wf_normAC (r : Ranks s) (so : Nat → Option SortId) (f : s.ACSym) {args : List (Dag s)}
    (hl : 2 ≤ args.length) (hw : ∀ a ∈ args, a.Wf) : (Dag.ac f (normAC r so f args)).Wf := by
  rw [Wf, normAC, List.length_mergeSort]
  refine ⟨Nat.le_trans hl (length_flat f args), fun e he => ?_⟩
  rw [(List.mergeSort_perm _ _).mem_iff] at he
  rcases mem_flat he with he | ⟨inner, hi, he⟩
  · exact hw e he
  · have := hw _ hi
    rw [Wf] at this
    exact this.2 e he

/-- The slots of an instantiated dag: the unbound slots of the dag and the
slots of the values of its bound ones. -/
theorem mem_vars_inst (r : Ranks s) (so : Nat → Option SortId) (σ : Nat → Option (Dag s))
    (d : Dag s) {x : Nat} (h : x ∈ (inst r so σ d).vars) :
    ∃ j ∈ d.vars, (σ j = none ∧ x = j) ∨ ∃ e, σ j = some e ∧ x ∈ e.vars := by
  induction d using induct' with
  | var i =>
    rw [inst_var] at h
    refine ⟨i, by simp [vars], ?_⟩
    cases hσ : σ i with
    | none => rw [hσ] at h; simp [vars] at h; exact .inl ⟨rfl, h⟩
    | some e => rw [hσ] at h; exact .inr ⟨e, rfl, h⟩
  | atom a => rw [inst] at h; simp [vars] at h
  | free f args ih =>
    rw [inst_free] at h
    split at h
    case isFalse t => exact mem_vars_untouched (by simpa using t) h
    rw [vars_free, List.mem_flatMap] at h
    obtain ⟨e, he, hx⟩ := h
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    obtain ⟨j, hj, hr⟩ := ih a ha hx
    exact ⟨j, by rw [vars_free, List.mem_flatMap]; exact ⟨a, ha, hj⟩, hr⟩
  | comm f a b ia ib =>
    rw [inst_comm] at h
    split at h
    case isFalse t => exact mem_vars_untouched (by simpa using t) h
    rcases mem_vars_mkComm h with h | h
    · obtain ⟨j, hj, hr⟩ := ia h
      exact ⟨j, by rw [vars_comm]; exact List.mem_append_left _ hj, hr⟩
    · obtain ⟨j, hj, hr⟩ := ib h
      exact ⟨j, by rw [vars_comm]; exact List.mem_append_right _ hj, hr⟩
  | ac f args ih =>
    rw [inst_ac] at h
    split at h
    case isFalse t => exact mem_vars_untouched (by simpa using t) h
    obtain ⟨e, he, hx⟩ := mem_vars_normAC h
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    obtain ⟨j, hj, hr⟩ := ih a ha hx
    exact ⟨j, by rw [vars_ac, List.mem_flatMap]; exact ⟨a, ha, hj⟩, hr⟩

theorem wf_inst (r : Ranks s) (so : Nat → Option SortId) (σ : Nat → Option (Dag s))
    (d : Dag s) (hd : d.Wf) (hσ : ∀ j ∈ d.vars, ∀ e, σ j = some e → e.Wf) : (inst r so σ d).Wf := by
  induction d using induct' with
  | var i =>
    rw [inst_var]
    cases h : σ i with
    | none => trivial
    | some e => exact hσ i (by simp [vars]) e h
  | atom a => rw [inst]; trivial
  | free f args ih =>
    rw [inst_free]
    split
    case isFalse => exact hd
    rw [Wf] at hd
    rw [Wf, List.length_map]
    refine ⟨hd.1, fun e he => ?_⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    exact ih a ha (hd.2 a ha) fun j hj => hσ j (by rw [vars_free, List.mem_flatMap]; exact ⟨a, ha, hj⟩)
  | comm f a b ia ib =>
    rw [inst_comm]
    split
    case isFalse => exact hd
    rw [Wf] at hd
    exact wf_mkComm r so f (ia hd.1 fun j hj => hσ j (by rw [vars_comm]; exact List.mem_append_left _ hj))
      (ib hd.2 fun j hj => hσ j (by rw [vars_comm]; exact List.mem_append_right _ hj))
  | ac f args ih =>
    rw [inst_ac]
    split
    case isFalse => exact hd
    rw [Wf] at hd
    refine wf_normAC r so f (by simpa using hd.1) fun e he => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    exact ih a ha (hd.2 a ha) fun j hj => hσ j (by rw [vars_ac, List.mem_flatMap]; exact ⟨a, ha, hj⟩)

end Dag

/-! ### Instantiation along a checked order -/

theorem FinishProofs.getD_setIfInBounds {α : Type} (a : Array α) {i : Nat} (v : α) (hi : i < a.size)
    (j : Nat) (d : α) : (a.setIfInBounds i v).getD j d = if j = i then v else a.getD j d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h : j = i
  · subst h; simp [hi]
  · simp [h, Ne.symm h]


theorem Binds.through {st : St s} {ρ : Nat → Term s} (m : Binds st ρ) (j : Nat) :
    EquivB (Dag.through ρ st.value j) (ρ j) := by
  unfold Dag.through
  split
  · next d h => exact (m j d h).symm
  · exact .refl _

/-- One step of `isOrder`. -/
def orderStep (st : St s) (acc : Option (Array Bool)) (i : Nat) : Option (Array Bool) :=
  match acc with
  | none => none
  | some seen =>
    match st.value i with
    | none => none
    | some d =>
      if d.vars.all (fun j => (st.value j).isNone || seen.getD j false) then
        some (seen.setIfInBounds i true)
      else none

theorem isOrder_eq (st : St s) (order : List Nat) : isOrder st order =
    match order.foldl (orderStep st) (some (Array.replicate st.vals.size false)) with
    | none => false
    | some seen => (List.range st.vals.size).all fun i => (st.value i).isNone || seen.getD i false :=
  rfl

theorem orderStep_none (st : St s) (l : List Nat) : l.foldl (orderStep st) none = none := by
  induction l with
  | nil => rfl
  | cons i l ih => exact ih

variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]
variable (r : Ranks s)

/-- One step of `instantiate`. -/
def instStep (st : St s) (i : Nat) : St s :=
  match st.value i with
  | some d => st.bind i (some (Dag.inst r st.sortOf st.value d))
  | none => st

theorem instantiate_eq (st : St s) (order : List Nat) :
    instantiate r st order = order.foldl (instStep r) st := rfl

/-- The invariant of the instantiation: the slots marked seen have values
over unbound slots, the others keep their bindings, and the models do not
change. -/
structure InstInv (st stk : St s) (S : Array Bool) : Prop where
  size : stk.vals.size = st.vals.size
  sorts : stk.sorts = st.sorts
  pending : stk.pending = st.pending
  ssize : S.size = st.vals.size
  bound : ∀ i, (stk.value i).isSome = (st.value i).isSome
  seen : ∀ i, S.getD i false = true →
    ∃ d, stk.value i = some d ∧ d.Wf ∧ ∀ x ∈ d.vars, x < st.vals.size ∧ st.value x = none
  unseen : ∀ i, S.getD i false = false → stk.value i = st.value i
  models : ∀ ρ, Binds st ρ ↔ Binds stk ρ

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem InstInv.start (st : St s) : InstInv st st (Array.replicate st.vals.size false) where
  size := rfl
  sorts := rfl
  pending := rfl
  ssize := by simp
  bound := fun _ => rfl
  seen := fun i h => by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at h
    split at h <;> simp at h
  unseen := fun _ _ => rfl
  models := fun _ => .rfl

theorem InstInv.step {st stk : St s} {S S' : Array Bool} {i : Nat} (b : Bounded st)
    (inv : InstInv st stk S) (h : orderStep st (some S) i = some S') :
    InstInv st (instStep r stk i) S' := by
  simp only [orderStep] at h
  split at h
  · cases h
  · next d0 hd0 =>
    split at h
    · next hall =>
      cases h
      simp only [List.all_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none] at hall
      have hi : i < st.vals.size := St.lt_of_value_some hd0
      obtain ⟨d, hd⟩ : ∃ d, stk.value i = some d := by
        have := inv.bound i
        rw [hd0] at this
        exact Option.isSome_iff_exists.mp this
      have hA : d.Wf ∧ ∀ x ∈ d.vars, x < st.vals.size ∧ (st.value x = none ∨ S.getD x false = true) := by
        cases hS : S.getD i false with
        | true =>
          obtain ⟨d', hd', w, hv⟩ := inv.seen i hS
          rw [hd] at hd'; cases hd'
          exact ⟨w, fun x hx => ⟨(hv x hx).1, .inl (hv x hx).2⟩⟩
        | false =>
          have := inv.unseen i hS
          rw [hd, hd0] at this; cases this
          exact ⟨(b.vals _ _ hd0).1, fun x hx => ⟨(b.vals _ _ hd0).2 x hx, hall x hx⟩⟩
      have hB : i ∉ d.vars := by
        intro hx
        rcases (hA.2 i hx).2 with h | h
        · rw [hd0] at h; cases h
        · obtain ⟨d', hd', _, hv⟩ := inv.seen i h
          rw [hd] at hd'; cases hd'
          have := (hv i hx).2
          rw [hd0] at this; cases this
      have hi' : i < stk.vals.size := inv.size ▸ hi
      have hstep : instStep r stk i = stk.bind i (some (Dag.inst r stk.sortOf stk.value d)) := by
        unfold instStep; rw [hd]
      rw [hstep]
      have hval := St.value_bind stk (some (Dag.inst r stk.sortOf stk.value d)) hi'
      have hset := FinishProofs.getD_setIfInBounds S true (inv.ssize ▸ hi)
      -- the seen slots of the values
      have seenVal : ∀ j e, stk.value j = some e →
          (st.value j = none ∨ S.getD j false = true) →
          e.Wf ∧ ∀ x ∈ e.vars, x < st.vals.size ∧ st.value x = none := by
        intro j e he hj
        rcases hj with hj | hj
        · have := inv.bound j
          rw [he, hj] at this; cases this
        · obtain ⟨e', he', w, hv⟩ := inv.seen j hj
          rw [he] at he'; cases he'
          exact ⟨w, hv⟩
      have eqv : ∀ ρ, Binds stk ρ → EquivB (Dag.eval ρ (Dag.inst r stk.sortOf stk.value d)) (Dag.eval ρ d) :=
        fun ρ m => .trans (Dag.eval_inst r _ _ ρ d) (Dag.eval_equiv d fun j _ => m.through j)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [St.bind, inv.size]
      · exact inv.sorts
      · exact inv.pending
      · simp [inv.ssize]
      · intro j
        rw [hval]
        split
        · next hj => subst hj; rw [hd0]; rfl
        · exact inv.bound j
      · intro j hj
        rw [hset] at hj
        rw [hval]
        split
        · next hji =>
          subst hji
          refine ⟨_, rfl, ?_, ?_⟩
          · refine Dag.wf_inst r _ _ d hA.1 fun y hy e he => (seenVal y e he (hA.2 y hy).2).1
          · intro x hx
            obtain ⟨y, hy, hr⟩ := Dag.mem_vars_inst r _ _ d hx
            rcases hr with ⟨hn, rfl⟩ | ⟨e, he, hx⟩
            · refine ⟨(hA.2 x hy).1, ?_⟩
              have := inv.bound x
              rw [hn] at this
              exact Option.not_isSome_iff_eq_none.mp (by rw [← this]; simp)
            · exact (seenVal y e he (hA.2 y hy).2).2 x hx
        · next hji =>
          rw [ite_eq_right hji] at hj
          exact inv.seen j hj
      · intro j hj
        rw [hset] at hj
        rw [hval]
        split
        · next hji => rw [ite_eq_left hji] at hj; cases hj
        · next hji => rw [ite_eq_right hji] at hj; exact inv.unseen j hj
      · intro ρ
        refine (inv.models ρ).trans ⟨fun m j e he => ?_, fun m j e he => ?_⟩
        · rw [hval] at he
          split at he
          · next hji =>
            subst hji; cases he
            exact .trans (m _ _ hd) (eqv ρ m).symm
          · exact m j e he
        · by_cases hji : j = i
          · subst hji
            rw [hd] at he; cases he
            have mi := m j _ (by rw [hval, ite_eq_left rfl])
            refine .trans mi (.trans (Dag.eval_inst r _ _ ρ _) (Dag.eval_equiv _ fun y hy => ?_))
            unfold Dag.through
            split
            · next e he =>
              have hyj : y ≠ j := fun h => hB (h ▸ hy)
              exact (m y e (by rw [hval, ite_eq_right hyj]; exact he)).symm
            · exact .refl _
          · exact m j e (by rw [hval, ite_eq_right hji]; exact he)
    · simp at h

theorem InstInv.fold {st : St s} (b : Bounded st) (order : List Nat) :
    ∀ {stk : St s} {S SF : Array Bool}, InstInv st stk S →
    order.foldl (orderStep st) (some S) = some SF → InstInv st (order.foldl (instStep r) stk) SF := by
  induction order with
  | nil => intro stk S SF inv h; cases h; exact inv
  | cons i order ih =>
    intro stk S SF inv h
    simp only [List.foldl_cons] at h ⊢
    cases hs : orderStep st (some S) i with
    | none => rw [hs, orderStep_none] at h; cases h
    | some S' => rw [hs] at h; exact ih (inv.step r b hs) h

/-- What instantiation along a checked order guarantees. -/
structure Instantiated (st st' : St s) : Prop where
  size : st'.vals.size = st.vals.size
  sorts : st'.sorts = st.sorts
  pending : st'.pending = st.pending
  bound : ∀ i, (st'.value i).isSome = (st.value i).isSome
  vals : ∀ i d, st'.value i = some d → d.Wf ∧ ∀ x ∈ d.vars, x < st.vals.size ∧ st.value x = none
  models : ∀ ρ, Binds st ρ ↔ Binds st' ρ

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem Instantiated.none_iff {st st' : St s} (I : Instantiated st st') (x : Nat) :
    st'.value x = none ↔ st.value x = none := by
  have := I.bound x
  constructor
  · intro h; rw [h] at this
    cases h' : st.value x with
    | none => rfl
    | some _ => rw [h'] at this; cases this
  · intro h; rw [h] at this
    cases h' : st'.value x with
    | none => rfl
    | some _ => rw [h'] at this; cases this

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem Instantiated.sortOf {st st' : St s} (I : Instantiated st st') (x : Nat) :
    st'.sortOf x = st.sortOf x := by
  simp [St.sortOf, I.sorts]

theorem instantiate_spec {st : St s} (b : Bounded st) {order : List Nat} (h : isOrder st order = true) :
    Instantiated st (instantiate r st order) := by
  rw [isOrder_eq] at h
  split at h
  · cases h
  · next SF hf =>
    have inv := InstInv.fold r b order (InstInv.start st) hf
    rw [instantiate_eq]
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Option.isNone_iff_eq_none] at h
    refine ⟨inv.size, inv.sorts, inv.pending, inv.bound, fun i d hd => ?_, inv.models⟩
    have hi : i < st.vals.size := inv.size ▸ St.lt_of_value_some hd
    rcases h i hi with h | h
    · have := inv.bound i
      rw [hd, h] at this; cases this
    · obtain ⟨d', hd', w⟩ := inv.seen i h
      rw [hd] at hd'; cases hd'
      exact w

/-! ### Renaming the free slots -/

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem eval_renameOut (names : Array Nat) (out : Nat → Term s) (d : Dag s) :
    Dag.eval out (renameOut names d) = Dag.eval (fun x => out (names.getD x 0)) d := by
  induction d using Dag.induct' with
  | var i => rw [renameOut, Dag.eval_var, Dag.eval_var]
  | atom a => rw [renameOut, Dag.eval_atom, Dag.eval_atom]
  | free f args ih =>
    rw [renameOut, Dag.eval_free, Dag.eval_free]
    simp only [List.map_attach_eq_pmap, List.map_pmap]
    rw [List.pmap_eq_map (f := fun d => Dag.eval out (renameOut names d)), List.map_congr_left ih]
  | comm f a b ia ib => rw [renameOut, Dag.eval_comm, Dag.eval_comm, ia, ib]
  | ac f args ih =>
    rw [renameOut, Dag.eval_ac, Dag.eval_ac]
    simp only [List.map_attach_eq_pmap, List.map_pmap]
    rw [List.pmap_eq_map (f := fun d => Dag.eval out (renameOut names d)), List.map_congr_left ih]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem wf_renameOut (names : Array Nat) (d : Dag s) (hd : d.Wf) : (renameOut names d).Wf := by
  induction d using Dag.induct' with
  | var i => rw [renameOut, Dag.Wf]; trivial
  | atom a => rw [renameOut, Dag.Wf]; trivial
  | free f args ih =>
    rw [Dag.Wf] at hd
    rw [renameOut, Dag.Wf]
    simp only [List.map_attach_eq_pmap, List.length_pmap, List.mem_pmap]
    refine ⟨hd.1, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact ih a ha (hd.2 a ha)
  | comm f a b ia ib =>
    rw [Dag.Wf] at hd
    rw [renameOut, Dag.Wf]
    exact ⟨ia hd.1, ib hd.2⟩
  | ac f args ih =>
    rw [Dag.Wf] at hd
    rw [renameOut, Dag.Wf]
    simp only [List.map_attach_eq_pmap, List.length_pmap, List.mem_pmap]
    refine ⟨hd.1, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact ih a ha (hd.2 a ha)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem mem_vars_renameOut (names : Array Nat) (d : Dag s) {j : Nat} (h : j ∈ (renameOut names d).vars) :
    ∃ x ∈ d.vars, j = names.getD x 0 := by
  induction d using Dag.induct' with
  | var i => rw [renameOut] at h; simp only [Dag.vars, List.mem_singleton] at h; exact ⟨i, by simp [Dag.vars], h⟩
  | atom a => rw [renameOut] at h; simp [Dag.vars] at h
  | free f args ih =>
    rw [renameOut, Dag.vars_free, List.mem_flatMap] at h
    obtain ⟨e, he, hj⟩ := h
    simp only [List.map_attach_eq_pmap, List.mem_pmap] at he
    obtain ⟨a, ha, rfl⟩ := he
    obtain ⟨x, hx, rfl⟩ := ih a ha hj
    exact ⟨x, by rw [Dag.vars_free, List.mem_flatMap]; exact ⟨a, ha, hx⟩, rfl⟩
  | comm f a b ia ib =>
    rw [renameOut, Dag.vars_comm, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨x, hx, rfl⟩ := ia h
      exact ⟨x, by rw [Dag.vars_comm]; exact List.mem_append_left _ hx, rfl⟩
    · obtain ⟨x, hx, rfl⟩ := ib h
      exact ⟨x, by rw [Dag.vars_comm]; exact List.mem_append_right _ hx, rfl⟩
  | ac f args ih =>
    rw [renameOut, Dag.vars_ac, List.mem_flatMap] at h
    obtain ⟨e, he, hj⟩ := h
    simp only [List.map_attach_eq_pmap, List.mem_pmap] at he
    obtain ⟨a, ha, rfl⟩ := he
    obtain ⟨x, hx, rfl⟩ := ih a ha hj
    exact ⟨x, by rw [Dag.vars_ac, List.mem_flatMap]; exact ⟨a, ha, hx⟩, rfl⟩


/-! ### Soundness and completeness of the sort bounds -/

namespace FinishProofs

/-- The sort of argument `i` of a free symbol, as `bounds` reads it. -/
def argSort (f : s.FreeSym) (i : Nat) : SortId :=
  if h : i < s.arity f then s.inputSort f ⟨i, h⟩ else .msg

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem mem_zipIdx_attach {args : List (Dag s)} {p : {d // d ∈ args} × Nat}
    (hp : p ∈ args.attach.zipIdx) : ∃ h : p.2 < args.length, p.1.1 = args[p.2] := by
  rw [List.mem_zipIdx_iff_getElem?] at hp
  have hl : p.2 < args.attach.length := by
    rcases Nat.lt_or_ge p.2 args.attach.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hp; cases hp
  rw [List.getElem?_eq_getElem hl] at hp
  have e := (Option.some.inj hp).symm
  refine ⟨by simpa using hl, ?_⟩
  rw [e, List.getElem_attach]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem zipIdx_attach_mem {args : List (Dag s)} (k : Nat) (hk : k < args.length) :
    (⟨args[k], List.getElem_mem hk⟩, k) ∈ args.attach.zipIdx := by
  rw [List.mem_zipIdx_iff_getElem?]
  simp [hk]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem eval_free_arg (ν : Nat → Term s) {args : List (Dag s)} {k : Nat} (hk : k < args.length) :
    (args.map (Dag.eval ν)).getD k Dag.dflt = Dag.eval ν args[k] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem bounds_sound (P : Nat → Prop) (n : Nat) (d : Dag s) :
    ∀ (ub ub' : Array (Option SortId)) (srt : SortId), d.Wf → ub.size = n →
      (∀ x ∈ d.vars, P x ∧ x < n) → bounds ub d srt = some ub' →
      SoundStep P n ub ub' fun ν => HasSort (Dag.eval ν d) srt := by
  induction d using Dag.induct' with
  | var x =>
    intro ub ub' srt _ hn hx h
    have ⟨px, xn⟩ := hx x (by simp [Dag.vars])
    have hset := fun v => getD_setIfInBounds ub (v : Option SortId) (hn ▸ xn)
    rw [bounds] at h
    split at h
    · next hu =>
      cases h
      refine ⟨by simp [hn], fun ν sat => ⟨fun y c py hy => ?_, ?_⟩⟩
      · by_cases hyx : y = x
        · subst hyx; rw [hu] at hy; cases hy
        · exact sat y c py (by rw [hset, ite_eq_right hyx]; exact hy)
      · dsimp only; rw [Dag.eval_var]; exact sat x srt px (by rw [hset, ite_eq_left rfl])
    · next c hu =>
      cases hm : meet c srt with
      | none => rw [hm] at h; cases h
      | some m =>
        rw [hm] at h; cases h
        have ⟨mc, ms⟩ := meet_sound hm
        refine ⟨by simp [hn], fun ν sat => ⟨fun y c' py hy => ?_, ?_⟩⟩
        · by_cases hyx : y = x
          · subst hyx; rw [hu] at hy; cases hy
            exact .widen (sat y m py (by rw [hset, ite_eq_left rfl])) mc
          · exact sat y c' py (by rw [hset, ite_eq_right hyx]; exact hy)
        · dsimp only; rw [Dag.eval_var]; exact .widen (sat x m px (by rw [hset, ite_eq_left rfl])) ms
  | atom a =>
    intro ub ub' srt _ hn _ h
    rw [bounds] at h
    split at h
    · next hs =>
      cases h
      exact ⟨hn, fun ν sat => ⟨sat, by dsimp only; rw [Dag.eval_atom]; exact .widen (.atom a) ((Subsort.check_iff _ _).mp hs)⟩⟩
    · cases h
  | free f args ih =>
    intro ub ub' srt wf hn hx h
    rw [Dag.Wf] at wf
    rw [bounds] at h
    split at h
    · next hs =>
      have fs := foldBind_sound P n (fun ub p => bounds ub p.1.1 (argSort f p.2))
        (fun ν p => HasSort (Dag.eval ν p.1.1) (argSort f p.2)) args.attach.zipIdx
        (fun p hp ub ub' hn h => by
          obtain ⟨hk, he⟩ := mem_zipIdx_attach hp
          have hm : p.1.1 ∈ args := p.1.2
          exact ih p.1.1 hm ub ub' _ (wf.2 _ hm) hn
            (fun x hx' => hx x (by rw [Dag.vars_free, List.mem_flatMap]; exact ⟨_, hm, hx'⟩)) h)
        ub ub' hn h
      refine ⟨fs.1, fun ν sat => ⟨(fs.2 ν sat).1, ?_⟩⟩
      have all := (fs.2 ν sat).2
      dsimp only
      rw [Dag.eval_free]
      refine .widen (.free f _ fun i => ?_) ((Subsort.check_iff _ _).mp hs)
      have hk : i.val < args.length := by rw [wf.1]; exact i.isLt
      rw [eval_free_arg ν hk]
      have := all _ (zipIdx_attach_mem i.val hk)
      simpa [argSort, i.isLt] using this
    · cases h
  | comm f a b ia ib =>
    intro ub ub' srt wf hn hx h
    rw [Dag.Wf] at wf
    rw [bounds] at h
    split at h
    · next hs =>
      cases ha : bounds ub a (s.cSort f) with
      | none => rw [ha] at h; cases h
      | some ub1 =>
        rw [ha, Option.bind_some] at h
        have s1 := ia ub ub1 _ wf.1 hn
          (fun x h' => hx x (by rw [Dag.vars_comm]; exact List.mem_append_left _ h')) ha
        have s2 := ib ub1 ub' _ wf.2 s1.1
          (fun x h' => hx x (by rw [Dag.vars_comm]; exact List.mem_append_right _ h')) h
        refine ⟨s2.1, fun ν sat => ?_⟩
        have ⟨sat1, hb⟩ := s2.2 ν sat
        have ⟨sat0, ha'⟩ := s1.2 ν sat1
        exact ⟨sat0, by dsimp only; rw [Dag.eval_comm]; exact .widen (.comm f _ _ ha' hb) ((Subsort.check_iff _ _).mp hs)⟩
    · cases h
  | ac f args ih =>
    intro ub ub' srt wf hn hx h
    rw [Dag.Wf] at wf
    rw [bounds] at h
    split at h
    · next hs =>
      have fs := foldBind_sound P n (fun ub a => bounds ub a.1 (s.acSort f))
        (fun ν a => HasSort (Dag.eval ν a.1) (s.acSort f)) args.attach
        (fun a _ ub ub' hn h => ih a.1 a.2 ub ub' _ (wf.2 _ a.2) hn
            (fun x hx' => hx x (by rw [Dag.vars_ac, List.mem_flatMap]; exact ⟨_, a.2, hx'⟩)) h)
        ub ub' hn h
      refine ⟨fs.1, fun ν sat => ⟨(fs.2 ν sat).1, ?_⟩⟩
      have all := (fs.2 ν sat).2
      dsimp only
      rw [Dag.eval_ac]
      refine hasSort_product (by simpa using wf.1) ((Subsort.check_iff _ _).mp hs) fun t ht => ?_
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
      exact all ⟨a, ha⟩ (List.mem_attach _ _)
    · cases h

/-- The bounds hold of a valuation that meets the starting bounds everywhere. -/
def Good (ρ : Nat → Term s) (n : Nat) (ub : Array (Option SortId)) : Prop :=
  ub.size = n ∧ SatP (fun _ => True) ρ ub

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem bounds_complete (ρ : Nat → Term s) (n : Nat) (d : Dag s) :
    ∀ (ub : Array (Option SortId)) (srt : SortId), d.Wf → (∀ x ∈ d.vars, x < n) → Good ρ n ub →
      HasSort (Dag.eval ρ d) srt →
      ∃ ub', bounds ub d srt = some ub' ∧ Good ρ n ub' ∧ Mono ub ub' ∧
        ∀ x ∈ d.vars, (ub'.getD x none).isSome := by
  induction d using Dag.induct' with
  | var x =>
    intro ub srt _ hx g hs
    rw [Dag.eval_var] at hs
    have xn := hx x (by simp [Dag.vars])
    have hset := fun v => getD_setIfInBounds ub (v : Option SortId) (g.1 ▸ xn)
    have mk : ∀ m, HasSort (ρ x) m → Good ρ n (ub.setIfInBounds x (some m)) ∧
        Mono ub (ub.setIfInBounds x (some m)) ∧
        ∀ y ∈ (Dag.var x : Dag s).vars, ((ub.setIfInBounds x (some m)).getD y none).isSome := by
      intro m hm
      refine ⟨⟨by simp [g.1], fun y c _ hy => ?_⟩, fun y hy => ?_, fun y hy => ?_⟩
      · rw [hset] at hy
        split at hy
        · next hyx => subst hyx; cases hy; exact hm
        · exact g.2 y c trivial hy
      · rw [hset]; split
        · rfl
        · exact hy
      · simp [Dag.vars] at hy; subst hy; rw [hset, ite_eq_left rfl]; rfl
    cases hu : ub.getD x none with
    | none =>
      exact ⟨_, by rw [bounds, hu], mk srt hs⟩
    | some c =>
      obtain ⟨m, hm, hsm⟩ := meet_complete (g.2 x c trivial hu) hs
      exact ⟨_, by rw [bounds, hu]; dsimp only; rw [hm]; rfl, mk m hsm⟩
  | atom a =>
    intro ub srt _ _ g hs
    rw [Dag.eval_atom] at hs
    have := Term.checkSort_complete hs
    simp only [Term.checkSort] at this
    exact ⟨ub, by rw [bounds, ite_eq_left this], g, fun _ h => h, by simp [Dag.vars]⟩
  | free f args ih =>
    intro ub srt wf hx g hs
    rw [Dag.Wf] at wf
    rw [Dag.eval_free] at hs
    obtain ⟨hout, hin⟩ := hasSort_free_inv hs
    have fc := foldBind_complete (Good ρ n) (fun ub p => bounds ub p.1.1 (argSort f p.2))
      (fun p => p.1.1.vars) args.attach.zipIdx
      (fun p hp ub g => by
        obtain ⟨hk, he⟩ := mem_zipIdx_attach hp
        have hm : p.1.1 ∈ args := p.1.2
        refine ih p.1.1 hm ub _ (wf.2 _ hm)
          (fun x hx' => hx x (by rw [Dag.vars_free, List.mem_flatMap]; exact ⟨_, hm, hx'⟩)) g ?_
        have := hin ⟨p.2, wf.1 ▸ hk⟩
        rw [eval_free_arg ρ hk] at this
        simpa [argSort, wf.1 ▸ hk, he] using this)
      ub g
    obtain ⟨ub', h, g', m, v⟩ := fc
    refine ⟨ub', by rw [bounds, ite_eq_left ((Subsort.check_iff _ _).mpr hout)]; exact h, g', m, fun x hx' => ?_⟩
    rw [Dag.vars_free, List.mem_flatMap] at hx'
    obtain ⟨a, ha, hxa⟩ := hx'
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
    exact v _ (zipIdx_attach_mem k hk) x hxa
  | comm f a b ia ib =>
    intro ub srt wf hx g hs
    rw [Dag.Wf] at wf
    rw [Dag.eval_comm] at hs
    obtain ⟨hc, ha, hb⟩ := hasSort_comm_inv hs
    obtain ⟨ub1, h1, g1, m1, v1⟩ := ia ub _ wf.1
      (fun x h' => hx x (by rw [Dag.vars_comm]; exact List.mem_append_left _ h')) g ha
    obtain ⟨ub2, h2, g2, m2, v2⟩ := ib ub1 _ wf.2
      (fun x h' => hx x (by rw [Dag.vars_comm]; exact List.mem_append_right _ h')) g1 hb
    refine ⟨ub2, by rw [bounds, ite_eq_left ((Subsort.check_iff _ _).mpr hc), h1, Option.bind_some]; exact h2,
      g2, fun x h => m2 x (m1 x h), fun x hx' => ?_⟩
    rw [Dag.vars_comm, List.mem_append] at hx'
    rcases hx' with hx' | hx'
    · exact m2 x (v1 x hx')
    · exact v2 x hx'
  | ac f args ih =>
    intro ub srt wf hx g hs
    rw [Dag.Wf] at wf
    rw [Dag.eval_ac] at hs
    obtain ⟨hc, hall⟩ := hasSort_product_inv (by simpa using wf.1) hs
    have fc := foldBind_complete (Good ρ n) (fun ub a => bounds ub a.1 (s.acSort f))
      (fun a => a.1.vars) args.attach
      (fun a _ ub g => ih a.1 a.2 ub _ (wf.2 _ a.2)
        (fun x hx' => hx x (by rw [Dag.vars_ac, List.mem_flatMap]; exact ⟨_, a.2, hx'⟩)) g
        (hall _ (List.mem_map_of_mem a.2)))
      ub g
    obtain ⟨ub', h, g', m, v⟩ := fc
    refine ⟨ub', by rw [bounds, ite_eq_left ((Subsort.check_iff _ _).mpr hc)]; exact h, g', m, fun x hx' => ?_⟩
    rw [Dag.vars_ac, List.mem_flatMap] at hx'
    obtain ⟨a, ha, hxa⟩ := hx'
    exact v ⟨a, ha⟩ (List.mem_attach _ _) x hxa

end FinishProofs

/-! ### The pieces of `finish` -/

/-- The starting sort bounds: the sorts of the free original slots. -/
def ub0Of (st : St s) (nOrig : Nat) : Array (Option SortId) :=
  (Array.range st.vals.size).map fun i => if i < nOrig ∧ (st.value i).isNone then st.sortOf i else none

/-- The sort bounds from the bindings of the original slots. -/
def ubFold (st : St s) (nOrig : Nat) : Option (Array (Option SortId)) :=
  (List.range nOrig).foldl (fun acc i => acc.bind fun ub =>
    match st.value i, st.sortOf i with
    | some d, some srt => bounds ub d srt
    | _, _ => some ub) (some (ub0Of st nOrig))

/-- The free slots in slot order. -/
def freeOf (st : St s) : List Nat := (List.range st.vals.size).filter fun i => (st.value i).isNone

/-- The output number of each free slot. -/
def namesOf (st : St s) : Array Nat :=
  (freeOf st).zipIdx.foldl (fun (a : Array Nat) (i, n) => a.setIfInBounds i n) (Array.replicate st.vals.size 0)

/-- The image of a slot. -/
def imageOf (st : St s) (i : Nat) : Dag s :=
  match st.value i with
  | some d => renameOut (namesOf st) d
  | none => .var ((namesOf st).getD i 0)

/-- The answer of a solved state. -/
def mkAnswer (st : St s) (nOrig : Nat) (ub : Array (Option SortId)) : Answer s :=
  ⟨(List.range nOrig).map (imageOf st), (freeOf st).map fun i => (ub.getD i none).getD .msg⟩

theorem finish_eq (k nOrig : Nat) (st : St s) : finish r k nOrig st =
    match exploreAll st k (List.range nOrig ++ (List.range st.vals.size).drop nOrig) with
    | .gaveUp => .gaveUp
    | .cycle c => if isCycle st c then .ok none else .gaveUp
    | .done _ order =>
      if !isOrder st order then .gaveUp else
      match ubFold (instantiate r st order) nOrig with
      | none => .ok none
      | some ub => .ok (some (mkAnswer (instantiate r st order) nOrig ub)) := rfl

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem names_fold (l : List Nat) (hnd : l.Nodup) : ∀ (k : Nat) (a : Array Nat), (∀ x ∈ l, x < a.size) →
    ((l.zipIdx k).foldl (fun (a : Array Nat) (i, n) => a.setIfInBounds i n) a).size = a.size ∧
    (∀ x, x ∉ l → ((l.zipIdx k).foldl (fun (a : Array Nat) (i, n) => a.setIfInBounds i n) a).getD x 0 =
      a.getD x 0) ∧
    ∀ j (hj : j < l.length),
      ((l.zipIdx k).foldl (fun (a : Array Nat) (i, n) => a.setIfInBounds i n) a).getD l[j] 0 = k + j := by
  induction l with
  | nil => intro k a _; simp
  | cons y l ih =>
    intro k a hl
    rw [List.nodup_cons] at hnd
    have hy : y < a.size := hl y (by simp)
    simp only [List.zipIdx_cons, List.foldl_cons]
    have ⟨s1, s2, s3⟩ := ih hnd.2 (k + 1) (a.setIfInBounds y k)
      (fun x hx => by rw [Array.size_setIfInBounds]; exact hl x (List.mem_cons_of_mem _ hx))
    refine ⟨by rw [s1, Array.size_setIfInBounds], fun x hx => ?_, fun j hj => ?_⟩
    · have hxy : x ≠ y := fun h => hx (h ▸ by simp)
      rw [s2 x (fun h => hx (List.mem_cons_of_mem _ h)), FinishProofs.getD_setIfInBounds _ _ hy, ite_eq_right hxy]
    · cases j with
      | zero =>
        simp only [List.getElem_cons_zero]
        rw [s2 y hnd.1, FinishProofs.getD_setIfInBounds _ _ hy, ite_eq_left rfl]; rfl
      | succ j =>
        simp only [List.getElem_cons_succ]
        rw [s3 j (by simpa using hj)]
        omega

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem mem_freeOf {st : St s} {x : Nat} : x ∈ freeOf st ↔ x < st.vals.size ∧ st.value x = none := by
  simp [freeOf, List.mem_filter, List.mem_range]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
/-- The output number of a free slot is its position among the free slots. -/
theorem names_spec {st : St s} {x : Nat} (hx : x ∈ freeOf st) :
    ∃ (j : Nat) (hj : j < (freeOf st).length), (freeOf st)[j] = x ∧ (namesOf st).getD x 0 = j := by
  have nd : (freeOf st).Nodup := List.nodup_range.sublist List.filter_sublist
  have ⟨_, _, s3⟩ := names_fold (freeOf st) nd 0 (Array.replicate st.vals.size 0)
    (fun y hy => by simpa using (mem_freeOf.mp hy).1)
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  exact ⟨j, hj, rfl, by unfold namesOf; rw [s3 j hj]; omega⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem ub0_getD (st : St s) (nOrig x : Nat) : (ub0Of st nOrig).getD x none =
    if x < st.vals.size ∧ x < nOrig ∧ (st.value x).isNone then st.sortOf x else none := by
  unfold ub0Of
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
  by_cases hx : x < st.vals.size
  · rw [ite_eq_left hx]
    simp only [Option.map_some, Option.getD_some]
    by_cases h : x < nOrig ∧ (st.value x).isNone = true
    · rw [ite_eq_left h, ite_eq_left ⟨hx, h⟩]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.2)]
  · rw [ite_eq_right hx, ite_eq_right (fun h' => hx h'.1)]; rfl

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem ub0_size (st : St s) (nOrig : Nat) : (ub0Of st nOrig).size = st.vals.size := by
  simp [ub0Of]

theorem finish_some {k nOrig : Nat} {st : St s} {ans : Answer s} (h : finish r k nOrig st = .ok (some ans)) :
    ∃ order ub, isOrder st order = true ∧ ubFold (instantiate r st order) nOrig = some ub ∧
      ans = mkAnswer (instantiate r st order) nOrig ub := by
  rw [finish_eq] at h
  split at h
  · cases h
  · split at h <;> cases h
  · next order _ =>
    split at h
    · cases h
    · next ho =>
      split at h
      · cases h
      · next ub hub =>
        cases h
        exact ⟨order, ub, by simpa using ho, hub, rfl⟩

end Tamarin.MaudeUnify
