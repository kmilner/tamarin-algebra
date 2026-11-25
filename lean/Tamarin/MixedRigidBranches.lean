import Tamarin.MixedReconstruction

/-! Congruence constraints between rigid terms whose outputs have been
identified. Consume each pair once. Additional child equations may enable
previously unrelated pairs, including under different constructors. -/
namespace Tamarin.MixedUnification.RigidBranches
variable {s : Signature}

abbrev Solves (p : Problem s) (θ : UnifierSorts.Template s) :=
  ∀ e ∈ p, EquivB (e.lhs.subst θ) (e.rhs.subst θ)

private theorem append_iff (a b : Problem s) (θ) :
    Solves (a ++ b) θ ↔ Solves a θ ∧ Solves b θ := by
  simp [Solves,List.mem_append,or_imp,forall_and]

variable [DecidableEq s.FreeSym] [DecidableEq s.CSym]

private def align : Term s → Term s → List (Problem s)
  | .free f xs,.free g ys =>
    if eq : f = g then [List.ofFn fun i => ⟨xs i,ys (eq ▸ i)⟩] else []
  | .comm f a b,.comm g c d =>
    if f = g then [[⟨a,c⟩,⟨b,d⟩],[⟨a,d⟩,⟨b,c⟩]] else []
  | _,_ => []

private theorem align_covers (a b : Term s) (θ : UnifierSorts.Template s)
    (active : align a b ≠ []) (eq : EquivB (a.subst θ) (b.subst θ)) :
    ∃ extra ∈ align a b, Solves extra θ := by
  cases a <;> cases b <;> try contradiction
  case free.free f xs g ys =>
    by_cases same : f = g
    · subst g
      simp only [align,↓reduceDIte]
      refine ⟨_,List.mem_singleton_self _,?_⟩

      intro e he
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
      exact (Matching.free_equiv_iff ..).mp eq i
    · simp [align,same] at active
  case comm.comm f a b g c d =>
    by_cases same : f = g
    · subst g
      simpa [align,Solves] using (Commutative.equiv_iff ..).mp eq
    · simp [align,same] at active

variable [DecidableEq (Term s)]

/-- Two rigid terms with their positions in the interned term table. -/
private abbrev Pair (s : Signature) := Nat × Nat × Term s × Term s

private def rigid : Term s → Bool
  | .free .. | .comm .. => true
  | _ => false

/-- The input term list is already interned. Only unordered pairs can give
new obligations, and zero-arity and syntactically distinct heads never branch. -/
private def pairs (i : Nat) : List (Term s) → List (Pair s)
  | [] => []
  | t :: ts =>
    ((ts.zipIdx (i+1)).filterMap fun u =>
      if (align t u.1).isEmpty then none else some (i,u.2,t,u.1)) ++ pairs (i+1) ts

omit [DecidableEq (Term s)] in
private theorem pairs_at (before xs : List (Term s)) (z : Pair s) (hz : z ∈ pairs before.length xs) :
    (before ++ xs)[z.1]? = some z.2.2.1 ∧ (before ++ xs)[z.2.1]? = some z.2.2.2 ∧
      z.2.2.1 ∈ xs ∧ z.2.2.2 ∈ xs ∧ align z.2.2.1 z.2.2.2 ≠ [] := by
  induction xs generalizing before with
  | nil => contradiction
  | cons x xs ih =>
    rcases List.mem_append.mp hz with hm | hm
    · obtain ⟨u,hu,eq⟩ := List.mem_filterMap.mp hm
      split at eq
      · contradiction
      next h =>
        cases eq
        obtain ⟨le,at_u⟩ := List.mem_zipIdx_iff_le_and_getElem?_sub.mp hu
        refine ⟨by simp,?_,List.mem_cons_self,List.mem_cons_of_mem _ (List.mem_of_getElem? at_u),
          by simpa using h⟩
        show (before ++ x :: xs)[u.2]? = some u.1
        rw [List.getElem?_append_right (by omega)]
        rw [show u.2 - before.length = (u.2 - (before.length + 1)) + 1 by omega]
        simpa using at_u
    · have step := ih (before ++ [x]) (by simpa using hm)
      simp only [List.append_assoc, List.singleton_append] at step
      obtain ⟨ia,ib,ha,hb,ok⟩ := step
      exact ⟨ia,ib,List.mem_cons_of_mem _ ha,List.mem_cons_of_mem _ hb,ok⟩

/-- The pair is identified by the current slots and not yet aligned. The
slots of the two terms are read from the table by position. -/
private def enabled (k : Term s → Nat) (slots : Array Nat) (pair : Pair s) :=
  slots.getD pair.1 0 == slots.getD pair.2.1 0 &&
  !(align pair.2.2.1 pair.2.2.2).any (fun es => es.all fun e => k e.lhs == k e.rhs)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] in
private theorem inventory_append (before p : Problem s) {t} (h : t ∈ inventory p) :
    t ∈ inventory (before ++ p) := by
  simpa [inventory] using Or.inr (a := t ∈ before.flatMap (fun e => subterms e.lhs ++ subterms e.rhs))
    (List.mem_eraseDups.mp h)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq (Term s)] in
private theorem slot_at (table : Array (Term s)) (k : Term s → Nat) (i : Nat) (t : Term s)
    (h : table[i]? = some t) : (table.map k).getD i 0 = k t := by
  simp [Array.getD_eq_getD_getElem?, h]

private abbrev Known (table : Array (Term s)) (p : Problem s) (z : Pair s) : Prop :=
  table[z.1]? = some z.2.2.1 ∧ table[z.2.1]? = some z.2.2.2 ∧
    z.2.2.1 ∈ inventory p ∧ z.2.2.2 ∈ inventory p ∧ align z.2.2.1 z.2.2.2 ≠ []

/-- One alternative for every pair, joined. -/
private def combine : List (List (Problem s)) → List (Problem s)
  | [] => [[]]
  | alts :: rest => alts.flatMap fun a => (combine rest).map (a ++ ·)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq (Term s)] in
private theorem combine_covers (θ : UnifierSorts.Template s) (xs : List (List (Problem s)))
    (each : ∀ alts ∈ xs, ∃ a ∈ alts, Solves a θ) : ∃ extra ∈ combine xs, Solves extra θ := by
  induction xs with
  | nil => exact ⟨[],List.mem_singleton_self _,fun _ h => nomatch h⟩
  | cons alts rest ih =>
    obtain ⟨a,ha,sa⟩ := each alts List.mem_cons_self
    obtain ⟨extra,he,se⟩ := ih (fun x hx => each x (List.mem_cons_of_mem _ hx))
    exact ⟨a ++ extra,List.mem_flatMap.mpr ⟨a,ha,List.mem_map_of_mem he⟩,
      (append_iff ..).mpr ⟨sa,se⟩⟩

/-- Align at once every pair that the current slots identify and that has a
single alignment. The number of passes over those pairs is then the depth of
the congruence, not the number of identified pairs, and a pass reads the slot
of each rigid term once. A pair with several alignments is taken alone, and
only when no pair with a single alignment is left: each of its alignments
changes the slots, which usually settles the other pairs of its class. Taking
all of them at once would multiply their alternatives. -/
private def loop (table : Array (Term s)) (todo : List (Pair s)) (p : Problem s)
    (inside : ∀ z ∈ todo, Known table p z) :
    {ps : List (Problem s) // (∀ child ∈ ps, ∀ e ∈ p, e ∈ child) ∧
      ∀ θ, Solves p θ → ∃ child ∈ ps, Solves child θ} := by
  -- Nothing to align: the slots are not needed.
  if todo.isEmpty then exact ⟨[p],⟨by simp,fun _ h => ⟨_,List.mem_singleton_self _,h⟩⟩⟩ else
  let q := slotsOnly p
  let slots := table.map q.slot
  let hits := todo.filter (enabled q.slot slots)
  match found : hits with
  | [] => exact ⟨[p],⟨by simp,fun _ h => ⟨_,List.mem_singleton_self _,h⟩⟩⟩
  | first :: more =>
    let forced := hits.any fun z => (align z.2.2.1 z.2.2.2).length ≤ 1
    let pick (z : Pair s) : Bool := enabled q.slot slots z &&
      (if forced then decide ((align z.2.2.1 z.2.2.2).length ≤ 1)
       else z.1 == first.1 && z.2.1 == first.2.1)
    let batch := todo.filter pick
    have member (z : Pair s) (hz : z ∈ batch) : z ∈ todo ∧ enabled q.slot slots z = true := by
      obtain ⟨mem,yes⟩ := List.mem_filter.mp hz
      exact ⟨mem,(Bool.and_eq_true_iff.mp yes).1⟩
    have some : ∃ z ∈ todo, pick z = true := by
      have firstHit : first ∈ todo ∧ enabled q.slot slots first = true := by
        have : first ∈ hits := by rw [found]; exact List.mem_cons_self
        exact List.mem_filter.mp this
      cases hf : forced with
      | true =>
        obtain ⟨z,hz,short⟩ := List.any_eq_true.mp hf
        obtain ⟨mem,yes⟩ := List.mem_filter.mp hz
        exact ⟨z,mem,by simp only [pick,yes,hf,Bool.true_and,ite_true]; exact short⟩
      | false => exact ⟨first,firstHit.1,by simp [pick,firstHit.2,hf]⟩
    let rest := todo.filter (fun z => !(pick z))
    have lt : rest.length < todo.length := by
      obtain ⟨z,hz,yes⟩ := some
      exact List.length_filter_lt_length_iff_exists.mpr ⟨z,hz,by simp [yes]⟩
    let visit (extra : Problem s) := loop table rest (extra ++ p) (fun t ht => by
      obtain ⟨ia,ib,ha,hb,ok⟩ := inside t (List.mem_filter.mp ht).1
      exact ⟨ia,ib,inventory_append _ _ ha,inventory_append _ _ hb,ok⟩)
    refine ⟨(combine (batch.map fun z => align z.2.2.1 z.2.2.2)).flatMap
      (fun es => (visit es).val),?_,?_⟩
    · intro child hc e he
      obtain ⟨es,_,hmem⟩ := List.mem_flatMap.mp hc
      exact (visit es).property.1 child hmem e (List.mem_append_right _ he)
    · intro θ sol
      obtain ⟨V,hV⟩ := inventory_values p θ sol
      have each : ∀ alts ∈ batch.map (fun z => align z.2.2.1 z.2.2.2),
          ∃ a ∈ alts, Solves a θ := by
        intro alts ha
        obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ha
        obtain ⟨ia,ib,ha,hb,ok⟩ := inside z (member z hz).1
        have yes := (member z hz).2
        simp only [enabled,Bool.and_eq_true,beq_iff_eq] at yes
        have same : (purify p).slot z.2.2.1 = (purify p).slot z.2.2.2 := by
          have left := slot_at table q.slot _ _ ia
          have right := slot_at table q.slot _ _ ib
          exact left.symm.trans (yes.1.trans right)
        have eq := hV _ ha
        change EquivB _ (V ((purify p).slot z.2.2.1)) at eq
        rw [same] at eq
        exact align_covers _ _ θ ok (eq.trans (hV _ hb).symm)
      obtain ⟨extra,he,hs⟩ := combine_covers θ _ each
      obtain ⟨c,hc,hsol⟩ := (visit extra).property.2 θ ((append_iff ..).mpr ⟨hs,sol⟩)
      exact ⟨c,List.mem_flatMap.mpr ⟨extra,he,hc⟩,hsol⟩
termination_by todo.length
decreasing_by exact lt

def refineProblem (p : Problem s) :
    {ps : List (Problem s) // (∀ child ∈ ps, ∀ e ∈ p, e ∈ child) ∧
      ∀ θ, Solves p θ → ∃ child ∈ ps, Solves child θ} := by
  let ts := (inventory p).filter rigid
  exact loop ts.toArray (pairs 0 ts) p (fun z hz => by
    obtain ⟨ia,ib,ha,hb,ok⟩ := pairs_at [] ts z hz
    exact ⟨by simpa using ia,by simpa using ib,(List.mem_filter.mp ha).1,(List.mem_filter.mp hb).1,ok⟩)

/-- Some subterm is a free or C application. -/
private def hasRigid : Term s → Bool
  | .free .. | .comm .. => true
  | .ac _ a b => hasRigid a || hasRigid b
  | _ => false

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq (Term s)] in
private theorem hasRigid_of_subterm : ∀ (u : Term s) {t : Term s}, t ∈ subterms u →
    rigid t = true → hasRigid u = true
  | .var _, t, h, r => by
    simp only [subterms, List.mem_singleton] at h
    subst h; simp [rigid] at r
  | .atom _, t, h, r => by
    simp only [subterms, List.mem_singleton] at h
    subst h; simp [rigid] at r
  | .free .., _, _, _ => rfl
  | .comm .., _, _, _ => rfl
  | .ac _ a b, t, h, r => by
    simp only [subterms, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · simp [rigid] at r
    · simp [hasRigid, hasRigid_of_subterm a h r]
    · simp [hasRigid, hasRigid_of_subterm b h r]

private theorem loop_nil (table : Array (Term s)) (todo : List (Pair s)) (p : Problem s)
    (inside : ∀ z ∈ todo, Known table p z) (h : todo = []) :
    (loop table todo p inside).val = [p] := by
  subst h
  unfold loop
  simp

/-- A cheap key of a term: its shape and its variables. Symbols are not read. -/
private def hkey : Term s → UInt64
  | .var v => mixHash 11 (hash v.id)
  | .atom _ => 13
  | .free f xs => (List.finRange (s.arity f)).foldl (fun h i => mixHash h (hkey (xs i))) 17
  | .comm _ a b => mixHash 19 (mixHash (hkey a) (hkey b))
  | .ac _ a b => mixHash 23 (mixHash (hkey a) (hkey b))

/-- A term with its key. -/
private abbrev Keyed (s : Signature) := UInt64 × Term s

private def keyed (t : Term s) : Keyed s := (hkey t,t)

/-- Membership, comparing the keys before the terms. -/
private def hasK : List (Keyed s) → Keyed s → Bool
  | [], _ => false
  | e :: es, x => (e.1 == x.1 && e.2 == x.2) || hasK es x

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] in
private theorem hasK_eq (S : List (Keyed s)) (x : Keyed s) :
    hasK S x = S.any fun e => e.1 == x.1 && e.2 == x.2 := by
  induction S with
  | nil => rfl
  | cons e es ih => simp only [hasK,List.any_cons,ih]

/-- The sides of the equations with their keys. -/
private def keyedSides (p : Problem s) : List (Keyed s × Keyed s) :=
  p.map fun e => (keyed e.lhs,keyed e.rhs)

/-- One pass over the equations: the other side of each equation with a
listed side is added. -/
private def linkStep : List (Keyed s × Keyed s) → List (Keyed s) → List (Keyed s)
  | [], acc => acc
  | e :: es, acc =>
    linkStep es (if hasK acc e.1 then (if hasK acc e.2 then acc else e.2 :: acc)
      else if hasK acc e.2 then e.1 :: acc else acc)

/-- Passes of `linkStep` until one adds nothing, at most the given number:
the list it stopped at, or `none` when the passes ran out. -/
private def linkUntil (eqs : List (Keyed s × Keyed s)) : Nat → List (Keyed s) → Option (List (Keyed s))
  | 0, _ => none
  | n+1, S =>
    let next := linkStep eqs S
    if next.length == S.length then some S else linkUntil eqs n next

/-- Whether `u` has the slot of `t` in the purification of the problem whose
keyed sides are given, read from the terms linked to `t`; `none` when the
passes ran out. -/
private def sameSlot? (eqs : List (Keyed s × Keyed s)) (t u : Term s) : Option Bool :=
  (linkUntil eqs (2 * eqs.length + 2) [keyed t]).map fun S => hasK S (keyed u)

/-- Every entry is the term with its key. -/
private def Honest (S : List (Keyed s)) : Prop := ∀ e ∈ S, e = keyed e.2

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] in
private theorem hasK_iff {S : List (Keyed s)} (h : Honest S) (x : Term s) :
    hasK S (keyed x) = true ↔ x ∈ S.map (·.2) := by
  rw [hasK_eq,List.any_eq_true]
  constructor
  · rintro ⟨e,he,ok⟩
    simp only [Bool.and_eq_true,beq_iff_eq] at ok
    exact List.mem_map.mpr ⟨e,he,ok.2⟩
  · intro hx
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
    refine ⟨e,he,?_⟩
    rw [h e he]
    simp [keyed]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq (Term s)] in
private theorem keyedSides_honest {p : Problem s} {d : Keyed s × Keyed s} (hd : d ∈ keyedSides p) :
    ∃ e ∈ p, d = (keyed e.lhs,keyed e.rhs) := by
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
  exact ⟨e,he,rfl⟩

/-- What one step of the pass does to the list. -/
private def linkOne (acc : List (Keyed s)) (e : Keyed s × Keyed s) : List (Keyed s) :=
  if hasK acc e.1 then (if hasK acc e.2 then acc else e.2 :: acc)
  else if hasK acc e.2 then e.1 :: acc else acc

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] in
private theorem linkStep_eq (eqs : List (Keyed s × Keyed s)) (S : List (Keyed s)) :
    linkStep eqs S = eqs.foldl linkOne S := by
  induction eqs generalizing S with
  | nil => rfl
  | cons e es ih => exact ih _

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] in
private theorem linkOne_sub (acc : List (Keyed s)) (e : Keyed s × Keyed s) :
    ∀ x ∈ acc, x ∈ linkOne acc e := by
  intro x hx
  unfold linkOne
  split
  · split
    · exact hx
    · exact List.mem_cons_of_mem _ hx
  · split
    · exact List.mem_cons_of_mem _ hx
    · exact hx

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] in
private theorem linkOne_length (acc : List (Keyed s)) (e : Keyed s × Keyed s) :
    acc.length ≤ (linkOne acc e).length := by
  unfold linkOne
  split
  · split
    · exact Nat.le_refl _
    · simp
  · split
    · simp
    · exact Nat.le_refl _

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] in
private theorem fold_sub (eqs : List (Keyed s × Keyed s)) :
    ∀ (S : List (Keyed s)), ∀ x ∈ S, x ∈ eqs.foldl linkOne S := by
  induction eqs with
  | nil => exact fun _ _ h => h
  | cons e es ih => exact fun S x hx => ih _ x (linkOne_sub S e x hx)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] in
private theorem fold_length (eqs : List (Keyed s × Keyed s)) :
    ∀ (S : List (Keyed s)), S.length ≤ (eqs.foldl linkOne S).length := by
  induction eqs with
  | nil => exact fun _ => Nat.le_refl _
  | cons e es ih => exact fun S => Nat.le_trans (linkOne_length S e) (ih _)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] in
/-- A pass that adds nothing found every equation with both sides listed or
neither. -/
private theorem fold_closed (eqs : List (Keyed s × Keyed s)) :
    ∀ (S : List (Keyed s)), (eqs.foldl linkOne S).length = S.length →
      ∀ e ∈ eqs, hasK S e.1 = hasK S e.2 := by
  induction eqs with
  | nil => intro _ _ e he; cases he
  | cons d ds ih =>
    intro S same e he
    simp only [List.foldl_cons] at same
    have grow := fold_length ds (linkOne S d)
    have still : linkOne S d = S := by
      have le := linkOne_length S d
      have eq : (linkOne S d).length = S.length := by omega
      unfold linkOne at eq ⊢
      by_cases l : hasK S d.1 = true
      · by_cases r : hasK S d.2 = true
        · simp [l,r]
        · simp [l,r] at eq
      · by_cases r : hasK S d.2 = true
        · simp [l,r] at eq
        · simp [l,r]
    rw [still] at same
    rcases List.mem_cons.mp he with rfl | he
    · unfold linkOne at still
      split at still
      · next l =>
        split at still
        · next r => rw [l,r]
        · next r => exact absurd (congrArg List.length still) (by simp)
      · next l =>
        split at still
        · exact absurd (congrArg List.length still) (by simp)
        · next r => simp only [Bool.not_eq_true] at l r; rw [l,r]
    · exact ih S same e he

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] in
private theorem fold_honest (eqs : List (Keyed s × Keyed s))
    (keys : ∀ d ∈ eqs, d.1 = keyed d.1.2 ∧ d.2 = keyed d.2.2) :
    ∀ (S : List (Keyed s)), Honest S → Honest (eqs.foldl linkOne S) := by
  induction eqs with
  | nil => exact fun _ h => h
  | cons d ds ih =>
    intro S hS
    apply ih (fun d' hd' => keys d' (List.mem_cons_of_mem _ hd'))
    have kd := keys d List.mem_cons_self
    intro x hx
    unfold linkOne at hx
    split at hx
    · split at hx
      · exact hS x hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact kd.2
        · exact hS x hx
    · split at hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact kd.1
        · exact hS x hx
      · exact hS x hx

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] in
/-- Every term added by a pass has the slot of a listed term. -/
private theorem fold_slots (k : Term s → Nat) (c : Nat) (eqs : List (Keyed s × Keyed s))
    (links : ∀ d ∈ eqs, k d.1.2 = k d.2.2) :
    ∀ (S : List (Keyed s)), (∀ x ∈ S, k x.2 = c) → ∀ x ∈ eqs.foldl linkOne S, k x.2 = c := by
  induction eqs with
  | nil => exact fun _ h => h
  | cons d ds ih =>
    intro S hS
    apply ih (fun d' hd' => links d' (List.mem_cons_of_mem _ hd'))
    have link := links d List.mem_cons_self
    intro x hx
    unfold linkOne at hx
    split at hx
    · next l =>
      split at hx
      · exact hS x hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · rw [hasK_eq] at l
          obtain ⟨y,hy,ok⟩ := List.any_eq_true.mp l
          simp only [Bool.and_eq_true,beq_iff_eq] at ok
          rw [← link,← ok.2]
          exact hS y hy
        · exact hS x hx
    · split at hx
      · next r =>
        rcases List.mem_cons.mp hx with rfl | hx
        · rw [hasK_eq] at r
          obtain ⟨y,hy,ok⟩ := List.any_eq_true.mp r
          simp only [Bool.and_eq_true,beq_iff_eq] at ok
          rw [link,← ok.2]
          exact hS y hy
        · exact hS x hx
      · exact hS x hx

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] in
/-- The list `linkUntil` stops at is honest, holds the start, has the slot of
its start throughout and is closed under the equations. -/
private theorem linkUntil_spec (k : Term s → Nat) (c : Nat) (eqs : List (Keyed s × Keyed s))
    (keys : ∀ d ∈ eqs, d.1 = keyed d.1.2 ∧ d.2 = keyed d.2.2)
    (links : ∀ d ∈ eqs, k d.1.2 = k d.2.2) :
    ∀ (n : Nat) (S out : List (Keyed s)), linkUntil eqs n S = some out → Honest S →
      (∀ x ∈ S, k x.2 = c) →
      Honest out ∧ (∀ x ∈ S, x ∈ out) ∧ (∀ x ∈ out, k x.2 = c) ∧
        ∀ d ∈ eqs, hasK out d.1 = hasK out d.2
  | 0, _, _, h, _, _ => by cases h
  | n+1, S, out, h, hS, cS => by
    unfold linkUntil at h
    dsimp only at h
    split at h
    · next same =>
      cases h
      refine ⟨hS,fun _ hx => hx,cS,?_⟩
      rw [linkStep_eq] at same
      exact fold_closed eqs S (by simpa using same)
    · obtain ⟨ho,sub,co,cl⟩ := linkUntil_spec k c eqs keys links n _ out h
        (by rw [linkStep_eq]; exact fold_honest eqs keys S hS)
        (by rw [linkStep_eq]; exact fold_slots k c eqs links S cS)
      exact ⟨ho,fun x hx => sub x (by rw [linkStep_eq]; exact fold_sub eqs S x hx),co,cl⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] in
/-- A decided `sameSlot?` is the comparison of the slots of `purify`. -/
private theorem sameSlot?_spec {p : Problem s} {t u : Term s} {b : Bool}
    (h : sameSlot? (keyedSides p) t u = some b) (ht : t ∈ inventory p) (hu : u ∈ inventory p) :
    b = ((purify p).slot t == (purify p).slot u) := by
  unfold sameSlot? at h
  obtain ⟨S,hS,rfl⟩ := Option.map_eq_some_iff.mp h
  have keys : ∀ d ∈ keyedSides p, d.1 = keyed d.1.2 ∧ d.2 = keyed d.2.2 := by
    intro d hd
    obtain ⟨e,_,rfl⟩ := keyedSides_honest hd
    exact ⟨rfl,rfl⟩
  have links : ∀ d ∈ keyedSides p, (purify p).slot d.1.2 = (purify p).slot d.2.2 := by
    intro d hd
    obtain ⟨e,he,rfl⟩ := keyedSides_honest hd
    exact purify_links p e he
  obtain ⟨honest,sub,slots,closedK⟩ := linkUntil_spec (purify p).slot ((purify p).slot t) _ keys links
    _ [keyed t] S hS (fun x hx => by rw [List.mem_singleton.mp hx]; rfl)
    (fun x hx => by rw [List.mem_singleton.mp hx]; rfl)
  have closed : ∀ e ∈ p, e.lhs ∈ S.map (·.2) ↔ e.rhs ∈ S.map (·.2) := by
    intro e he
    have := closedK (keyed e.lhs,keyed e.rhs) (List.mem_map.mpr ⟨e,he,rfl⟩)
    rw [← hasK_iff honest,← hasK_iff honest,this]
  have self : t ∈ S.map (·.2) := List.mem_map.mpr ⟨_,sub _ List.mem_cons_self,rfl⟩
  cases hm : hasK S (keyed u) with
  | true =>
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp ((hasK_iff honest u).mp hm)
    have := slots e he
    simp [this]
  | false =>
    have out : u ∉ S.map (·.2) := fun hin => by
      rw [(hasK_iff honest u).mpr hin] at hm
      cases hm
    have ne : (purify p).slot t ≠ (purify p).slot u := fun same =>
      out (purify_slot_closed p _ closed self ht hu same)
    simp [ne]

/-- Surely not enabled: the slots of the pair differ, or one of its alignments
holds already. Decided from the equations alone, without the slots. -/
private def quietPair (eqs : List (Keyed s × Keyed s)) (z : Pair s) : Bool :=
  match sameSlot? eqs z.2.2.1 z.2.2.2 with
  | some false => true
  | some true =>
    (align z.2.2.1 z.2.2.2).any fun es => es.all fun e => sameSlot? eqs e.lhs e.rhs == some true
  | none => false

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq (Term s)] in
private theorem self_sub (t : Term s) : t ∈ subterms t := by
  cases t <;> simp [subterms]

omit [DecidableEq (Term s)] in
private theorem align_subterms {a b : Term s} {es : Problem s} (h : es ∈ align a b) :
    ∀ e ∈ es, e.lhs ∈ subterms a ∧ e.rhs ∈ subterms b := by
  intro e he
  unfold align at h
  split at h
  · next f xs g ys =>
    split at h
    · next eq =>
      subst eq
      obtain rfl := List.mem_singleton.mp h
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
      exact ⟨List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,self_sub _⟩),
        List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,self_sub _⟩)⟩
    · cases h
  · next f a b g c d =>
    split at h
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl <;> simp only [List.mem_cons,List.not_mem_nil,
        or_false] at he <;> rcases he with rfl | rfl <;> simp [subterms,self_sub]
    · cases h
  · cases h

private theorem quietPair_enabled {table : Array (Term s)} {p : Problem s} {z : Pair s}
    (known : Known table p z) (h : quietPair (keyedSides p) z = true) :
    enabled (slotsOnly p).slot (table.map (slotsOnly p).slot) z = false := by
  obtain ⟨ia,ib,ha,hb,_⟩ := known
  unfold enabled
  rw [slot_at table _ _ _ ia,slot_at table _ _ _ ib,slotsOnly_slot]
  unfold quietPair at h
  split at h
  · next hs =>
    have := sameSlot?_spec hs ha hb
    simp [← this]
  · next hs =>
    have := sameSlot?_spec hs ha hb
    obtain ⟨es,hes,all⟩ := List.any_eq_true.mp h
    have yes : (align z.2.2.1 z.2.2.2).any (fun es => es.all fun e =>
        (purify p).slot e.lhs == (purify p).slot e.rhs) = true := by
      apply List.any_eq_true.mpr
      refine ⟨es,hes,List.all_eq_true.mpr fun e he => ?_⟩
      have one := List.all_eq_true.mp all e he
      have sub := align_subterms hes e he
      cases hq : sameSlot? (keyedSides p) e.lhs e.rhs with
      | none => simp [hq] at one
      | some c =>
        rw [hq] at one
        have := sameSlot?_spec hq (inventory_subterms ha _ sub.1) (inventory_subterms hb _ sub.2)
        simp at one
        rw [← this, one]
    simp [yes]
  · cases h

private theorem loop_quiet (table : Array (Term s)) (todo : List (Pair s)) (p : Problem s)
    (inside : ∀ z ∈ todo, Known table p z) (h : todo.all (quietPair (keyedSides p)) = true) :
    (loop table todo p inside).val = [p] := by
  unfold loop
  split
  · rfl
  · dsimp only
    have none : todo.filter (enabled (slotsOnly p).slot (table.map (slotsOnly p).slot)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro z hz
      rw [quietPair_enabled (inside z hz) (List.all_eq_true.mp h z hz)]
      simp
    split
    · rfl
    · next first more found =>
      rw [none] at found
      cases found

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] in
private theorem filter_loop (q : Term s → Bool) :
    ∀ (l acc : List (Term s)),
      (List.eraseDupsBy.loop (· == ·) l acc).filter q =
        List.eraseDupsBy.loop (· == ·) (l.filter q) (acc.filter q)
  | [], acc => by simp [List.eraseDupsBy.loop,List.filter_reverse]
  | a :: as, acc => by
    by_cases qa : q a = true
    · have same : (acc.filter q).any (fun b => a == b) = acc.any (fun b => a == b) := by
        rw [List.any_filter]
        congr 1
        funext b
        by_cases ab : a = b
        · subst ab; simp [qa]
        · simp [ab]
      simp only [List.eraseDupsBy.loop,List.filter_cons,qa,↓reduceIte]
      rw [same]
      split
      · exact filter_loop q as acc
      · rw [filter_loop q as (a :: acc)]
        simp [qa]
    · simp only [List.eraseDupsBy.loop,List.filter_cons,qa,Bool.false_eq_true,↓reduceIte]
      split
      · exact filter_loop q as acc
      · rw [filter_loop q as (a :: acc)]
        simp [qa]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] in
/-- The rigid interned terms, without interning the others. -/
private theorem rigid_inventory (p : Problem s) :
    (inventory p).filter rigid =
      Buckets.dedup bucketKey ((p.flatMap fun e => subterms e.lhs ++ subterms e.rhs).filter rigid) := by
  rw [Buckets.dedup_eq]
  unfold inventory List.eraseDups List.eraseDupsBy
  exact filter_loop rigid _ []

/-- `refineProblem` of a problem without free or C subterms, or whose pairs of
rigid terms are surely not enabled. There is no rigid pair to align, and the
problem is its own only child. -/
private def refineProblemPlain (p : Problem s) :
    {ps : List (Problem s) // (∀ child ∈ ps, ∀ e ∈ p, e ∈ child) ∧
      ∀ θ, Solves p θ → ∃ child ∈ ps, Solves child θ} :=
  if p.any (fun e => hasRigid e.lhs || hasRigid e.rhs) then
    if (pairs 0 (Buckets.dedup bucketKey ((p.flatMap fun e => subterms e.lhs ++ subterms e.rhs).filter
        rigid))).all (quietPair (keyedSides p)) then
      ⟨[p],by simp,fun _ h => ⟨_,List.mem_singleton_self _,h⟩⟩
    else refineProblem p
  else ⟨[p],by simp,fun _ h => ⟨_,List.mem_singleton_self _,h⟩⟩

@[csimp] private theorem refineProblem_eq_plain : @refineProblem = @refineProblemPlain := by
  funext s _ _ _ p
  unfold refineProblemPlain
  split
  · split
    · next quiet =>
      apply Subtype.ext
      unfold refineProblem
      rw [← rigid_inventory] at quiet
      exact loop_quiet _ _ _ _ quiet
    · rfl
  · next plain =>
    apply Subtype.ext
    have none : (inventory p).filter rigid = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro t ht r
      obtain ⟨e,he,mem⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp ht)
      apply plain
      apply List.any_eq_true.mpr
      refine ⟨e,he,?_⟩
      rcases List.mem_append.mp mem with l | r'
      · simp [hasRigid_of_subterm _ l r]
      · simp [hasRigid_of_subterm _ r' r]
    unfold refineProblem
    exact loop_nil _ _ _ _ (by rw [none]; rfl)

variable [Interrupt]

/-- The answers of each child in order, or `none` at the first child that
does not complete. The loop carries the finished children, so its stack does
not grow with their number. -/
private def gather [Interrupt] {ι α : Type} (run : ι → Option (List α)) :
    List ι → List (List α) → Option (List (List α))
  | [], done => some done.reverse
  | x :: xs, done =>
    match run x with
    | none => none
    | some a => gather run xs (a :: done)

/-- `gather` as it is compiled: it asks before every child. -/
private def gatherAsking [Interrupt] {ι α : Type} (run : ι → Option (List α)) :
    List ι → List (List α) → Option (List (List α))
  | [], done => some done.reverse
  | x :: xs, done =>
    if Interrupt.poll () then none
    else match run x with
      | none => none
      | some a => gatherAsking run xs (a :: done)

omit [Interrupt] in
@[csimp] private theorem gather_eq_asking : @gather = @gatherAsking := by
  funext i ι α run xs done
  induction xs generalizing done with
  | nil => rfl
  | cons x xs ih => cases h : run x <;> simp [gather, gatherAsking, Interrupt.quiet, h, ih]

private theorem gather_eq {ι α : Type} (run : ι → Option (List α)) (xs : List ι)
    (done : List (List α)) :
    gather run xs done = (xs.mapM run).map (done.reverse ++ ·) := by
  induction xs generalizing done with
  | nil => simp [gather]
  | cons x xs ih =>
    cases hx : run x with
    | none => simp [gather, hx]
    | some a =>
      simp only [gather, hx, ih, List.mapM_cons, Option.bind_eq_bind, Option.bind_some,
        List.reverse_cons, List.append_assoc, List.singleton_append]
      cases xs.mapM run <;> simp

omit [Interrupt] in
private theorem mapM_some {ι α : Type} (run : ι → Option (List α)) :
    ∀ (xs : List ι) (ys : List (List α)), xs.mapM run = some ys →
      (∀ x ∈ xs, ∃ a, run x = some a ∧ a ∈ ys) ∧
      (∀ a ∈ ys, ∃ x ∈ xs, run x = some a)
  | [], ys, h => by
    obtain rfl : [] = ys := by simpa using h
    simp
  | x :: xs, ys, h => by
    cases hx : run x with
    | none => simp [hx] at h
    | some a =>
      cases ht : xs.mapM run with
      | none => simp [hx, ht] at h
      | some tail =>
        obtain rfl : a :: tail = ys := by simpa [hx, ht] using h
        obtain ⟨fwd, back⟩ := mapM_some run xs tail ht
        constructor
        · intro i hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact ⟨a, hx, List.mem_cons_self⟩
          · obtain ⟨b, hb, mem⟩ := fwd i hi
            exact ⟨b, hb, List.mem_cons_of_mem _ mem⟩
        · intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact ⟨x, List.mem_cons_self, hx⟩
          · obtain ⟨i, hi, eq⟩ := back b hb
            exact ⟨i, List.mem_cons_of_mem _ hi, eq⟩

/-- A family of search children completes only if every child completes. -/
def collect {ι α : Type} (run : ι → Option (List α)) (xs : List ι) :
    Option {ys : List α //
      (∀ x ∈ xs, ∃ a, run x = some a ∧ a ⊆ ys) ∧
      (∀ y ∈ ys, ∃ x ∈ xs, ∃ a, run x = some a ∧ y ∈ a)} :=
  match h : gather run xs [] with
  | none => none
  | some parts => some ⟨parts.flatten, by
      have all : xs.mapM run = some parts := by
        rw [gather_eq] at h
        cases hm : xs.mapM run with
        | none => simp [hm] at h
        | some ys => simpa [hm] using h
      obtain ⟨fwd, back⟩ := mapM_some run xs parts all
      constructor
      · intro x hx
        obtain ⟨a, ha, mem⟩ := fwd x hx
        exact ⟨a, ha, fun _ hy => List.mem_flatten.mpr ⟨a, mem, hy⟩⟩
      · intro y hy
        obtain ⟨a, mem, ya⟩ := List.mem_flatten.mp hy
        obtain ⟨x, hx, eq⟩ := back a mem
        exact ⟨x, hx, a, eq, ya⟩⟩

theorem collect_completes {ι α : Type} (run : ι → Option (List α)) (xs : List ι)
    (h : ∀ i ∈ xs, (run i).isSome) : (collect run xs).isSome := by
  have total : ∀ (ys : List ι) (done : List (List α)), (∀ i ∈ ys, (run i).isSome) →
      (gather run ys done).isSome := by
    intro ys
    induction ys with
    | nil => intro done _; rfl
    | cons y ys ih =>
      intro done hy
      obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp (hy y List.mem_cons_self)
      simp only [gather, ha]
      exact ih _ (fun i hi => hy i (List.mem_cons_of_mem _ hi))
  obtain ⟨parts,hp⟩ := Option.isSome_iff_exists.mp (total xs [] h)
  unfold collect
  split
  · next none => rw [hp] at none; cases none
  · rfl

abbrev Certified (p : Problem s) := {r : Option (List (UnifierSorts.Template s)) //
  ∀ rows, r = some rows → UnifierSorts.CompleteTemplates p rows}

def refineWith (p : Problem s) (run : ∀ c : Problem s, Certified c) : Certified p := by
  let children := refineProblem p
  match collect (fun c => (run c).val) children.val with
  | none => exact ⟨none,by simp⟩
  | some out =>
    refine ⟨some out.val,?_⟩
    rintro _ ⟨⟩
    constructor
    · intro θ hθ e he
      obtain ⟨c,hc,rows,hr,mem⟩ := out.property.2 θ hθ
      exact ((run c).property rows hr).sound θ mem e (children.property.1 c hc e he)
    · intro ρ sol
      obtain ⟨c,hc,hs⟩ := children.property.2 ρ.image sol
      obtain ⟨ans,hr,sub⟩ := out.property.1 c hc
      obtain ⟨θ,hθ,μ,agree⟩ := ((run c).property ans hr).covers ρ hs
      refine ⟨θ,sub hθ,μ,?_⟩
      rintro v ⟨e,he,hv⟩
      exact agree v ⟨e,children.property.1 c hc e he,hv⟩

theorem refineWith_completes (p : Problem s) (run : ∀ c : Problem s, Certified c)
    (h : ∀ c ∈ (refineProblem p).val, (run c).val.isSome) : (refineWith p run).val.isSome := by
  obtain ⟨as,ha⟩ := Option.isSome_iff_exists.mp (collect_completes _ _ h)
  simp [refineWith,ha]

end Tamarin.MixedUnification.RigidBranches
