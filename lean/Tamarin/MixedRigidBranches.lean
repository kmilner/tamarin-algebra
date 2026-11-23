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
