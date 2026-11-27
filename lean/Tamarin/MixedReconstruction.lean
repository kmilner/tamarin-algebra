import Tamarin.ACReference
import Tamarin.FiniteOccurs
import Tamarin.ReferenceMatching
import Tamarin.TermEquality
import Tamarin.UnifierSorts
import Tamarin.Buckets

/-! Purification for simultaneous free, C and AC unification. Each distinct source
subterm has a slot. Equations identify their root slots before we emit the local
constructor constraints. Slots are shared between components and have no assigned
sort at this stage. -/
namespace Tamarin.MixedUnification
variable {s : Signature}

def subterms : Term s → List (Term s)
  | t@(.var _) | t@(.atom _) => [t]
  | t@(.free _ xs) => t :: (List.ofFn fun i => subterms (xs i)).flatten
  | t@(.comm _ a b) | t@(.ac _ a b) => t :: (subterms a ++ subterms b)

private theorem self_mem (t : Term s) : t ∈ subterms t := by
  cases t <;> simp [subterms]

private theorem var_mem {t : Term s} {v : Variable} (h : t.Occurs v) :
    .var v ∈ subterms t := by
  induction t with
  | var w => cases h; simp [subterms]
  | atom => exact False.elim h
  | free f xs ih =>
    obtain ⟨i,hi⟩ := h
    exact List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,ih i hi⟩)
  | comm f a b ia ib | ac f a b ia ib =>
    exact List.mem_cons_of_mem _ (List.mem_append.mpr (h.imp ia ib))

private theorem descend {t : Term s} (a : Term s) :
    t ∈ subterms a → ∀ u ∈ subterms t, u ∈ subterms a := by
  induction a with
  | var | atom => intro h; obtain rfl := List.mem_singleton.mp h; exact fun _ => id
  | free f xs ih =>
    intro h
    rcases List.mem_cons.mp h with rfl | h
    · exact fun _ => id
    · obtain ⟨l,hl,hit⟩ := List.mem_flatten.mp h
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl
      exact fun u hu => List.mem_cons_of_mem _ (List.mem_flatten.mpr
        ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,ih i hit u hu⟩)
  | comm f a b ia ib | ac f a b ia ib =>
    intro h
    rcases List.mem_cons.mp h with rfl | h
    · exact fun _ => id
    · rcases List.mem_append.mp h with ha | hb
      · exact fun u hu => List.mem_cons_of_mem _ (List.mem_append_left _ (ia ha u hu))
      · exact fun u hu => List.mem_cons_of_mem _ (List.mem_append_right _ (ib hb u hu))

private def redirect (lhs rhs slot : Nat) := if slot = lhs then rhs else slot

/-- Merge a pair of root slots globally. Every previous identification survives
the remaining merges, including cycles of variable aliases. -/
private def identify (key : Term s → Nat) : Problem s → Term s → Nat
  | [] => key
  | e :: es => identify (redirect (key e.lhs) (key e.rhs) ∘ key) es

private theorem identify_preserves (p : Problem s) (k : Term s → Nat) {a b} (h : k a = k b) :
    identify k p a = identify k p b := by
  induction p generalizing k with
  | nil => exact h
  | cons e es ih => apply ih; simp [h]

private theorem identify_links (p : Problem s) (k : Term s → Nat) :
    ∀ e ∈ p, identify k p e.lhs = identify k p e.rhs := by
  induction p generalizing k with
  | nil => simp
  | cons e es ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · unfold identify; apply identify_preserves; simp [redirect]
    · exact ih _ x hx

private theorem identify_values (p : Problem s) (k : Term s → Nat) (V : Nat → Term s)
    (links : ∀ e ∈ p, EquivB (V (k e.lhs)) (V (k e.rhs))) (t : Term s) :
    EquivB (V (k t)) (V (identify k p t)) := by
  induction p generalizing k with
  | nil => exact .refl _
  | cons e es ih =>
    let next := redirect (k e.lhs) (k e.rhs) ∘ k
    have step (x) : EquivB (V (k x)) (V (next x)) := by
      by_cases h : k x = k e.lhs
      · simpa [next,Function.comp_def,redirect,h] using links e List.mem_cons_self
      · simp [next,Function.comp_def,redirect,h]; exact .refl _
    exact (step t).trans (ih next (fun x hx => (step x.lhs).symm.trans
      ((links x (List.mem_cons_of_mem _ hx)).trans (step x.rhs))) )

inductive Constraint (s : Signature) where
  | atom (out : Nat) (a : s.Atom)
  | free (out : Nat) (f : s.FreeSym) (args : Fin (s.arity f) → Nat)
  | comm (out : Nat) (f : s.CSym) (lhs rhs : Nat)
  | ac (out : Nat) (f : s.ACSym) (lhs rhs : Nat)

def Constraint.out : Constraint s → Nat
  | .atom n _ | .free n .. | .comm n .. | .ac n .. => n

def Constraint.term (V : Nat → Term s) : Constraint s → Term s
  | .atom _ a => .atom a
  | .free _ f args => .free f fun i => V (args i)
  | .comm _ f a b => .comm f (V a) (V b)
  | .ac _ f a b => .ac f (V a) (V b)

def Constraint.Holds (V : Nat → Term s) (c : Constraint s) := EquivB (V c.out) (c.term V)

private def describe (k : Term s → Nat) : Term s → Option (Constraint s)
  | .var _ => none
  | t@(.atom a) => some (.atom (k t) a)
  | t@(.free f xs) => some (.free (k t) f fun i => k (xs i))
  | t@(.comm f a b) => some (.comm (k t) f (k a) (k b))
  | t@(.ac f a b) => some (.ac (k t) f (k a) (k b))

/-- `describe` with the argument slots of a free application stored. The
slot of an argument is a table lookup, and every later read of the constraint
would repeat it. -/
private def describeStored (k : Term s → Nat) : Term s → Option (Constraint s)
  | .var _ => none
  | t@(.atom a) => some (.atom (k t) a)
  | t@(.free f xs) =>
    let stored := Vector.ofFn fun i => k (xs i)
    some (.free (k t) f fun i => stored[i])
  | t@(.comm f a b) => some (.comm (k t) f (k a) (k b))
  | t@(.ac f a b) => some (.ac (k t) f (k a) (k b))

@[csimp] private theorem describe_eq_stored : @describe = @describeStored := by
  funext s k t
  cases t <;> simp [describe, describeStored]

structure System (s : Signature) where
  slot : Term s → Nat
  constraints : List (Constraint s)

def System.Model (q : System s) (V : Nat → Term s) := ∀ c ∈ q.constraints, c.Holds V

def inventory [DecidableEq (Term s)] (p : Problem s) :=
  (p.flatMap fun e => subterms e.lhs ++ subterms e.rhs).eraseDups

def purify [DecidableEq (Term s)] (p : Problem s) : System s :=
  let ts := inventory p
  let k := identify ts.idxOf p
  ⟨k, ts.filterMap (describe k)⟩

private theorem inside [DecidableEq (Term s)] {p : Problem s} {e} (he : e ∈ p) {t}
    (ht : t ∈ subterms e.lhs ∨ t ∈ subterms e.rhs) : t ∈ inventory p :=
  List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨e,he,List.mem_append.mpr ht⟩)

/-- A subterm of a subterm is a subterm. -/
theorem subterms_trans {t a : Term s} : t ∈ subterms a → ∀ u ∈ subterms t, u ∈ subterms a :=
  descend a

/-- The inventory contains every subterm of every side. -/
theorem subterm_inventory [DecidableEq (Term s)] {p : Problem s} {e} (he : e ∈ p) {t}
    (ht : t ∈ subterms e.lhs ∨ t ∈ subterms e.rhs) : t ∈ inventory p := inside he ht

/-- The two sides of an equation share a slot. -/
theorem slot_sides [DecidableEq (Term s)] (p : Problem s) :
    ∀ e ∈ p, (purify p).slot e.lhs = (purify p).slot e.rhs := identify_links p _

private theorem interpret {k : Term s → Nat} {V : Nat → Term s} (t : Term s)
    (models : ∀ u ∈ subterms t, ∀ c ∈ describe k u, c.Holds V) :
    EquivB (V (k t)) (t.subst (fun v => V (k (.var v)))) := by
  induction t with
  | var => exact .refl _
  | atom a => exact models _ (self_mem _) _ rfl
  | free f xs ih =>
    apply (models _ (self_mem _) _ rfl).trans
    apply EquivB.free
    intro i
    apply ih i
    intro u hu
    exact models u (List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,hu⟩))
  | comm f a b ia ib | ac f a b ia ib =>
    apply (models _ (self_mem _) _ rfl).trans
    first | apply EquivB.comm_congr | apply EquivB.ac_congr
    · apply ia
      exact fun u hu => models u (List.mem_cons_of_mem _ (List.mem_append_left _ hu))
    · apply ib
      exact fun u hu => models u (List.mem_cons_of_mem _ (List.mem_append_right _ hu))

section Purification
variable [DecidableEq (Term s)]

/-- The slots of the interned terms after each merge, as a table. -/
private def identifyTable (ts : List (Term s)) : List Nat → Problem s → List Nat
  | table, [] => table
  | table, e :: es =>
    let a := table.getD (ts.idxOf e.lhs) 0
    let b := table.getD (ts.idxOf e.rhs) 0
    identifyTable ts (table.map (redirect a b)) es

private theorem getD_map_idxOf (ts : List (Term s)) (key : Term s → Nat) {t : Term s}
    (ht : t ∈ ts) (d : Nat) : (ts.map key).getD (ts.idxOf t) d = key t := by
  have lt := List.idxOf_lt_length_of_mem ht
  simp [List.getD_eq_getElem?_getD, lt, List.getElem_idxOf]

private theorem identifyTable_eq (ts : List (Term s)) (p : Problem s) (key : Term s → Nat)
    (known : ∀ e ∈ p, e.lhs ∈ ts ∧ e.rhs ∈ ts) :
    identifyTable ts (ts.map key) p = ts.map (identify key p) := by
  induction p generalizing key with
  | nil => rfl
  | cons e es ih =>
    have ⟨hl,hr⟩ := known e List.mem_cons_self
    simp only [identifyTable, identify]
    rw [getD_map_idxOf ts key hl, getD_map_idxOf ts key hr, List.map_map]
    exact ih _ (fun e he => known e (List.mem_cons_of_mem _ he))

/-- A cheap key read from the top of a term. Symbols are not inspected, so the
key separates terms by their shape and by the variables near the root. -/
private def termKey : Nat → Term s → UInt64
  | 0, _ => 0
  | _+1, .var v => 2 * v.id.toUInt64 + 1
  | _+1, .atom _ => 2
  | d+1, .free f xs => Fin.foldl (s.arity f) (fun acc i => acc * 31 + termKey d (xs i)) 3
  | d+1, .comm _ a b => (termKey d a * 31 + termKey d b) * 37 + 5
  | d+1, .ac _ a b => (termKey d a * 31 + termKey d b) * 41 + 7

/-- The length of the right spine of a product. The partial products of a
long product agree near the root and differ in this length. -/
private def spine : Term s → Nat
  | .ac _ _ b => spine b + 1
  | _ => 0

def bucketKey (t : Term s) : Nat := (termKey 3 t).toNat + 1000003 * spine t

/-- `inventory` comparing each subterm only with the kept subterms of the same key. -/
private def inventoryBucketed (p : Problem s) : List (Term s) :=
  Buckets.dedup bucketKey (p.flatMap fun e => subterms e.lhs ++ subterms e.rhs)

@[csimp] theorem inventory_eq_bucketed : @inventory = @inventoryBucketed := by
  funext s _ p
  exact (Buckets.dedup_eq ..).symm

/-- `identifyTable` on an array, reading the two slots by the supplied index
and leaving the table alone when they already agree. -/
private def identifyArray (idx : Term s → Nat) : Array Nat → Problem s → Array Nat
  | table, [] => table
  | table, e :: es =>
    let a := table.getD (idx e.lhs) 0
    let b := table.getD (idx e.rhs) 0
    identifyArray idx (if a = b then table else table.map (redirect a b)) es

private theorem identifyArray_eq (ts : List (Term s)) (table : Array Nat) (p : Problem s) :
    (identifyArray ts.idxOf table p).toList = identifyTable ts table.toList p := by
  induction p generalizing table with
  | nil => rfl
  | cons e es ih =>
    have get (i : Nat) : table.getD i 0 = table.toList.getD i 0 := by
      simp only [Array.getD, List.getD, Array.getElem?_toList]
      split
      · next h => rw [Array.getElem?_eq_getElem h]; rfl
      · next h => rw [Array.getElem?_eq_none (Nat.le_of_not_lt h)]; rfl
    simp only [identifyArray, identifyTable, ih, get]
    split
    · next same =>
      rw [same]
      congr 1
      have fixed : redirect (table.toList.getD (ts.idxOf e.rhs) 0) (table.toList.getD (ts.idxOf e.rhs) 0) = id := by
        funext x
        simp [redirect]
        intro h; exact h.symm
      rw [fixed, List.map_id]
    · simp

/-- The positions of the elements of a list without repeats are the numbers
below its length, in order. -/
private theorem map_idxOf_range {α : Type} [BEq α] [LawfulBEq α] (ts : List α) (nd : ts.Nodup) :
    ts.map ts.idxOf = List.range ts.length := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [List.getElem_map, List.getElem_range]
  exact nd.idxOf_getElem i (by simpa using h₁)

private theorem filterMap_agree {α β : Type} {f g : α → Option β} (l : List α)
    (h : ∀ a ∈ l, f a = g a) : l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filterMap_cons, List.filterMap_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

private theorem inventory_nodup (p : Problem s) : (inventory p).Nodup :=
  Matching.ACBagSearch.dedup_distinct _

/-- `describe` for a term whose slot is known. -/
private def describeAt (k : Term s → Nat) (out : Nat) : Term s → Option (Constraint s)
  | .var _ => none
  | .atom a => some (.atom out a)
  | .free f xs => some (.free out f fun i => k (xs i))
  | .comm f a b => some (.comm out f (k a) (k b))
  | .ac f a b => some (.ac out f (k a) (k b))

omit [DecidableEq (Term s)] in
private theorem describeAt_slot (k : Term s → Nat) (t : Term s) : describeAt k (k t) t = describe k t := by
  cases t <;> rfl

/-- `purify` with the subterms interned in buckets and the slot of every
interned term computed once. The slot function of `purify` re-derives each
merge on every call, and looks every term up by a linear scan. The interned
terms are distinct, so the position of the `i`-th one is `i` and needs no
lookup, neither for the first table of slots nor for the slot that the
constraint of the term defines. -/
private def purifyTabled (p : Problem s) : System s :=
  let ts := inventory p
  let index := Buckets.index bucketKey (ts.length + 1) 0 ts
  let idx := fun t => Buckets.lookup bucketKey index ts.length t
  let table := identifyArray idx (Array.range ts.length) p
  let k := fun t =>
    let i := idx t
    if h : i < table.size then table[i] else identify ts.idxOf p t
  ⟨k, ts.zipIdx.filterMap fun e => describeAt k (table.getD e.2 0) e.1⟩

private theorem idx_eq (p : Problem s) :
    (fun t => Buckets.lookup bucketKey
      (Buckets.index bucketKey ((inventory p).length + 1) 0 (inventory p)) (inventory p).length t) =
      (inventory p).idxOf := by
  funext t
  simpa using Buckets.lookup_index bucketKey ((inventory p).length + 1) (by omega) 0 (inventory p) t

private theorem table_eq (p : Problem s) :
    (identifyArray (inventory p).idxOf (Array.range (inventory p).length) p).toList =
      (inventory p).map (identify (inventory p).idxOf p) := by
  rw [identifyArray_eq]
  have start : (Array.range (inventory p).length).toList = (inventory p).map (inventory p).idxOf := by
    rw [map_idxOf_range _ (inventory_nodup p)]
    simp
  rw [start]
  exact identifyTable_eq _ _ _ (fun e he => ⟨inside he (.inl (self_mem _)), inside he (.inr (self_mem _))⟩)

private theorem slot_eq (p : Problem s) :
    (fun t => if h : (inventory p).idxOf t <
        (identifyArray (inventory p).idxOf (Array.range (inventory p).length) p).size
      then (identifyArray (inventory p).idxOf (Array.range (inventory p).length) p)[(inventory p).idxOf t]
      else identify (inventory p).idxOf p t) = identify (inventory p).idxOf p := by
  funext t
  split
  · next h =>
    have lt : (inventory p).idxOf t < (inventory p).length := by
      have := congrArg List.length (table_eq p)
      simp only [Array.length_toList, List.length_map] at this
      omega
    rw [← Array.getElem_toList]
    simp [table_eq, List.getElem_idxOf lt]
  · rfl

@[csimp] theorem purify_eq_tabled : @purify = @purifyTabled := by
  funext s _ p
  simp only [purify, purifyTabled, idx_eq, slot_eq]
  congr 1
  have known : ∀ e ∈ (inventory p).zipIdx,
      describeAt (identify (inventory p).idxOf p)
        ((identifyArray (inventory p).idxOf (Array.range (inventory p).length) p).getD e.2 0) e.1 =
        describe (identify (inventory p).idxOf p) e.1 := by
    intro e he
    obtain ⟨t,i⟩ := e
    have at_i : (inventory p)[i]? = some t := by
      simpa using (List.mem_zipIdx_iff_getElem?.mp he)
    have lt : i < (inventory p).length := by
      rcases Nat.lt_or_ge i (inventory p).length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at at_i; cases at_i
    have here : (inventory p)[i] = t := by
      rw [List.getElem?_eq_getElem lt] at at_i
      exact Option.some.inj at_i
    have slot : (identifyArray (inventory p).idxOf (Array.range (inventory p).length) p).getD i 0 =
        identify (inventory p).idxOf p t := by
      have size : i < (identifyArray (inventory p).idxOf (Array.range (inventory p).length) p).size := by
        have := congrArg List.length (table_eq p)
        simp only [Array.length_toList, List.length_map] at this
        omega
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem size, Option.getD_some,
        ← Array.getElem_toList]
      simp [table_eq, here]
    dsimp only
    rw [slot, describeAt_slot]
  rw [filterMap_agree _ known]
  have spread (ts : List (Term s)) (g : Term s → Option (Constraint s)) :
      ts.filterMap g = ts.zipIdx.filterMap fun e => g e.1 := by
    conv => lhs; rw [← List.zipIdx_map_fst 0 ts]
    rw [List.filterMap_map]
    rfl
  exact spread _ _

/-- The slots of `purify` without the constructor constraints, for callers
that only compare slots. The result is a record so that its table is built
once and shared by every lookup. -/
def slotsOnly (p : Problem s) : System s := ⟨(purify p).slot, []⟩

private def slotsOnlyTabled (p : Problem s) : System s :=
  let ts := inventory p
  let index := Buckets.index bucketKey (ts.length + 1) 0 ts
  let idx := fun t => Buckets.lookup bucketKey index ts.length t
  let table := identifyArray idx (Array.range ts.length) p
  let k := fun t =>
    let i := idx t
    if h : i < table.size then table[i] else identify ts.idxOf p t
  ⟨k, []⟩

@[csimp] theorem slotsOnly_eq_tabled : @slotsOnly = @slotsOnlyTabled := by
  funext s _ p
  show (⟨(purify p).slot, []⟩ : System s) = _
  rw [purify_eq_tabled]
  rfl

theorem slotsOnly_slot (p : Problem s) : (slotsOnly p).slot = (purify p).slot := rfl

def project (q : System s) (V : Nat → Term s) : UnifierSorts.Template s :=
  fun v => V (q.slot (.var v))

theorem project_solves (p : Problem s) {V} (model : (purify p).Model V) :
    ∀ e ∈ p, EquivB (e.lhs.subst (project (purify p) V)) (e.rhs.subst (project (purify p) V)) := by
  intro e he
  have known (t) (ht : t ∈ inventory p) (c) (hc : c ∈ describe (purify p).slot t) :=
    model c (List.mem_filterMap.mpr ⟨t,ht,hc⟩)
  have left := interpret e.lhs (fun u hu => known u (inside he (.inl hu)))
  have right := interpret e.rhs (fun u hu => known u (inside he (.inr hu)))
  have same : (purify p).slot e.lhs = (purify p).slot e.rhs := identify_links p _ e he
  rw [← same] at right
  exact left.symm.trans right

/-- Every source solution gives the same value modulo B to subterms whose
slots coincide, including aliases forced by a chain of input equations. -/
theorem inventory_values (p : Problem s) (θ : UnifierSorts.Template s)
    (sol : ∀ e ∈ p, EquivB (e.lhs.subst θ) (e.rhs.subst θ)) :
    ∃ V : Nat → Term s, ∀ t ∈ inventory p, EquivB (t.subst θ) (V ((purify p).slot t)) := by
  let ts := inventory p
  let V := fun (i : Nat) => ((ts[i]?).getD (Term.var ⟨0,.msg⟩)).subst θ
  have lookup (t : Term s) (ht : t ∈ ts) : V (ts.idxOf t) = t.subst θ := by
    simp [V,List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem ht),List.getElem_idxOf]
  have links (e) (he : e ∈ p) : EquivB (V (ts.idxOf e.lhs)) (V (ts.idxOf e.rhs)) := by
    rw [lookup _ (inside he (.inl (self_mem _))),lookup _ (inside he (.inr (self_mem _)))]
    exact sol e he
  exact ⟨V, fun t ht => lookup t ht ▸ identify_values p ts.idxOf V links t⟩

theorem extend_inventory (p : Problem s) (θ : UnifierSorts.Template s)
    (sol : ∀ e ∈ p, EquivB (e.lhs.subst θ) (e.rhs.subst θ)) :
    ∃ V, (purify p).Model V ∧ ∀ t ∈ inventory p, EquivB (t.subst θ) (V ((purify p).slot t)) := by
  let ts := inventory p
  obtain ⟨V,val⟩ := inventory_values p θ sol
  refine ⟨V,?_,?_⟩
  · intro c hc
    obtain ⟨t,ht,eq⟩ := List.mem_filterMap.mp hc
    have children : ∀ u ∈ subterms t, u ∈ ts := by
      obtain ⟨e,he,hm⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp ht)
      exact fun u hu => inside he ((List.mem_append.mp hm).imp
        (fun h => descend _ h u hu) (fun h => descend _ h u hu))
    have out := (val t ht).symm
    cases t with
    | var => simp [describe] at eq
    | atom a => cases eq; exact out
    | free f xs =>
      cases eq
      exact out.trans (.free _ _ _ (fun i => val _ (children _ (List.mem_cons_of_mem _
        (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,self_mem _⟩)))))
    | comm f a b | ac f a b =>
      cases eq
      have left := val a (children _ (List.mem_cons_of_mem _ (List.mem_append_left _ (self_mem a))))
      have right := val b (children _ (List.mem_cons_of_mem _ (List.mem_append_right _ (self_mem b))))
      first | exact out.trans (.comm_congr _ left right) | exact out.trans (.ac_congr _ left right)
  · exact val

theorem var_in_inventory {p : Problem s} {v} (h : p.Occurs v) : .var v ∈ inventory p := by
  obtain ⟨e,he,hv⟩ := h
  exact inside he (hv.imp var_mem var_mem)

theorem extend_solution (p : Problem s) (θ : UnifierSorts.Template s)
    (sol : ∀ e ∈ p, EquivB (e.lhs.subst θ) (e.rhs.subst θ)) :
    ∃ V, (purify p).Model V ∧ ∀ v, p.Occurs v → EquivB (θ v) (project (purify p) V v) := by
  obtain ⟨V,h,values⟩ := extend_inventory p θ sol
  exact ⟨V,h,fun _ hv => values _ (var_in_inventory hv)⟩

/-- The two sides of an equation of the problem have one slot. -/
theorem purify_links (p : Problem s) : ∀ e ∈ p, (purify p).slot e.lhs = (purify p).slot e.rhs :=
  identify_links p _

/-- The sides of the equations are interned. -/
theorem sides_in_inventory {p : Problem s} {e : Equation s} (he : e ∈ p) :
    e.lhs ∈ inventory p ∧ e.rhs ∈ inventory p :=
  ⟨inside he (.inl (self_mem _)),inside he (.inr (self_mem _))⟩

/-- The subterms of an interned term are interned. -/
theorem inventory_subterms {p : Problem s} {t : Term s} (ht : t ∈ inventory p) :
    ∀ u ∈ subterms t, u ∈ inventory p := by
  obtain ⟨e,he,hm⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp ht)
  exact fun u hu => inside he ((List.mem_append.mp hm).imp
    (fun h => descend _ h u hu) (fun h => descend _ h u hu))

/-- Slots only identify what the equations link. A list of terms that holds,
with each side of an equation, the other side holds every interned term that
has the slot of one of its interned members. -/
theorem purify_slot_closed (p : Problem s) (S : List (Term s))
    (closed : ∀ e ∈ p, e.lhs ∈ S ↔ e.rhs ∈ S) {t u : Term s} (ht : t ∈ S) (hti : t ∈ inventory p)
    (hu : u ∈ inventory p) (same : (purify p).slot t = (purify p).slot u) : u ∈ S := by
  classical
  let ts := inventory p
  let a : Variable := ⟨0,.msg⟩
  let b : Variable := ⟨1,.msg⟩
  let V : Nat → Term s := fun n => if ∃ x ∈ S, x ∈ ts ∧ ts.idxOf x = n then .var a else .var b
  have key (y : Term s) (hy : y ∈ ts) : (∃ x ∈ S, x ∈ ts ∧ ts.idxOf x = ts.idxOf y) ↔ y ∈ S := by
    constructor
    · rintro ⟨x,hx,hxt,eq⟩
      have left := List.getElem_idxOf (List.idxOf_lt_length_of_mem hxt)
      have right := List.getElem_idxOf (List.idxOf_lt_length_of_mem hy)
      have : x = y := by
        rw [← left,← right]
        simp only [eq]
      exact this ▸ hx
    · intro h
      exact ⟨y,h,hy,rfl⟩
  have value (y : Term s) (hy : y ∈ ts) : V (ts.idxOf y) = if y ∈ S then .var a else .var b := by
    by_cases inS : y ∈ S
    · have yes : ∃ x ∈ S, x ∈ ts ∧ ts.idxOf x = ts.idxOf y := (key y hy).mpr inS
      simp only [V,yes,inS,↓reduceIte]
    · have no : ¬∃ x ∈ S, x ∈ ts ∧ ts.idxOf x = ts.idxOf y := fun h => inS ((key y hy).mp h)
      simp only [V,no,inS,↓reduceIte]
  have links (e) (he : e ∈ p) : EquivB (V (ts.idxOf e.lhs)) (V (ts.idxOf e.rhs)) := by
    rw [value _ (sides_in_inventory he).1,value _ (sides_in_inventory he).2]
    by_cases l : e.lhs ∈ S
    · simp only [l,(closed e he).mp l,↓reduceIte]
      exact .refl _
    · have r : e.rhs ∉ S := fun h => l ((closed e he).mpr h)
      simp only [l,r,↓reduceIte]
      exact .refl _
  have at_t := identify_values p ts.idxOf V links t
  have at_u := identify_values p ts.idxOf V links u
  change identify ts.idxOf p t = identify ts.idxOf p u at same
  rw [← same] at at_u
  have joint := at_u.trans at_t.symm
  rw [value u hu,value t hti] at joint
  by_cases inS : u ∈ S
  · exact inS
  · simp only [inS,ht,↓reduceIte] at joint
    have heads := joint.head_eq
    simp [Model.eval,headModel,a,b] at heads

end Purification

private def inputs : Constraint s → List Nat
  | .atom .. => []
  | .free _ _ args => List.ofFn args
  | .comm _ _ a b | .ac _ _ a b => [a,b]

private theorem child_smaller {V : Nat → Term s} {c : Constraint s}
    (h : c.Holds V) {i} (hi : i ∈ inputs c) :
    FiniteOccurs.nodes (V i) < FiniteOccurs.nodes (V c.out) := by
  rw [FiniteOccurs.nodes_equiv h]
  cases c with
  | atom => cases hi
  | free n f args =>
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
    let weights := List.ofFn (fun j => FiniteOccurs.nodes (V (args j)))
    have le (xs : List Nat) (m : Nat) (hm : m ∈ xs) : m ≤ xs.sum := by
      induction xs with
      | nil => cases hm
      | cons a xs ih =>
        rcases List.mem_cons.mp hm with rfl | hm
        · simp
        · simp only [List.sum_cons]; have := ih hm; omega
    have := le weights _ (List.mem_ofFn.mpr ⟨j,rfl⟩)
    change _ < weights.sum + 1
    omega
  | ac _ f a b | comm _ f a b =>
    change _ < FiniteOccurs.nodes (V a) + FiniteOccurs.nodes (V b) + 1
    rcases List.mem_cons.mp hi with rfl | hi
    · omega
    · obtain rfl := List.mem_singleton.mp hi; omega

private def ready (todo : List (Constraint s)) (c : Constraint s) :=
  (inputs c).all fun i => !todo.any (fun d => d.out == i)

/-- In a finite-term model, some pending constructor of least output size
has all its inputs available. This holds across different component heads. -/
private theorem ready_exists {V : Nat → Term s} (todo : List (Constraint s))
    (model : ∀ c ∈ todo, c.Holds V) (c : Constraint s) (hc : c ∈ todo) :
    ∃ d ∈ todo, ready todo d := by
  by_cases ok : ready todo c
  · exact ⟨c,hc,ok⟩
  · simp [ready] at ok
    obtain ⟨i,hi,d,hd,eq⟩ := ok
    have lt := child_smaller (model c hc) hi
    rw [← eq] at lt
    exact ready_exists todo model d hd
termination_by FiniteOccurs.nodes (V c.out)

/-- The outputs of the pending constraints, as a table of marks. -/
private def outputs (todo : List (Constraint s)) : Array Bool :=
  todo.foldl (fun acc d => acc.setIfInBounds d.out true)
    (Array.replicate (todo.foldl (fun m d => max m d.out) 0 + 1) false)

private theorem outputs_at (todo : List (Constraint s)) (i : Nat) :
    (outputs todo).getD i false = todo.any (fun d => d.out == i) := by
  have bound : ∀ (cs : List (Constraint s)) (m : Nat), ∀ d ∈ cs,
      d.out ≤ cs.foldl (fun m d => max m d.out) m := by
    intro cs
    induction cs with
    | nil => intro _ d hd; cases hd
    | cons c cs ih =>
      intro m d hd
      have grows : ∀ (xs : List (Constraint s)) (a : Nat), a ≤ xs.foldl (fun m d => max m d.out) a := by
        intro xs
        induction xs with
        | nil => exact fun a => Nat.le_refl a
        | cons x xs ih => exact fun a => Nat.le_trans (Nat.le_max_left a x.out) (ih _)
      rcases List.mem_cons.mp hd with rfl | hd
      · exact Nat.le_trans (Nat.le_max_right m d.out) (grows cs _)
      · exact ih _ d hd
  have fill : ∀ (cs : List (Constraint s)) (acc : Array Bool), (∀ d ∈ cs, d.out < acc.size) →
      (cs.foldl (fun acc d => acc.setIfInBounds d.out true) acc).getD i false =
        (acc.getD i false || cs.any (fun d => d.out == i)) := by
    intro cs
    induction cs with
    | nil => intro acc _; simp
    | cons c cs ih =>
      intro acc inside
      rw [List.foldl_cons, ih _ (fun d hd => by
        simpa using inside d (List.mem_cons_of_mem _ hd))]
      have here := inside c List.mem_cons_self
      simp only [List.any_cons, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
      by_cases same : c.out = i
      · subst same; simp [here]
      · have off : (c.out == i) = false := by simpa using same
        simp [same, off]
  unfold outputs
  rw [fill todo _ (fun d hd => by
    have := bound todo 0 d hd
    simp only [Array.size_replicate]
    omega)]
  have empty : (Array.replicate (todo.foldl (fun m d => max m d.out) 0 + 1) false).getD i false =
      false := by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  rw [empty, Bool.false_or]

/-- `ready` reading the outputs from their table. -/
private def readyIn (marks : Array Bool) (c : Constraint s) : Bool :=
  (inputs c).all fun i => !marks.getD i false

private theorem readyIn_eq (todo : List (Constraint s)) :
    readyIn (outputs todo) = ready todo := by
  funext c
  simp only [readyIn, ready, outputs_at]

/-- A valuation with one slot set. The value is an argument, so it is
computed once and not on every read of the slot. -/
private def installAt (out : Nat) (value : Term s) (images : Nat → Term s) (i : Nat) : Term s :=
  if i = out then value else images i

private def Factors (V images : Nat → Term s) (μ : Variable → Term s) :=
  ∀ i, EquivB (V i) ((images i).subst μ)

private def install (images : Nat → Term s) (c : Constraint s) (i : Nat) : Term s :=
  if i = c.out then c.term images else images i

private theorem install_factors {V images : Nat → Term s} {μ} {c : Constraint s}
    (h : Factors V images μ) (hc : c.Holds V) : Factors V (install images c) μ := by
  intro i
  by_cases eq : i = c.out
  · subst i
    simp only [install,ite_true]
    apply hc.trans
    cases c with
    | atom => exact .refl _
    | free => exact .free _ _ _ (fun i => h _)
    | comm => exact .comm_congr _ (h _) (h _)
    | ac => exact .ac_congr _ (h _) (h _)
  · simpa [install,eq] using h i

/-- Every defined slot has one constructor description. Arbitrarily many
constraints may share its value as an input, including in other components. -/
def SingleDefinition (cs : List (Constraint s)) :=
  ∀ c ∈ cs, ∀ d ∈ cs, c.out = d.out → c = d

/-- Several definitions of a slot can describe the same constructor value
under every valuation, for example after commutative alignment. -/
def AgreeingDefinitions (cs : List (Constraint s)) :=
  ∀ c ∈ cs, ∀ d ∈ cs, c.out = d.out → ∀ V, EquivB (c.term V) (d.term V)

private structure Reconstructed (todo : List (Constraint s)) (images : Nat → Term s)
    (r : Option (Nat → Term s)) : Prop where
  covers : ∀ V μ, (∀ c ∈ todo, c.Holds V) → Factors V images μ →
    ∃ row, r = some row ∧ Factors V row μ
  stable : ∀ row, r = some row → ∀ i, (∀ c ∈ todo, c.out ≠ i) → row i = images i
  solves : ∀ row, r = some row → AgreeingDefinitions todo → ∀ c ∈ todo, c.Holds row

private theorem term_agree (c : Constraint s) {V W : Nat → Term s}
    (h : ∀ i ∈ inputs c, V i = W i) : c.term V = c.term W := by
  cases c with
  | atom => rfl
  | free f g args =>
    apply congrArg (Term.free g)
    exact funext (fun i => h _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  | ac | comm =>
    simp [Constraint.term,h _ List.mem_cons_self,h _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))]

/-- Build a schematic valuation using a constructor for each defined slot.
Multiple definitions are constraints on the same output and are all checked
after construction. A dependency cycle with no ready constructor refutes
every finite valuation. -/
private def reconstruct (todo : List (Constraint s)) (images : Nat → Term s) :
    {r : Option (Nat → Term s) // Reconstructed todo images r} := by
  match todo with
  | [] => exact ⟨some images,⟨fun _ _ _ h => ⟨_,rfl,h⟩,
      fun _ eq _ _ => by cases eq; rfl, by simp⟩⟩
  | c :: cs =>
    let pending := c :: cs
    let test : Constraint s → Bool := readyIn (outputs pending)
    have same : test = ready pending := readyIn_eq pending
    match seen : pending.find? test with
    | none =>
      have found : pending.find? (ready pending) = none := same ▸ seen
      refine ⟨none,⟨fun V μ model _ => ?_,by simp,by simp⟩⟩
      obtain ⟨d,hd,ok⟩ := ready_exists pending model c List.mem_cons_self
      exact False.elim ((List.find?_eq_none.mp found d hd) ok)
    | some d =>
      have found : pending.find? (ready pending) = some d := same ▸ seen
      have hd := List.mem_of_find?_eq_some found
      let rest := pending.filter fun e => e.out != d.out
      have smaller : rest.length < pending.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨d,hd,by simp⟩
      let value := d.term images
      have stored : installAt d.out value images = install images d := rfl
      let recursed := reconstruct rest (installAt d.out value images)
      have subset {e} (he : e ∈ rest) := (List.mem_filter.mp he).1
      refine ⟨recursed.val,⟨fun V μ model h => recursed.property.covers V μ
        (fun e he => model e (subset he)) (install_factors h (model d hd)),?_,?_⟩⟩
      · intro row hr i external
        rw [recursed.property.stable row hr i (fun e he => external e (subset he))]
        simp [installAt,Ne.symm (external d hd)]
      · intro row hr unique e he
        by_cases same : e.out = d.out
        · unfold Constraint.Holds
          rw [same]
          apply EquivB.trans _ (unique d hd e he same.symm row)
          have chosen := List.find?_some found
          have available (i) (hi : i ∈ inputs d) : ∀ x ∈ pending, x.out ≠ i := by
            simpa [ready,List.all_eq_true] using (List.all_eq_true.mp chosen i hi)
          have kept (i) (hi : i ∈ inputs d) : row i = images i := by
            rw [recursed.property.stable row hr i (fun x hx => available i hi x (subset hx))]
            simp [installAt,Ne.symm (available i hi d hd)]
          rw [term_agree d kept,recursed.property.stable row hr d.out
            (fun x hx => by simpa using (List.mem_filter.mp hx).2)]
          simp [installAt, value]; exact .refl _
        · exact recursed.property.solves row hr (fun x hx y hy => unique x (subset hx) y (subset hy))
            e (List.mem_filter.mpr ⟨he,by simpa using same⟩)
termination_by todo.length

private theorem reconstruct_nil (images : Nat → Term s) :
    (reconstruct ([] : List (Constraint s)) images).val = some images := by
  rw [reconstruct]

private theorem reconstruct_cons (c : Constraint s) (cs : List (Constraint s)) (images : Nat → Term s) :
    (reconstruct (c :: cs) images).val =
      match (c :: cs).find? (readyIn (outputs (c :: cs))) with
      | none => none
      | some d => (reconstruct ((c :: cs).filter fun e => e.out != d.out)
          (installAt d.out (d.term images) images)).val := by
  rw [reconstruct]
  split <;> simp_all

/-- The valuation that a table of terms stands for: the entry of a slot
inside the table, and the variable of the slot outside it. -/
private def view (table : Array (Term s)) (i : Nat) : Term s :=
  if h : i < table.size then table[i] else .var ⟨i,.msg⟩

private theorem view_set (table : Array (Term s)) (out : Nat) (value : Term s)
    (inside : out < table.size) :
    view (table.setIfInBounds out value) = installAt out value (view table) := by
  funext i
  unfold view installAt
  by_cases same : i = out
  · subst same
    simp [inside]
  · have other : ¬ out = i := fun h => same h.symm
    simp only [same, ↓reduceIte, Array.size_setIfInBounds]
    split
    · next lt =>
      rw [Array.getElem_setIfInBounds lt]
      simp only [other, ↓reduceIte]
    · rfl

/-- `reconstruct` on a table of the slots. The valuation of `reconstruct` is
a chain of one closure per defined slot, and every read of a slot walks it.
The first argument bounds the number of constraints. -/
private def reconstructTable : Nat → List (Constraint s) → Array (Term s) → Option (Array (Term s))
  | _, [], table => some table
  | 0, _ :: _, _ => none
  | fuel + 1, c :: cs, table =>
    match (c :: cs).find? (readyIn (outputs (c :: cs))) with
    | none => none
    | some d =>
      reconstructTable fuel ((c :: cs).filter fun e => e.out != d.out)
        (table.setIfInBounds d.out (d.term (view table)))

private theorem reconstructTable_eq (n : Nat) : ∀ (todo : List (Constraint s)) (table : Array (Term s)),
    todo.length ≤ n → (∀ c ∈ todo, c.out < table.size) →
    (reconstructTable n todo table).map view = (reconstruct todo (view table)).val := by
  induction n with
  | zero =>
    intro todo table short _
    obtain rfl : todo = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp short)
    rw [reconstructTable, reconstruct_nil]
    rfl
  | succ n ih =>
    intro todo table short inside
    cases todo with
    | nil =>
      rw [reconstructTable, reconstruct_nil]
      rfl
    | cons c cs =>
      rw [reconstructTable, reconstruct_cons]
      cases found : (c :: cs).find? (readyIn (outputs (c :: cs))) with
      | none => rfl
      | some d =>
        dsimp only
        have member := List.mem_of_find?_eq_some found
        rw [← view_set table d.out _ (inside d member)]
        apply ih
        · have shorter : ((c :: cs).filter fun e => e.out != d.out).length < (c :: cs).length :=
            List.length_filter_lt_length_iff_exists.mpr ⟨d, member, by simp⟩
          omega
        · intro e he
          rw [Array.size_setIfInBounds]
          exact inside e (List.mem_filter.mp he).1

private theorem out_le_fold (cs : List (Constraint s)) (m : Nat) :
    m ≤ cs.foldl (fun m c => max m c.out) m ∧ ∀ c ∈ cs, c.out ≤ cs.foldl (fun m c => max m c.out) m := by
  induction cs generalizing m with
  | nil => exact ⟨Nat.le_refl m, fun c hc => nomatch hc⟩
  | cons d ds ih =>
    obtain ⟨grows, covers⟩ := ih (max m d.out)
    refine ⟨Nat.le_trans (Nat.le_max_left m d.out) grows, fun c hc => ?_⟩
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Nat.le_trans (Nat.le_max_right m c.out) grows
    · exact covers c hc

section Solve
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

/-- A variable or an atom: a term that only itself equals modulo B. -/
private def simple : Term s → Bool
  | .var _ | .atom _ => true
  | _ => false

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
private theorem simple_alone {t u : Term s} (st : simple t = true) (h : EquivB t u) : u = t := by
  have root := h.head_eq
  cases t <;> cases u <;> simp_all [Model.eval, headModel, simple]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] in
private theorem flatten_classes (f : s.ACSym) (t : Term s) :
    Cancellation.flatten f t = (ACRepresentation.flatten f t).map Cancellation.classOf := by
  induction t with
  | var | atom | free | comm => rfl
  | ac g a b ia ib =>
    by_cases same : f = g
    · subst same
      rw [Cancellation.flatten_ac, ia, ib]
      simp [ACRepresentation.flatten]
    · simp [Cancellation.flatten, ACRepresentation.flatten, same]

open Classical in
private theorem count_simple {t : Term s} (st : simple t = true) (l : List (Term s)) :
    l.count t = (l.map Cancellation.classOf).count (Cancellation.classOf t) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have same : (x = t) ↔ (Cancellation.classOf x = Cancellation.classOf t) :=
      ⟨fun e => e ▸ rfl, fun e => simple_alone st (EquivB.symm (Quotient.exact e))⟩
    simp only [List.map_cons, List.count_cons, ih, beq_iff_eq, same]

/-- A product of variables and atoms equals a term modulo B exactly when the
term has the same operands in some order. -/
private theorem simple_product (f : s.ACSym) (a b : Term s)
    (plain : ∀ x ∈ ACRepresentation.flatten f a, simple x = true) :
    (ACRepresentation.flatten f a).Perm (ACRepresentation.flatten f b) ↔ EquivB a b := by
  constructor
  · intro perm
    obtain ⟨u, hu, eu⟩ := ACRepresentation.flatten_correct f a
    obtain ⟨w, hw, ew⟩ := ACRepresentation.flatten_correct f b
    exact eu.symm.trans ((ACRepresentation.decode_perm f perm u w hu hw).trans ew)
  · intro eq
    have classes : ((ACRepresentation.flatten f a).map Cancellation.classOf).Perm
        ((ACRepresentation.flatten f b).map Cancellation.classOf) := by
      rw [← flatten_classes, ← flatten_classes]
      exact Cancellation.flatten_equiv f eq
    apply List.perm_iff_count.mpr
    intro t
    by_cases st : simple t = true
    · classical
      have left := count_simple st (ACRepresentation.flatten f a)
      have right := count_simple st (ACRepresentation.flatten f b)
      have same := classes.count_eq (Cancellation.classOf t)
      exact left.trans (same.trans right.symm)
    · have outA : t ∉ ACRepresentation.flatten f a := fun h => st (plain t h)
      have outB : t ∉ ACRepresentation.flatten f b := by
        intro h
        obtain ⟨x, hx, ex⟩ := List.mem_map.mp
          (classes.mem_iff.mpr (List.mem_map_of_mem (f := Cancellation.classOf) h))
        have alone := simple_alone (plain x hx) (Quotient.exact ex)
        exact st (alone ▸ plain x hx)
      rw [List.count_eq_zero.mpr outA, List.count_eq_zero.mpr outB]

/-- Equality modulo B, answered at once for identical terms, and by comparing
the operands for a product of variables and atoms. The constructor installed
for a slot is syntactically the slot's value, so only competing definitions
reach a comparison of bags. -/
private def agree (a b : Term s) : Bool :=
  decide (a = b) ||
    match a with
    | .ac f _ _ =>
      let operands := ACRepresentation.flatten f a
      if operands.all simple then operands.isPerm (ACRepresentation.flatten f b)
      else ReferenceMatching.equal a b
    | _ => ReferenceMatching.equal a b

private theorem agree_iff (a b : Term s) : agree a b = true ↔ EquivB a b := by
  unfold agree
  rw [Bool.or_eq_true]
  constructor
  · rintro (same | rest)
    · exact of_decide_eq_true same ▸ .refl _
    · split at rest
      · next f x y =>
        dsimp only at rest
        split at rest
        · next plain =>
          exact (simple_product f _ b (List.all_eq_true.mp plain)).mp (List.isPerm_iff.mp rest)
        · exact (ReferenceMatching.equal_iff ..).mp rest
      · exact (ReferenceMatching.equal_iff ..).mp rest
  · intro eq
    right
    split
    · next f x y =>
      dsimp only
      split
      · next plain =>
        exact List.isPerm_iff.mpr ((simple_product f _ b (List.all_eq_true.mp plain)).mpr eq)
      · exact (ReferenceMatching.equal_iff ..).mpr eq
    · exact (ReferenceMatching.equal_iff ..).mpr eq

/-- A completed result is a mathematically complete raw family. If the
schematic valuation needs further unification among constructor definitions,
leave the query open for component solving. -/
def reconstructOf (q : System s) : Option (List (UnifierSorts.Template s)) :=
  match (reconstruct q.constraints (fun i => .var ⟨i,.msg⟩)).val with
  | none => some []
  | some row =>
    if q.constraints.all (fun c => agree (row c.out) (c.term row))
    then some [project q row] else none

/-- `reconstructOf` with the valuation kept in a table of the slots. -/
private def reconstructOfTabled (q : System s) : Option (List (UnifierSorts.Template s)) :=
  let size := q.constraints.foldl (fun m c => max m c.out) 0 + 1
  match reconstructTable q.constraints.length q.constraints
      (Array.ofFn (n := size) fun i => .var ⟨i.val,.msg⟩) with
  | none => some []
  | some table =>
    let row := view table
    if q.constraints.all (fun c => agree (row c.out) (c.term row))
    then some [project q row] else none

@[csimp] private theorem reconstructOf_eq_tabled : @reconstructOf = @reconstructOfTabled := by
  funext s _ _ _ _ q
  have start (n : Nat) : view (Array.ofFn (n := n) fun i => (.var ⟨i.val,.msg⟩ : Term s)) =
      fun i => .var ⟨i,.msg⟩ := by
    funext i
    unfold view
    split
    · simp
    · rfl
  have same := reconstructTable_eq q.constraints.length q.constraints
    (Array.ofFn (n := q.constraints.foldl (fun m c => max m c.out) 0 + 1)
      fun i => (.var ⟨i.val,.msg⟩ : Term s)) (Nat.le_refl _) (fun c hc => by
      have := (out_le_fold q.constraints 0).2 c hc
      simp only [Array.size_ofFn]
      omega)
  rw [start] at same
  unfold reconstructOf reconstructOfTabled
  dsimp only
  rw [← same]
  cases reconstructTable q.constraints.length q.constraints
      (Array.ofFn (n := q.constraints.foldl (fun m c => max m c.out) 0 + 1)
        fun i => (.var ⟨i.val,.msg⟩ : Term s)) <;> rfl

def reconstruct? (p : Problem s) : Option (List (UnifierSorts.Template s)) :=
  reconstructOf (purify p)

theorem reconstruct_correct {p : Problem s} {rows} (result : reconstruct? p = some rows) :
    UnifierSorts.CompleteTemplates p rows := by
  let q := purify p
  let r := reconstruct q.constraints (fun i => .var ⟨i,.msg⟩)
  have survives (ρ : Substitution s) (sol : p.Solves ρ) :
      ∃ row, r.val = some row ∧ ∃ μ, ∀ v, p.Occurs v →
        EquivB (ρ.image v) (((project q row) v).subst μ) := by
    obtain ⟨V,hV,agree⟩ := extend_solution p ρ.image sol
    let μ := fun (w : Variable) => V w.id
    obtain ⟨row,hr,hrow⟩ := r.property.covers V μ hV (fun i => .refl _)
    exact ⟨row,hr,μ,fun v hv => (agree v hv).trans (hrow _)⟩
  unfold reconstruct? reconstructOf at result
  change (match r.val with
    | none => some []
    | some row => if q.constraints.all (fun c => agree (row c.out) (c.term row))
      then some [project q row] else none) = some rows at result
  cases hr : r.val with
  | none =>
    simp [hr] at result
    subst rows
    refine ⟨by simp,fun ρ h => ?_⟩
    obtain ⟨_,bad,_⟩ := survives ρ h
    simp [hr] at bad
  | some row =>
    simp only [hr] at result
    split at result
    next ok =>
      cases result
      have model : q.Model row := fun c hc =>
        (agree_iff ..).mp (List.all_eq_true.mp ok c hc)
      refine ⟨?_,?_⟩
      · intro θ hθ
        obtain rfl := List.mem_singleton.mp hθ
        exact project_solves p model
      · intro ρ h
        obtain ⟨r',same,μ,agree⟩ := survives ρ h
        rw [hr] at same
        cases same
        exact ⟨_,List.mem_singleton_self _,μ,agree⟩
    next => contradiction

/-- A structural coverage guarantee independent of a successful run. When definitions of each slot
agree under every valuation, reconstruction produces a most general row or
refutes a constructor cycle, including across different operators. -/
theorem reconstructs_agreeing (p : Problem s)
    (h : AgreeingDefinitions (purify p).constraints) : (reconstruct? p).isSome := by
  let q := purify p
  let r := reconstruct q.constraints (fun i => .var ⟨i,.msg⟩)
  change (match r.val with
    | none => some []
    | some row =>
      if q.constraints.all (fun c => agree (row c.out) (c.term row)) then
        some [project q row]
      else none).isSome = true
  cases hr : r.val with
  | none => rfl
  | some row =>
    have ok := List.all_eq_true.mpr (fun c hc => (agree_iff ..).mpr
      (r.property.solves row hr h c hc))
    simp [ok]

theorem reconstructs_singleDefinition (p : Problem s)
    (h : SingleDefinition (purify p).constraints) : (reconstruct? p).isSome :=
  reconstructs_agreeing p (fun c hc d hd eq _ => (h c hc d hd eq) ▸ EquivB.refl _)

/-- The empty problem has one reconstructed template. -/
theorem reconstruct_empty : ∃ x, reconstruct? (s := s) [] = some [x] := by
  have empty : (purify (s := s) []).constraints = [] := by simp [purify, inventory]
  unfold reconstruct? reconstructOf
  rw [empty, reconstruct_nil]
  exact ⟨_, rfl⟩

end Solve

namespace System
variable [DecidableEq s.ACSym]

private def coordinate (f : s.ACSym) (i : Nat) : Variable := ⟨i,s.acSort f⟩

private def asRow (f : s.ACSym) : Constraint s → Option ACSystem.Row
  | .ac n g a b => if f = g then
      some ⟨⟨coordinate f n,[]⟩,⟨coordinate f a,[coordinate f b]⟩⟩ else none
  | _ => none

/-- The equations of one AC operator form a single homogeneous system. Reused
slots keep the same coordinate on either side and across equations. -/
def rows (q : System s) (f : s.ACSym) : List ACSystem.Row := q.constraints.filterMap (asRow f)

def remaining (q : System s) (f : s.ACSym) : List (Constraint s) :=
  q.constraints.filter (fun c => (asRow f c).isNone)

theorem component_iff (q : System s) (f : s.ACSym) (V : Nat → Term s) :
    q.Model V ↔
      (∀ e ∈ ACSystem.problem f (q.rows f),
        EquivB (e.lhs.subst (fun v => V v.id)) (e.rhs.subst (fun v => V v.id))) ∧
      ∀ c ∈ q.remaining f, c.Holds V := by
  have represents (c : Constraint s) (r : ACSystem.Row) (h : asRow f c = some r) :
      c.Holds V ↔ EquivB ((r.equation f).lhs.subst (fun v => V v.id))
        ((r.equation f).rhs.subst (fun v => V v.id)) := by
    cases c with
    | atom | free | comm => contradiction
    | ac n g a b =>
      simp [asRow] at h
      obtain ⟨rfl,rfl⟩ := h
      rfl
  constructor
  · intro h
    refine ⟨?_,fun c hc => h c (List.mem_filter.mp hc).1⟩
    intro e he
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp he
    obtain ⟨c,hc,eq⟩ := List.mem_filterMap.mp hr
    exact (represents c r eq).mp (h c hc)
  · rintro ⟨hm,rest⟩ c hc
    cases h : asRow f c with
    | none => exact rest c (List.mem_filter.mpr ⟨hc,by simp [h]⟩)
    | some r =>
      exact (represents c r h).mpr (hm _ (List.mem_map_of_mem (List.mem_filterMap.mpr ⟨c,hc,h⟩)))

private theorem sorted (q : System s) (f : s.ACSym) :
    ∀ v ∈ ACSystem.variables (q.rows f), v.sort = s.acSort f := by
  intro v hv
  obtain ⟨r,hr,hv⟩ := List.mem_flatMap.mp hv
  obtain ⟨c,_,eq⟩ := List.mem_filterMap.mp hr
  cases c with
  | atom | free | comm => contradiction
  | ac _ g a b =>
    simp [asRow] at eq
    obtain ⟨rfl,rfl⟩ := eq
    simp [ACSystem.Side.vars] at hv
    rcases hv with rfl | rfl | rfl <;> rfl

def solveComponent (q : System s) (f : s.ACSym) (avoid : List Variable) :=
  ACSystem.Reference.solve f (q.rows f) (sorted q f) avoid

theorem component_correct (q : System s) (f : s.ACSym) (avoid : List Variable) :
    (Outcome.complete (q.solveComponent f avoid)).CorrectIn (ACSystem.problem f (q.rows f)) avoid :=
  ACSystem.Reference.correct f (q.rows f) (sorted q f) avoid

end System
end Tamarin.MixedUnification
