import Tamarin.MixedComponentSearch
import Tamarin.MixedFlatPurification

/-! The homogeneous solver works in one sort. Purified slots represent raw
terms, including kind-level subterms of a sorted unification query. Run the
component search in a copy of the signature with one common sort and restore
the source sorts only after projecting the shared slot valuation. -/
namespace Tamarin.MixedUnification.ComponentEncoding
variable {s : Signature}

abbrev uniform (s : Signature) : Signature := { s with
  inputSort := fun _ _ => .msg, outputSort := fun _ => .msg, cSort := fun _ => .msg,
  acSort := fun _ => .msg, atomSort := fun _ => .msg }

private def number : SortId → Nat
  | .pub => 0 | .fresh => 1 | .msg => 2 | .node => 3 | .nat => 4

def original (v : Variable) : Variable :=
  ⟨v.id / 5,match v.id % 5 with | 0 => .pub | 1 => .fresh | 2 => .msg | 3 => .node | _ => .nat⟩

def name (v : Variable) : Variable := ⟨v.id * 5 + number v.sort,.msg⟩

theorem original_name (v : Variable) : original (name v) = v := by
  obtain ⟨i,k⟩ := v
  cases k <;> simp [original,name,number,Nat.add_mod] <;> omega

def encode : Term s → Term (uniform s)
  | .var v => .var (name v)
  | .atom a => .atom a
  | .free f args => .free f fun i => encode (args i)
  | .comm f a b => .comm f (encode a) (encode b)
  | .ac f a b => .ac f (encode a) (encode b)

theorem encode_sorted (t : Term s) : HasSort (encode t) .msg := by
  induction t with
  | var => exact .var _
  | atom => exact .atom _
  | free f xs ih => exact .free _ _ ih
  | comm f a b ha hb => exact .comm _ _ _ ha hb
  | ac f a b ha hb => exact .ac _ _ _ ha hb

theorem encode_equiv {a b : Term s} (h : EquivB a b) : EquivB (encode a) (encode b) := by
  induction h with
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih hj => exact ih.trans hj
  | free _ _ _ _ ih => exact .free _ _ _ ih
  | comm_congr _ _ _ ih hj => exact .comm_congr _ ih hj
  | ac_congr _ _ _ ih hj => exact .ac_congr _ ih hj
  | comm_swap => exact .comm_swap _ _ _
  | ac_swap => exact .ac_swap _ _ _
  | ac_assoc => exact .ac_assoc _ _ _ _

def read (vars : Variable → Term s) : Term (uniform s) → Term s
  | .var v => vars v
  | .atom a => .atom a
  | .free f args => .free f fun i => read vars (args i)
  | .comm f a b => .comm f (read vars a) (read vars b)
  | .ac f a b => .ac f (read vars a) (read vars b)

theorem read_equiv (vars : Variable → Term s) {a b} (h : EquivB a b) :
    EquivB (read vars a) (read vars b) := by
  induction h with
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih hj => exact ih.trans hj
  | free _ _ _ _ ih => exact .free _ _ _ ih
  | comm_congr _ _ _ ih hj => exact .comm_congr _ ih hj
  | ac_congr _ _ _ ih hj => exact .ac_congr _ ih hj
  | comm_swap => exact .comm_swap _ _ _
  | ac_swap => exact .ac_swap _ _ _
  | ac_assoc => exact .ac_assoc _ _ _ _

theorem read_encode (t : Term s) : read (.var ∘ original) (encode t) = t := by
  induction t with
  | var v => simp [encode,read,original_name]
  | atom => rfl
  | free f xs ih => exact congrArg (Term.free f) (funext ih)
  | ac _ _ _ ih hj | comm _ _ _ ih hj => simp [encode,read,ih,hj]

theorem read_subst (vars : Variable → Term s) (δ : Substitution (uniform s)) (t) :
    read vars (δ.apply t) = (read Term.var t).subst (fun w => read vars (δ.image w)) := by
  induction t with
  | var | atom => rfl
  | free f xs ih => apply congrArg (Term.free (sig := s) f); funext i; exact ih i
  | ac f a b ih hj | comm f a b ih hj =>
    simp only [Substitution.apply,Term.subst,read] at *; rw [ih,hj]

private def slot (i : Nat) : Variable := ⟨i,.msg⟩
private def equation (c : Constraint s) : Equation (uniform s) :=
  ⟨.var (slot c.out),match c with
    | .atom _ a => .atom a
    | .free _ f args => .free f fun j => .var (slot (args j))
    | .comm _ f i j => .comm f (.var (slot i)) (.var (slot j))
    | .ac _ f i j => .ac f (.var (slot i)) (.var (slot j))⟩

/-- `equation` with the arguments of a free application stored. -/
private def equationStored (c : Constraint s) : Equation (uniform s) :=
  match c with
  | .atom n a => ⟨.var (slot n), .atom a⟩
  | .free n f args =>
    let stored : Vector (Term (uniform s)) (s.arity f) := Vector.ofFn fun j => .var (slot (args j))
    ⟨.var (slot n), .free f fun j => stored[j]⟩
  | .comm n f i j => ⟨.var (slot n), .comm f (.var (slot i)) (.var (slot j))⟩
  | .ac n f i j => ⟨.var (slot n), .ac f (.var (slot i)) (.var (slot j))⟩

@[csimp] private theorem equation_eq_stored : @equation = @equationStored := by
  funext s c
  cases c <;> simp [equation, equationStored, Constraint.out]

def reserve (obs : List Variable) (V : Nat → Term s) : Substitution (uniform s) where
  support := obs
  image v := if v ∈ obs ∧ v.sort = .msg then encode (V v.id) else .var v
  outside := by intro v hv; simp [hv]
  sorted := by intro v; split <;> rename_i h; exact h.2 ▸ encode_sorted _; exact .var _

private theorem reserve_solves (q : System s) {V} (model : q.Model V) (obs : List Variable)
    (includes : ∀ v, Problem.Occurs (q.constraints.map equation) v → v ∈ obs) :
    Problem.Solves (q.constraints.map equation) (reserve obs V) := by
  intro e he
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp he
  let full := fun (v : Variable) => encode (V v.id)
  have same (t : Term (uniform s)) (side : t = (equation c).lhs ∨ t = (equation c).rhs)
      (msg : ∀ v, t.Occurs v → v.sort = .msg) :
      (reserve obs V).apply t = t.subst full := by
    apply Term.subst_eq_of_agree
    intro v hv
    have live := includes v ⟨equation c,List.mem_map_of_mem hc,by rcases side with rfl|rfl <;> simp_all⟩
    simp [reserve,full,live,msg v hv]
  have typed (v : Variable) (h : (equation c).rhs.Occurs v) : v.sort = .msg := by
    cases c with
    | atom => exact False.elim h
    | free _ _ _ => obtain ⟨_,rfl⟩ := h; rfl
    | comm | ac => rcases h with rfl|rfl <;> rfl
  rw [same _ (.inl rfl) (fun v hv => (show v = slot c.out from hv) ▸ rfl),
      same _ (.inr rfl) typed]
  have h := encode_equiv (model c hc)
  cases c <;> exact h

private theorem read_model (q : System s) {σ : Substitution (uniform s)}
    (h : Problem.Solves (q.constraints.map equation) σ) :
    q.Model (fun i => read Term.var (σ.image (slot i))) := by
  intro c hc
  have eq := read_equiv (s := s) Term.var (h (equation c) (List.mem_map_of_mem hc))
  cases c <;> exact eq

private def heads (q : System s) [DecidableEq s.ACSym] : List s.ACSym :=
  (q.constraints.filterMap fun c => match c with | .ac _ f .. => some f | _ => none).eraseDups

variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

private def compiledProblem (q : System s) : Problem (uniform s) := q.constraints.map equation

private def slotTerm (k : Term s → Nat) (t : Term s) : Term (uniform s) := .var (slot (k t))

/-- A product over the slots of its operands, each with its multiplicity. -/
private def flatSide (k : Term s → Nat) (f : s.ACSym) (t : Term s) : Option (Term (uniform s)) :=
  ACRepresentation.decode (sig := uniform s) f ((ACRepresentation.flatten f t).map (slotTerm k))

/-- The definition of a term over the slots. A product is defined once, over
its operands with their multiplicities. -/
private def flatEquation (k : Term s → Nat) : Term s → Option (Equation (uniform s))
  | .var _ => none
  | t@(.atom a) => some ⟨slotTerm k t, .atom a⟩
  | t@(.free f xs) =>
    let stored : Vector (Term (uniform s)) (s.arity f) := Vector.ofFn fun j => slotTerm k (xs j)
    some ⟨slotTerm k t, .free f fun j => stored[j]⟩
  | t@(.comm f a b) => some ⟨slotTerm k t, .comm f (slotTerm k a) (slotTerm k b)⟩
  | t@(.ac f _ _) => (flatSide k f t).map fun product => ⟨slotTerm k t, product⟩

/-- The head of an equation between two products at one head. Such an
equation is stated between the two flat products, and neither side needs a
slot on its account: the value of the whole product is as large as all its
operands together, and nothing else reads it. -/
private def direct (e : Equation s) : Option s.ACSym :=
  match e.lhs, e.rhs with
  | .ac f _ _, .ac g _ _ => if f = g then some f else none
  | _, _ => none

/-- The terms that receive a definition on account of an equation. -/
private def named (e : Equation s) : List (Term s) :=
  match direct e with
  | some f => Flat.exposed (some f) e.lhs ++ Flat.exposed (some f) e.rhs
  | none => Flat.exposed none e.lhs ++ Flat.exposed none e.rhs

private def directEquation (k : Term s → Nat) (e : Equation s) : Option (Equation (uniform s)) :=
  match direct e with
  | some f => do return ⟨← flatSide k f e.lhs, ← flatSide k f e.rhs⟩
  | none => none

/-- The definitions of the terms that an equation, a free argument or a
product at another head can observe, and the equations between products. -/
private def flatProblem (p : Problem s) (k : Term s → Nat) : Problem (uniform s) :=
  (Buckets.dedup bucketKey (p.flatMap named)).filterMap (flatEquation k) ++ p.filterMap (directEquation k)

private def observationsOn (compiled : Problem (uniform s)) (q : System s) (terms : List (Term s)) :
    List Variable :=
  Buckets.dedup Variable.id (compiled.variables ++ terms.map (fun t => slot (q.slot t)))

/-- The variables, and the terms whose slot the compiled problem mentions. The
slot of any other term occurs in no equation of the search, so observing it
would only add an unconstrained variable to every leaf. -/
private def watched (compiled : Problem (uniform s)) (q : System s) (terms : List (Term s)) :
    List (Term s) :=
  let ids := compiled.variables.map Variable.id
  let marks := ids.foldl (fun acc i => acc.setIfInBounds i true)
    (Array.replicate (ids.foldl max 0 + 1) false)
  terms.filter fun t => match t with
    | .var _ => true
    | _ => marks.getD (q.slot t) false

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
private theorem watched_subset (compiled : Problem (uniform s)) (q : System s) (terms : List (Term s))
    {t : Term s} (h : t ∈ watched compiled q terms) : t ∈ terms :=
  (List.mem_filter.mp h).1

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
private theorem watched_var (compiled : Problem (uniform s)) (q : System s) (terms : List (Term s))
    {v : Variable} (h : .var v ∈ terms) : .var v ∈ watched compiled q terms :=
  List.mem_filter.mpr ⟨h, rfl⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
private theorem decode_map {a b : Signature} (f : a.ACSym) (g : b.ACSym) (h : Term a → Term b)
    (step : ∀ x y, h (.ac f x y) = .ac g (h x) (h y)) (l : List (Term a)) :
    ACRepresentation.decode g (l.map h) = (ACRepresentation.decode f l).map h := by
  cases l with
  | nil => rfl
  | cons x xs =>
    simp only [List.map_cons, ACRepresentation.decode, Option.map_some]
    congr 1
    induction xs generalizing x with
    | nil => rfl
    | cons y ys ih => simp only [List.map_cons, ACRepresentation.fold, step, ih]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
private theorem decode_occurs {a : Signature} (f : a.ACSym) (l : List (Term a)) (r : Term a)
    (h : ACRepresentation.decode f l = some r) (t : Term a) (ht : t ∈ l) (v : Variable)
    (occ : t.Occurs v) : r.Occurs v := by
  cases l with
  | nil => cases ht
  | cons x xs =>
    obtain rfl : ACRepresentation.fold f x xs = r := by simpa [ACRepresentation.decode] using h
    induction xs generalizing x with
    | nil =>
      obtain rfl := List.mem_singleton.mp ht
      exact occ
    | cons y ys ih =>
      rcases List.mem_cons.mp ht with rfl | ht
      · exact .inl occ
      · exact .inr (ih y ht rfl)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] in
private theorem flatSide_some (k : Term s → Nat) (f : s.ACSym) (t : Term s) :
    ∃ product, flatSide k f t = some product := by
  unfold flatSide
  cases hl : ACRepresentation.flatten f t with
  | nil => exact (ACRepresentation.flatten_nonempty f _ hl).elim
  | cons x xs => exact ⟨_, rfl⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] in
/-- A solved flat product reads as the fold of the values of its operands. -/
private theorem side_read (k : Term s → Nat) (σ : Substitution (uniform s)) (f : s.ACSym) (t : Term s)
    (product : Term (uniform s)) (shape : flatSide k f t = some product) :
    ACRepresentation.decode f ((ACRepresentation.flatten f t).map
      fun u => read Term.var (σ.image (slot (k u)))) = some (read Term.var (σ.apply product)) := by
  have images := decode_map (a := uniform s) (b := s) f f (fun t => read Term.var (σ.apply t))
    (fun _ _ => rfl) ((ACRepresentation.flatten f t).map (slotTerm k))
  unfold flatSide at shape
  rw [shape, List.map_map] at images
  exact images

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] in
/-- A flat product under the reserved valuation is the encoded fold of the
values of its operands. -/
private theorem side_reserve (k : Term s → Nat) (obs : List Variable) (V : Nat → Term s)
    (f : s.ACSym) (t : Term s) (product : Term (uniform s)) (shape : flatSide k f t = some product)
    (live : ∀ v, product.Occurs v → v ∈ obs) :
    ∃ r, ACRepresentation.decode f ((ACRepresentation.flatten f t).map fun u => V (k u)) = some r ∧
      (reserve obs V).apply product = encode r := by
  have at_slot (i : Nat) (h : slot i ∈ obs) : (reserve obs V).image (slot i) = encode (V i) :=
    ite_eq_left ⟨h, rfl⟩
  unfold flatSide at shape
  cases folded : ACRepresentation.decode f ((ACRepresentation.flatten f t).map fun u => V (k u)) with
  | none =>
    cases hl : ACRepresentation.flatten f t with
    | nil => exact (ACRepresentation.flatten_nonempty f _ hl).elim
    | cons x xs => simp [hl, ACRepresentation.decode] at folded
  | some r =>
    refine ⟨r, rfl, ?_⟩
    have applied := decode_map (a := uniform s) (b := uniform s) f f (reserve obs V).apply
      (fun _ _ => rfl) ((ACRepresentation.flatten f t).map (slotTerm k))
    rw [shape, List.map_map] at applied
    have encoded := decode_map (a := s) (b := uniform s) f f encode (fun _ _ => rfl)
      ((ACRepresentation.flatten f t).map fun u => V (k u))
    rw [folded, List.map_map] at encoded
    have same : (ACRepresentation.flatten f t).map ((reserve obs V).apply ∘ slotTerm k) =
        (ACRepresentation.flatten f t).map (encode ∘ fun u => V (k u)) := by
      apply List.map_congr_left
      intro w hw
      have occ : product.Occurs (slot (k w)) :=
        decode_occurs (a := uniform s) f _ product shape (slotTerm k w)
          (List.mem_map_of_mem hw) (slot (k w)) rfl
      exact at_slot _ (live _ occ)
    rw [same, encoded] at applied
    exact (Option.some.inj applied).symm

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] in
/-- A solution of the definition of a term makes the term defined. -/
private theorem flat_defined (k : Term s → Nat) (σ : Substitution (uniform s)) (u : Term s)
    (solved : ∀ e, flatEquation k u = some e → EquivB (σ.apply e.lhs) (σ.apply e.rhs)) :
    Flat.Defined (fun t => read Term.var (σ.image (slot (k t)))) u := by
  cases u with
  | var => trivial
  | atom a => exact read_equiv (s := s) Term.var (solved _ rfl)
  | free f xs =>
    have eq := read_equiv (s := s) Term.var (solved _ rfl)
    simpa only [Flat.Defined, slotTerm, Substitution.apply, Term.subst, read, Fin.getElem_fin,
      Vector.getElem_ofFn] using eq
  | comm f a b => exact read_equiv (s := s) Term.var (solved _ rfl)
  | ac f a b =>
    obtain ⟨product, shape⟩ := flatSide_some k f (.ac f a b)
    have eq := read_equiv (s := s) Term.var (solved ⟨slotTerm k (.ac f a b), product⟩
      (by simp only [flatEquation, shape, Option.map_some]))
    exact ⟨_, side_read k σ f _ product shape, eq⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] in
/-- The values of a defined term solve its definition. -/
private theorem defined_flat (k : Term s → Nat) (obs : List Variable) (V : Nat → Term s) (u : Term s)
    (e : Equation (uniform s)) (he : flatEquation k u = some e)
    (live : ∀ v, e.lhs.Occurs v ∨ e.rhs.Occurs v → v ∈ obs)
    (d : Flat.Defined (fun t => V (k t)) u) :
    EquivB ((reserve obs V).apply e.lhs) ((reserve obs V).apply e.rhs) := by
  have at_slot (i : Nat) (h : slot i ∈ obs) : (reserve obs V).image (slot i) = encode (V i) :=
    ite_eq_left ⟨h, rfl⟩
  cases u with
  | var => cases he
  | atom a =>
    obtain rfl : (⟨slotTerm k (.atom a), .atom a⟩ : Equation (uniform s)) = e := Option.some.inj he
    change EquivB ((reserve obs V).image (slot (k (.atom a)))) (.atom a)
    rw [at_slot _ (live _ (.inl rfl))]
    exact encode_equiv d
  | free f xs =>
    obtain rfl : (⟨slotTerm k (.free f xs), .free f fun j =>
        (Vector.ofFn fun j => slotTerm k (xs j))[j]⟩ : Equation (uniform s)) = e := Option.some.inj he
    have args : (fun j : Fin (s.arity f) => (reserve obs V).apply
        ((Vector.ofFn fun j => slotTerm k (xs j))[j])) = fun j => encode (V (k (xs j))) := by
      funext j
      simp only [Fin.getElem_fin, Vector.getElem_ofFn]
      exact at_slot _ (live _ (.inr ⟨j, by simp [slotTerm, Term.Occurs]⟩))
    change EquivB ((reserve obs V).image (slot (k (.free f xs))))
      (.free f fun j => (reserve obs V).apply ((Vector.ofFn fun j => slotTerm k (xs j))[j]))
    rw [at_slot _ (live _ (.inl rfl)), args]
    exact encode_equiv d
  | comm f a b =>
    obtain rfl : (⟨slotTerm k (.comm f a b), .comm f (slotTerm k a) (slotTerm k b)⟩ :
        Equation (uniform s)) = e := Option.some.inj he
    change EquivB ((reserve obs V).image (slot (k (.comm f a b))))
      (.comm f ((reserve obs V).image (slot (k a))) ((reserve obs V).image (slot (k b))))
    rw [at_slot _ (live _ (.inl rfl)), at_slot _ (live _ (.inr (.inl rfl))),
      at_slot _ (live _ (.inr (.inr rfl)))]
    exact encode_equiv d
  | ac f a b =>
    obtain ⟨product, shape⟩ := flatSide_some k f (.ac f a b)
    obtain rfl : (⟨slotTerm k (.ac f a b), product⟩ : Equation (uniform s)) = e := by
      simpa [flatEquation, shape] using he
    obtain ⟨r, folded, eq⟩ := d
    obtain ⟨r', folded', applied⟩ := side_reserve k obs V f _ product shape (fun v hv => live v (.inr hv))
    obtain rfl : r = r' := Option.some.inj (folded.symm.trans folded')
    change EquivB ((reserve obs V).image (slot (k (.ac f a b)))) ((reserve obs V).apply product)
    rw [at_slot _ (live _ (.inl rfl)), applied]
    exact encode_equiv eq

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] in
private theorem direct_shape {e : Equation s} {f : s.ACSym} (h : direct e = some f) :
    (∃ a b, e.lhs = .ac f a b) ∧ ∃ c d, e.rhs = .ac f c d := by
  unfold direct at h
  split at h
  · next g a b g' c d hl hr =>
    split at h
    · next same =>
      obtain rfl := Option.some.inj h
      exact ⟨⟨a, b, hl⟩, ⟨c, d, same ▸ hr⟩⟩
    · cases h
  · cases h

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] in
private theorem named_subterms {e : Equation s} {u : Term s} (h : u ∈ named e) :
    u ∈ subterms e.lhs ∨ u ∈ subterms e.rhs := by
  unfold named at h
  split at h <;> exact (List.mem_append.mp h).imp Flat.exposed_subterms Flat.exposed_subterms

/-- A problem over the slots that stands for the source problem: its
solutions project to source solutions, and the slot values of every source
solution solve it. -/
private structure Compiled (p : Problem s) where
  problem : Problem (uniform s)
  sound : ∀ σ : Substitution (uniform s), problem.Solves σ →
    RigidBranches.Solves p (project (purify p) fun i => read Term.var (σ.image (slot i)))
  cover : ∀ (obs : List Variable) (V : Nat → Term s) (ρ : UnifierSorts.Template s),
    (purify p).Model V → (∀ t ∈ inventory p, EquivB (t.subst ρ) (V ((purify p).slot t))) →
    (∀ v, problem.Occurs v → v ∈ obs) → problem.Solves (reserve obs V)

/-- One definition per binary node. -/
private def binary (p : Problem s) : Compiled p where
  problem := compiledProblem (purify p)
  sound _ solves := project_solves _ (read_model (purify p) solves)
  cover obs _ _ model _ live := reserve_solves (purify p) model obs live

/-- One definition per observable term, with flat products. -/
private def flat (p : Problem s) : Compiled p where
  problem := flatProblem p (purify p).slot
  sound σ solves := by
    let k := (purify p).slot
    let W := fun t => read Term.var (σ.image (slot (k t)))
    have defined (e) (he : e ∈ p) (u : Term s) (hu : u ∈ named e) : Flat.Defined W u := by
      apply flat_defined
      intro eq heq
      exact solves eq (List.mem_append_left _ (List.mem_filterMap.mpr ⟨u, Buckets.mem_dedup.mpr
        (List.mem_flatMap.mpr ⟨e, he, hu⟩), heq⟩))
    intro e he
    cases hd : direct e with
    | none =>
      have inside (u) (hu : u ∈ Flat.exposed none e.lhs ++ Flat.exposed none e.rhs) : u ∈ named e := by
        simpa only [named, hd] using hu
      have left := (Flat.interpret W e.lhs none
        (fun u hu => defined e he u (inside u (List.mem_append_left _ hu)))).1 (fun _ _ _ _ h => nomatch h)
      have right := (Flat.interpret W e.rhs none
        (fun u hu => defined e he u (inside u (List.mem_append_right _ hu)))).1 (fun _ _ _ _ h => nomatch h)
      have same : W e.lhs = W e.rhs := by simp only [W, k, slot_sides p e he]
      rw [same] at left
      exact left.symm.trans right
    | some f =>
      have inside (u) (hu : u ∈ Flat.exposed (some f) e.lhs ++ Flat.exposed (some f) e.rhs) :
          u ∈ named e := by
        simpa only [named, hd] using hu
      have left := (Flat.interpret W e.lhs (some f)
        (fun u hu => defined e he u (inside u (List.mem_append_left _ hu)))).2 f rfl
      have right := (Flat.interpret W e.rhs (some f)
        (fun u hu => defined e he u (inside u (List.mem_append_right _ hu)))).2 f rfl
      obtain ⟨l, hl⟩ := flatSide_some k f e.lhs
      obtain ⟨r, hr⟩ := flatSide_some k f e.rhs
      have stated : (⟨l, r⟩ : Equation (uniform s)) ∈ flatProblem p k :=
        List.mem_append_right _ (List.mem_filterMap.mpr ⟨e, he, by simp [directEquation, hd, hl, hr]⟩)
      have eq := read_equiv (s := s) Term.var (solves _ stated)
      obtain ⟨a, ha, ea⟩ := Flat.subst_flatten f e.lhs (fun v => W (.var v))
      obtain ⟨b, hb, eb⟩ := Flat.subst_flatten f e.rhs (fun v => W (.var v))
      have fromLeft := Flat.decode_congr f _ W (·.subst fun v => W (.var v)) left
        (side_read k σ f e.lhs l hl) ha
      have fromRight := Flat.decode_congr f _ W (·.subst fun v => W (.var v)) right
        (side_read k σ f e.rhs r hr) hb
      exact ea.symm.trans (fromLeft.symm.trans (eq.trans (fromRight.trans eb)))
  cover obs V ρ _ values live := by
    intro eq heq
    rcases List.mem_append.mp heq with heq' | heq'
    · obtain ⟨u, hu, hd⟩ := List.mem_filterMap.mp heq'
      obtain ⟨e, he, side⟩ := List.mem_flatMap.mp (Buckets.mem_dedup.mp hu)
      have below := named_subterms side
      apply defined_flat (purify p).slot obs V u eq hd
      · exact fun v hv => live v ⟨eq, heq, hv⟩
      · apply Flat.defined_of_values (fun t => V ((purify p).slot t)) ρ
        intro w hw
        exact values w (subterm_inventory he (below.imp (subterms_trans · w hw) (subterms_trans · w hw)))
    · obtain ⟨e, he, stated⟩ := List.mem_filterMap.mp heq'
      cases hd : direct e with
      | none => simp [directEquation, hd] at stated
      | some f =>
        obtain ⟨l, hl⟩ := flatSide_some (purify p).slot f e.lhs
        obtain ⟨r, hr⟩ := flatSide_some (purify p).slot f e.rhs
        obtain rfl : (⟨l, r⟩ : Equation (uniform s)) = eq := by
          simpa [directEquation, hd, hl, hr] using stated
        obtain ⟨a, ha, la⟩ := side_reserve (purify p).slot obs V f e.lhs l hl
          (fun v hv => live v ⟨_, heq, .inl hv⟩)
        obtain ⟨b, hb, rb⟩ := side_reserve (purify p).slot obs V f e.rhs r hr
          (fun v hv => live v ⟨_, heq, .inr hv⟩)
        change EquivB ((reserve obs V).apply l) ((reserve obs V).apply r)
        rw [la, rb]
        apply encode_equiv
        obtain ⟨a', ha', ea⟩ := Flat.subst_flatten f e.lhs ρ
        obtain ⟨b', hb', eb⟩ := Flat.subst_flatten f e.rhs ρ
        have operand (side : Term s) (inSide : side = e.lhs ∨ side = e.rhs) :
            ∀ u ∈ ACRepresentation.flatten f side, EquivB (u.subst ρ) (V ((purify p).slot u)) := by
          intro u hu
          apply values
          rcases inSide with rfl | rfl
          · exact subterm_inventory he (.inl (Flat.flatten_subterms f hu))
          · exact subterm_inventory he (.inr (Flat.flatten_subterms f hu))
        have fromLeft := Flat.decode_congr f _ (·.subst ρ) (fun u => V ((purify p).slot u))
          (operand e.lhs (.inl rfl)) ha' ha
        have fromRight := Flat.decode_congr f _ (·.subst ρ) (fun u => V ((purify p).slot u))
          (operand e.rhs (.inr rfl)) hb' hb
        have roots : EquivB (e.lhs.subst ρ) (e.rhs.subst ρ) := by
          have lhs := values e.lhs (subterm_inventory he (.inl (Flat.subterms_self _)))
          have rhs := values e.rhs (subterm_inventory he (.inr (Flat.subterms_self _)))
          rw [slot_sides p e he] at lhs
          exact lhs.trans rhs.symm
        exact fromLeft.symm.trans (ea.trans (roots.trans (eb.symm.trans fromRight)))

/-- An input-side sufficient condition. It inspects the constraints in the
complete joint AC frontier and does not require a successful unifier result. -/
def ConstructorFrontier (p : Problem s) : Prop :=
  let q := purify p
  let compiled := (flat p).problem
  let obs := observationsOn compiled q (watched compiled q (inventory p))
  ∀ c ∈ (ComponentSearch.frontier (s := uniform s) (heads (s := s) q) compiled obs).val,
    ComponentSearch.ConstructorDecided c obs

/-- Slots of input variables of a proper subsort, with that sort. -/
private def narrowOf (q : System s) (p : Problem s) : List (Variable × SortId) :=
  p.variables.eraseDups.filterMap fun v =>
    if v.sort = .msg then none else some (slot (q.slot (.var v)), v.sort)

/-- Some term with this outer constructor has the sort. -/
private def headFits (k : SortId) : Head (uniform s) → Bool
  | .var _ => true
  | .atom a => Subsort.check (s.atomSort a) k
  | .free f => Subsort.check (s.outputSort f) k
  | .comm f => Subsort.check (s.cSort f) k
  | .ac f => Subsort.check (s.acSort f) k

/-- A sorted solution never gives the slot of a sorted variable a head whose
terms all lie outside that sort. -/
private def banOf (table : List (Variable × SortId)) (y : Variable) (h : Head (uniform s)) : Bool :=
  table.any fun z => z.1 == y && !headFits z.2 h

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
private theorem fits_encode (t : Term s) (k : SortId) (le : Subsort t.rootSort k) :
    headFits k ((headModel (uniform s)).eval Head.var (encode t)) = true := by
  cases t with
  | var => rfl
  | _ => exact (Subsort.check_iff ..).mpr le

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
private theorem ban_source (q : System s) (p : Problem s) {y : Variable} {h : Head (uniform s)}
    (hb : banOf (narrowOf q p) y h = true) :
    ∃ v, p.Occurs v ∧ y = slot (q.slot (.var v)) ∧ headFits v.sort h = false := by
  obtain ⟨z,hz,both⟩ := List.any_eq_true.mp hb
  obtain ⟨v,hv,eq⟩ := List.mem_filterMap.mp hz
  split at eq
  · cases eq
  · cases eq
    obtain ⟨same,misfit⟩ := Bool.and_eq_true_iff.mp both
    exact ⟨v,(p.mem_variables v).mp (List.mem_eraseDups.mp hv),(beq_iff_eq.mp same).symm,
      by simpa using misfit⟩

private theorem ban_observed (p : Problem s) (compiled : Problem (uniform s)) :
    ∀ y (h : Head (uniform s)), banOf (narrowOf (purify p) p) y h = true →
      y ∈ observationsOn compiled (purify p) (watched compiled (purify p) (inventory p)) := by
  intro y h hb
  obtain ⟨v,occ,rfl,-⟩ := ban_source _ p hb
  exact Buckets.mem_dedup.mpr (List.mem_append_right _
    (List.mem_map_of_mem (watched_var _ _ _ (var_in_inventory occ))))

abbrev SlotPair (s : Signature) := Term s × Term s

/-- Keep a request unless an already kept request is contained in it. -/
private def minimalInto {α : Type} [DecidableEq α] : List (List α) → List (List α) → List (List α)
  | kept, [] => kept
  | kept, x :: xs =>
    if kept.any (fun k => k.all (· ∈ x)) then minimalInto kept xs else minimalInto (x :: kept) xs

private theorem minimalInto_mem {α : Type} [DecidableEq α] (kept xs : List (List α)) :
    ∀ y ∈ minimalInto kept xs, y ∈ kept ∨ y ∈ xs := by
  induction xs generalizing kept with
  | nil => exact fun y h => .inl h
  | cons x xs ih =>
    intro y h
    simp only [minimalInto] at h
    split at h
    · exact (ih kept y h).imp id (List.mem_cons_of_mem _)
    · rcases ih _ y h with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact .inr List.mem_cons_self
        · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)

private theorem minimalInto_covers {α : Type} [DecidableEq α] (kept xs : List (List α)) :
    ∀ y, y ∈ kept ∨ y ∈ xs → ∃ k ∈ minimalInto kept xs, k ⊆ y := by
  induction xs generalizing kept with
  | nil =>
    rintro y (h | h)
    · exact ⟨y,h,fun _ => id⟩
    · cases h
  | cons x xs ih =>
    intro y h
    simp only [minimalInto]
    split
    next covered =>
      rcases h with h | h
      · exact ih kept y (.inl h)
      · rcases List.mem_cons.mp h with rfl | h
        · obtain ⟨k,hk,sub⟩ := List.any_eq_true.mp covered
          obtain ⟨k',hk',sub'⟩ := ih kept k (.inl hk)
          refine ⟨k',hk',fun a ha => ?_⟩
          simpa using List.all_eq_true.mp sub a (sub' ha)
        · exact ih kept y (.inr h)
    next =>
      rcases h with h | h
      · exact ih _ y (.inl (List.mem_cons_of_mem _ h))
      · rcases List.mem_cons.mp h with rfl | h
        · exact ih _ y (.inl List.mem_cons_self)
        · exact ih _ y (.inr h)

/-- The requests none of whose proper subsets is requested. A solution that
satisfies a request satisfies each request contained in it. -/
def minimal {α : Type} [DecidableEq α] (xs : List (List α)) : List (List α) :=
  minimalInto [] (ACBasis.sortBy (fun a b => decide (a.length ≤ b.length)) xs)

theorem minimal_mem {α : Type} [DecidableEq α] (xs : List (List α)) :
    ∀ y ∈ minimal xs, y ∈ xs := by
  intro y h
  rcases minimalInto_mem _ _ y h with h | h
  · cases h
  · exact (ACBasis.mem_sortBy _ _ _).mp h

theorem minimal_covers {α : Type} [DecidableEq α] (xs : List (List α)) :
    ∀ y ∈ xs, ∃ k ∈ minimal xs, k ⊆ y :=
  fun y h => minimalInto_covers _ _ y (.inr ((ACBasis.mem_sortBy _ _ _).mpr h))

structure Stage (p : Problem s) (candidates : List (SlotPair s)) where
  rows : List (UnifierSorts.Template s)
  reopen : List (List (SlotPair s))
  nonempty : ∀ zs ∈ reopen, zs ≠ []
  subset : ∀ zs ∈ reopen, zs ⊆ candidates
  sound : ∀ θ ∈ rows, RigidBranches.Solves p θ
  covers : ∀ ρ : Substitution s, p.Solves ρ →
    (∃ θ ∈ rows, ∃ μ, ∀ v, p.Occurs v → EquivB (ρ.image v) ((θ v).subst μ)) ∨
    ∃ zs ∈ reopen, ∀ z ∈ zs, EquivB (ρ.apply z.1) (ρ.apply z.2)

/-- A completed branch projects its shared slot valuation back to the input.
A blocked branch may instead prove new equalities between original subterms.
Only those original terms cross into the next pass, and a request that
contains another request is covered by it. -/
private def branchOn (p : Problem s) (candidates : List (SlotPair s)) (c : Compiled p) :
    Option (Stage p candidates) := by
  let q := purify p
  let compiled := c.problem
  let key (z : SlotPair s) := (slot (q.slot z.1),slot (q.slot z.2))
  let terms := watched compiled q (inventory p)
  let eligible : Thunk (List (SlotPair s)) :=
    Thunk.mk fun _ => candidates.filter fun z => z.1 ∈ terms && z.2 ∈ terms
  let obs := observationsOn compiled q terms
  let ban := banOf (s := s) (narrowOf q p)
  let result := ComponentSearch.analyze (s := uniform s) key eligible (heads (s := s) q) compiled obs
    ban (ban_observed p compiled)
  let image := fun (σ : Substitution (uniform s)) => project q (fun i => read Term.var (σ.image (slot i)))
  have live (v) (h : compiled.Occurs v) : v ∈ obs :=
    Buckets.mem_dedup.mpr (List.mem_append_left _ ((Problem.mem_variables ..).mpr h))
  have observed (t : Term s) (h : t ∈ terms) : slot (q.slot t) ∈ obs :=
    Buckets.mem_dedup.mpr (List.mem_append_right _ (List.mem_map_of_mem h))
  match hr : result.val with
  | none => exact none
  | some ans =>
    let rows := ans.filterMap Sum.getLeft?
    let requests := ans.filterMap Sum.getRight?
    let again := minimal requests
    obtain ⟨allowed,valid,cover⟩ := result.property ans hr
    have memL {σ} : σ ∈ rows ↔ Sum.inl σ ∈ ans := by
      simp [rows,List.mem_filterMap,Sum.getLeft?_eq_some_iff]
    have memR {zs} : zs ∈ requests ↔ Sum.inr zs ∈ ans := by
      simp [requests,List.mem_filterMap,Sum.getRight?_eq_some_iff]
    refine some ⟨rows.map image,again,
      fun zs hz => (allowed zs (memR.mp (minimal_mem _ zs hz))).1,
      fun zs hz z mem => (List.mem_filter.mp
        ((allowed zs (memR.mp (minimal_mem _ zs hz))).2 z mem)).1,?_,?_⟩
    · intro θ hθ
      obtain ⟨σ,hσ,rfl⟩ := List.mem_map.mp hθ
      have solves := (Residual.start (· ∈ obs) compiled live σ).mp (valid σ (memL.mp hσ))
      exact c.sound σ solves
    · intro ρ sol
      obtain ⟨V,model,values⟩ := extend_inventory p ρ.image sol
      have start := (Residual.start (· ∈ obs) compiled live _).mpr (c.cover obs V ρ.image model values live)
      have hs (i) (h : slot i ∈ obs) : (reserve obs V).image (slot i) = encode (V i) :=
        ite_eq_left ⟨h,rfl⟩
      have shaped : ComponentSearch.Shaped (s := uniform s) ban (reserve obs V) := by
        intro y h hb eqh
        obtain ⟨v,occ,rfl,misfit⟩ := ban_source q p hb
        rw [hs _ (observed _ (watched_var _ _ _ (var_in_inventory occ)))] at eqh
        have val : EquivB (ρ.image v) (V (q.slot (.var v))) := values _ (var_in_inventory occ)
        have le : Subsort (V (q.slot (.var v))).rootSort v.sort :=
          Term.rootSort_equiv val ▸ Term.rootSort_le (ρ.sorted v)
        rw [← eqh, fits_encode _ _ le] at misfit
        cases misfit
      rcases cover _ shaped start with ⟨σ,hσ,δ,hδ⟩ | ⟨zs,hz,linked⟩
      · refine .inl ⟨_,List.mem_map_of_mem (memL.mpr hσ),fun w => read (.var ∘ original) (δ.image w),?_⟩
        intro v hv
        apply (values _ (var_in_inventory hv)).trans
        let i := q.slot (.var v)
        have seen := observed _ (watched_var compiled q _ (var_in_inventory hv))
        have eq := read_equiv (s := s) (.var ∘ original) (hδ _ seen)
        change EquivB (read _ ((reserve obs V).image (slot i))) (read _ (δ.apply (σ.image (slot i)))) at eq
        rw [hs _ seen,read_encode,read_subst] at eq
        exact eq
      · obtain ⟨ks,hk,sub⟩ := minimal_covers requests zs (memR.mpr hz)
        refine .inr ⟨ks,hk,fun z mem => ?_⟩
        have member := (allowed zs hz).2 z (sub mem)
        have both := (List.mem_filter.mp member).2
        simp only [Bool.and_eq_true,decide_eq_true_eq] at both
        have eq := read_equiv (s := s) (.var ∘ original) (linked z (sub mem))
        change EquivB (read _ ((reserve obs V).image (slot (q.slot z.1))))
          (read _ ((reserve obs V).image (slot (q.slot z.2)))) at eq
        rw [hs _ (observed _ both.1),hs _ (observed _ both.2),read_encode,read_encode] at eq
        exact (values _ (watched_subset _ _ _ both.1)).trans
          (eq.trans (values _ (watched_subset _ _ _ both.2)).symm)

/-- Search the flat problem. If that search defers, repeat it with one
definition per binary node, which can also relate the partial products. The
two problems have the same number of equations exactly when no product has
more than two operands, and then the second search would repeat the first. -/
def branch (p : Problem s) (candidates : List (SlotPair s)) : Option (Stage p candidates) :=
  match branchOn p candidates (flat p) with
  | some stage => some stage
  | none =>
    if (flat p).problem.length = (binary p).problem.length then none
    else branchOn p candidates (binary p)

theorem branch_closed (p : Problem s) (candidates : List (SlotPair s)) (closed : ConstructorFrontier p) :
    ∃ stage, branch p candidates = some stage ∧ stage.reopen = [] := by
  let q := purify p
  let compiled := (flat p).problem
  let key (z : SlotPair s) := (slot (q.slot z.1),slot (q.slot z.2))
  let es : Thunk (List (SlotPair s)) :=
    Thunk.mk fun _ => candidates.filter fun z =>
      z.1 ∈ watched compiled q (inventory p) && z.2 ∈ watched compiled q (inventory p)
  obtain ⟨ans,hr,clean⟩ := ComponentSearch.analyze_closed (s := uniform s) key es
    (heads (s := s) q) compiled (observationsOn compiled q (watched compiled q (inventory p)))
    (banOf (s := s) (narrowOf q p))
    (ban_observed p compiled) closed
  have empty : minimal (ans.filterMap Sum.getRight?) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro zs hz
    have := minimal_mem _ zs hz
    simp [List.mem_filterMap,Sum.getRight?_eq_some_iff,clean] at this
  have first : ∃ stage, branchOn p candidates (flat p) = some stage ∧ stage.reopen = [] := by
    unfold branchOn
    dsimp only
    split
    next none =>
      change (ComponentSearch.analyze key es _ compiled _ _ _).val = _ at none
      rw [hr] at none; contradiction
    next as same =>
      change (ComponentSearch.analyze key es _ compiled _ _ _).val = _ at same
      rw [hr] at same; cases same
      exact ⟨_,rfl,empty⟩
  obtain ⟨stage,hs,none⟩ := first
  exact ⟨stage,by simp [branch,hs],none⟩

end Tamarin.MixedUnification.ComponentEncoding
