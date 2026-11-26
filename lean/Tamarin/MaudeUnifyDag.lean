import Tamarin.ReferenceMatching

/-!
# Dags for the port of Maude's unification algorithm

Maude unifies dag nodes, not binary terms. A node is a variable slot, an atom,
a free application, a commutative application with two arguments, or an AC
application with its flattened arguments. AC arguments are kept as a list in
which equal arguments are repeated; Maude's pairs of an argument and its
multiplicity are the runs of that list.

Maude orders the arguments of AC and C nodes by its term order. That order is
determined by numbers that depend on the module and on the session: the
creation order of the operators, of the variable symbol of each sort, and of
variable names. They are the parameters `Ranks` here. They decide only the
order in which answers are found and how fresh variables are numbered. No
property of them is assumed anywhere: every statement holds for all ranks.

A dag denotes a term once its slots are given values (`eval`). Normalizing the
arguments of an AC or C node does not change the denoted term modulo B.
-/
namespace Tamarin.MaudeUnify

/-- Maude dag nodes over a signature. Slots number the variables. -/
inductive Dag (s : Signature) where
  | var (i : Nat)
  | atom (a : s.Atom)
  | free (f : s.FreeSym) (args : List (Dag s))
  | comm (f : s.CSym) (l r : Dag s)
  | ac (f : s.ACSym) (args : List (Dag s))

namespace Dag
variable {s : Signature}

/-- Induction over dags with a hypothesis for every argument of a list. -/
@[elab_as_elim]
theorem induct' {P : Dag s → Prop}
    (var : ∀ i, P (.var i)) (atom : ∀ a, P (.atom a))
    (free : ∀ f args, (∀ d ∈ args, P d) → P (.free f args))
    (comm : ∀ f l r, P l → P r → P (.comm f l r))
    (ac : ∀ f args, (∀ d ∈ args, P d) → P (.ac f args)) (d : Dag s) : P d :=
  Dag.rec (motive_1 := P) (motive_2 := fun l => ∀ d ∈ l, P d) var atom
    (fun f args h => free f args h) comm (fun f args h => ac f args h)
    (fun _ h => nomatch h)
    (fun d ds hd hds e he => by
      rcases List.mem_cons.mp he with rfl | he
      · exact hd
      · exact hds e he) d

section Eq
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

mutual
/-- Syntactic equality of dags. -/
def beq : Dag s → Dag s → Bool
  | .var i, .var j => i == j
  | .atom a, .atom b => decide (a = b)
  | .free f xs, .free g ys => decide (f = g) && beqList xs ys
  | .comm f a b, .comm g c d => decide (f = g) && beq a c && beq b d
  | .ac f xs, .ac g ys => decide (f = g) && beqList xs ys
  | _, _ => false

def beqList : List (Dag s) → List (Dag s) → Bool
  | [], [] => true
  | x :: xs, y :: ys => beq x y && beqList xs ys
  | _, _ => false
end

mutual
theorem beq_iff : ∀ (x y : Dag s), beq x y = true ↔ x = y
  | .var i, .var j => by simp [beq]
  | .atom a, .atom b => by simp [beq]
  | .free f xs, .free g ys => by
    simp only [beq, Bool.and_eq_true, decide_eq_true_eq, beqList_iff xs ys, free.injEq]
  | .comm f a b, .comm g c d => by
    simp only [beq, Bool.and_eq_true, decide_eq_true_eq, beq_iff a c, beq_iff b d, comm.injEq, and_assoc]
  | .ac f xs, .ac g ys => by
    simp only [beq, Bool.and_eq_true, decide_eq_true_eq, beqList_iff xs ys, ac.injEq]
  | .var _, .atom _ | .var _, .free _ _ | .var _, .comm _ _ _ | .var _, .ac _ _
  | .atom _, .var _ | .atom _, .free _ _ | .atom _, .comm _ _ _ | .atom _, .ac _ _
  | .free _ _, .var _ | .free _ _, .atom _ | .free _ _, .comm _ _ _ | .free _ _, .ac _ _
  | .comm _ _ _, .var _ | .comm _ _ _, .atom _ | .comm _ _ _, .free _ _ | .comm _ _ _, .ac _ _
  | .ac _ _, .var _ | .ac _ _, .atom _ | .ac _ _, .free _ _ | .ac _ _, .comm _ _ _ => by simp [beq]

theorem beqList_iff : ∀ (xs ys : List (Dag s)), beqList xs ys = true ↔ xs = ys
  | [], [] => by simp [beqList]
  | x :: xs, y :: ys => by
    simp only [beqList, Bool.and_eq_true, beq_iff x y, beqList_iff xs ys, List.cons.injEq]
  | [], _ :: _ | _ :: _, [] => by simp [beqList]
end

instance : DecidableEq (Dag s) := fun x y => decidable_of_iff _ (beq_iff x y)

end Eq

/-- The slots that occur in a dag, with repetitions. -/
def vars : Dag s → List Nat
  | .var i => [i]
  | .atom _ => []
  | .free _ args => args.attach.flatMap fun ⟨d, _⟩ => vars d
  | .comm _ l r => vars l ++ vars r
  | .ac _ args => args.attach.flatMap fun ⟨d, _⟩ => vars d

/-- A dag without slots. -/
def ground (d : Dag s) : Bool := d.vars.isEmpty

/-- The term that stands for an argument a dag does not have. -/
def dflt : Term s := .var ⟨0, .msg⟩

/-- The term a dag denotes when slot `i` has the value `ρ i`. An AC node
denotes the right-nested product of its arguments. -/
def eval (ρ : Nat → Term s) : Dag s → Term s
  | .var i => ρ i
  | .atom a => .atom a
  | .free f args =>
    let ts := args.attach.map fun ⟨d, _⟩ => eval ρ d
    .free f fun i => ts.getD i.val dflt
  | .comm f l r => .comm f (eval ρ l) (eval ρ r)
  | .ac f args =>
    match args.attach.map fun ⟨d, _⟩ => eval ρ d with
    | [] => dflt
    | t :: ts => ACRepresentation.fold f t ts

/-- The denotation of an AC node from the denotations of its arguments. -/
def product (f : s.ACSym) : List (Term s) → Term s
  | [] => dflt
  | t :: ts => ACRepresentation.fold f t ts

theorem eval_var (ρ : Nat → Term s) (i : Nat) : eval ρ (.var i) = ρ i := by
  simp [eval]

theorem eval_atom (ρ : Nat → Term s) (a : s.Atom) : eval ρ (.atom a) = .atom a := by
  simp [eval]

theorem eval_free (ρ : Nat → Term s) (f : s.FreeSym) (args : List (Dag s)) :
    eval ρ (.free f args) = .free f fun i => (args.map (eval ρ)).getD i.val dflt := by
  rw [eval]
  have : (args.attach.map fun (x : {d // d ∈ args}) => eval ρ x.val) = args.map (eval ρ) := by
    simp
  simp only [this]

theorem eval_comm (ρ : Nat → Term s) (f : s.CSym) (l r : Dag s) :
    eval ρ (.comm f l r) = .comm f (eval ρ l) (eval ρ r) := by
  simp [eval]

theorem eval_ac (ρ : Nat → Term s) (f : s.ACSym) (args : List (Dag s)) :
    eval ρ (.ac f args) = product f (args.map (eval ρ)) := by
  rw [eval]
  have : (args.attach.map fun (x : {d // d ∈ args}) => eval ρ x.val) = args.map (eval ρ) := by
    simp
  simp only [this]
  cases args.map (eval ρ) <;> rfl

theorem vars_free (f : s.FreeSym) (args : List (Dag s)) :
    vars (.free f args) = args.flatMap vars := by
  rw [vars]
  simp

theorem vars_ac (f : s.ACSym) (args : List (Dag s)) :
    vars (.ac f args) = args.flatMap vars := by
  rw [vars]
  simp

/-- A dag denotes the same term under two valuations that agree on its slots. -/
theorem eval_congr {ρ ρ' : Nat → Term s} (d : Dag s) (agree : ∀ i ∈ d.vars, ρ i = ρ' i) :
    eval ρ d = eval ρ' d := by
  induction d using induct' with
  | var i => simpa [eval_var, vars] using agree i (by simp [vars])
  | atom a => simp [eval_atom]
  | free f args ih =>
    rw [eval_free, eval_free]
    have same : args.map (eval ρ) = args.map (eval ρ') := by
      apply List.map_congr_left
      intro d hd
      exact ih d hd fun i hi => agree i (by rw [vars_free]; exact List.mem_flatMap.mpr ⟨d, hd, hi⟩)
    rw [same]
  | comm f l r il ir =>
    rw [eval_comm, eval_comm, il fun i hi => agree i (by simp [vars, hi]),
      ir fun i hi => agree i (by simp [vars, hi])]
  | ac f args ih =>
    rw [eval_ac, eval_ac]
    have same : args.map (eval ρ) = args.map (eval ρ') := by
      apply List.map_congr_left
      intro d hd
      exact ih d hd fun i hi => agree i (by rw [vars_ac]; exact List.mem_flatMap.mpr ⟨d, hd, hi⟩)
    rw [same]

/-- A ground dag denotes one term under every valuation. -/
theorem eval_ground {d : Dag s} (h : d.ground = true) (ρ ρ' : Nat → Term s) :
    eval ρ d = eval ρ' d :=
  eval_congr d fun i hi => by
    simp only [ground, List.isEmpty_iff] at h
    rw [h] at hi
    cases hi

/-! ### Products -/

theorem product_perm (f : s.ACSym) {ts us : List (Term s)} (h : ts.Perm us) :
    EquivB (product f ts) (product f us) := by
  cases ts with
  | nil => rw [List.Perm.nil_eq h]; exact .refl _
  | cons t ts =>
    cases us with
    | nil => exact absurd h.length_eq (by simp)
    | cons u us => exact ACRepresentation.decode_perm f h _ _ rfl rfl

theorem product_append (f : s.ACSym) {ts us : List (Term s)} (ht : ts ≠ []) (hu : us ≠ []) :
    EquivB (product f (ts ++ us)) (.ac f (product f ts) (product f us)) := by
  obtain ⟨t, ts, rfl⟩ := List.exists_cons_of_ne_nil ht
  obtain ⟨u, us, rfl⟩ := List.exists_cons_of_ne_nil hu
  exact ACRepresentation.fold_append f t ts u us

theorem product_cons_cons (f : s.ACSym) (t u : Term s) (us : List (Term s)) :
    product f (t :: u :: us) = .ac f t (product f (u :: us)) := rfl

theorem product_cons {f : s.ACSym} (t : Term s) {ts : List (Term s)} (h : ts ≠ []) :
    product f (t :: ts) = .ac f t (product f ts) := by
  obtain ⟨u, us, rfl⟩ := List.exists_cons_of_ne_nil h
  rfl

/-- A product of a list that contains a product of a nonempty list equals the
product of the spliced list. -/
theorem product_splice (f : s.ACSym) (xs ys zs : List (Term s)) (hy : ys ≠ []) :
    EquivB (product f (xs ++ product f ys :: zs)) (product f (xs ++ ys ++ zs)) := by
  -- move the inner product to the front on both sides
  have left : (xs ++ product f ys :: zs).Perm (product f ys :: (xs ++ zs)) :=
    List.perm_middle
  have right : (xs ++ ys ++ zs).Perm (ys ++ (xs ++ zs)) := by
    simpa [List.append_assoc] using (List.perm_append_comm (l₁ := xs) (l₂ := ys)).append_right zs
  refine .trans (product_perm f left) (.trans ?_ (product_perm f right).symm)
  cases hrest : xs ++ zs with
  | nil =>
    simp only [List.append_nil]
    obtain ⟨y, ys', rfl⟩ := List.exists_cons_of_ne_nil hy
    exact .refl _
  | cons r rs =>
    have step := product_append f (ts := ys) (us := r :: rs) hy (by simp)
    exact .trans (.refl _) step.symm

theorem fold_map_congr {α : Type} (f : s.ACSym) {t u : Term s} (h : EquivB t u) (l : List α)
    (g k : α → Term s) (hs : ∀ x ∈ l, EquivB (g x) (k x)) :
    EquivB (ACRepresentation.fold f t (l.map g)) (ACRepresentation.fold f u (l.map k)) := by
  induction l generalizing t u with
  | nil => exact h
  | cons x xs ih =>
    exact .ac_congr f h (ih (hs x (by simp)) fun y hy => hs y (List.mem_cons_of_mem _ hy))

/-- Products of lists mapped elementwise to equal terms are equal. -/
theorem product_map_congr {α : Type} (f : s.ACSym) (l : List α) (g k : α → Term s)
    (hs : ∀ x ∈ l, EquivB (g x) (k x)) :
    EquivB (product f (l.map g)) (product f (l.map k)) := by
  cases l with
  | nil => exact .refl _
  | cons x xs =>
    exact fold_map_congr f (hs x (by simp)) xs g k fun y hy => hs y (List.mem_cons_of_mem _ hy)

/-- Valuations that agree modulo B on the slots of a dag give it denotations
that agree modulo B. -/
theorem eval_equiv {ρ ρ' : Nat → Term s} (d : Dag s) (agree : ∀ i ∈ d.vars, EquivB (ρ i) (ρ' i)) :
    EquivB (eval ρ d) (eval ρ' d) := by
  induction d using induct' with
  | var i => simpa [eval_var, vars] using agree i (by simp [vars])
  | atom a => rw [eval_atom, eval_atom]; exact .refl _
  | free f args ih =>
    rw [eval_free, eval_free]
    apply EquivB.free
    intro i
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases h : args[i.val]? with
    | none => exact .refl _
    | some d =>
      have hd := List.mem_of_getElem? h
      exact ih d hd fun j hj => agree j (by rw [vars_free]; exact List.mem_flatMap.mpr ⟨d, hd, hj⟩)
  | comm f l r il ir =>
    rw [eval_comm, eval_comm]
    exact .comm_congr f (il fun i hi => agree i (by simp [vars, hi]))
      (ir fun i hi => agree i (by simp [vars, hi]))
  | ac f args ih =>
    rw [eval_ac, eval_ac]
    apply product_map_congr
    intro d hd
    exact ih d hd fun j hj => agree j (by rw [vars_ac]; exact List.mem_flatMap.mpr ⟨d, hd, hj⟩)

end Dag

/-! ### Maude's term order -/

/-- Operator and variable ranks of Maude's term order (`Symbol::compare`,
`VariableDagNode::compareArguments`). `name i` is the code of the name of the
variable in slot `i`; `varSym` is the rank of the variable symbol of a sort,
`none` being the error sort of fresh variables. `sortIndex` is the index of a
sort in its connected component, which orients variable bindings. -/
structure Ranks (s : Signature) where
  atom : s.Atom → Nat
  atomArg : s.Atom → Nat
  free : s.FreeSym → Nat
  comm : s.CSym → Nat
  ac : s.ACSym → Nat
  varSym : Option SortId → Nat
  name : Nat → Nat
  sortIndex : Option SortId → Nat

namespace Dag
variable {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

/-- The runs of equal adjacent arguments: Maude's argument/multiplicity pairs. -/
def runs : List (Dag s) → List (Dag s × Nat)
  | [] => []
  | d :: ds =>
    match runs ds with
    | (e, m) :: rest => if d = e then (e, m + 1) :: rest else (d, 1) :: (e, m) :: rest
    | [] => [(d, 1)]

/-- The rank of the top symbol. -/
def top (r : Ranks s) (sortOf : Nat → Option SortId) : Dag s → Nat
  | .var i => r.varSym (sortOf i)
  | .atom a => r.atom a
  | .free f _ => r.free f
  | .comm f _ _ => r.comm f
  | .ac f _ => r.ac f

mutual
/-- The number of nodes. -/
def size : Dag s → Nat
  | .var _ | .atom _ => 1
  | .free _ args => 1 + sizeList args
  | .comm _ l r => 1 + size l + size r
  | .ac _ args => 1 + sizeList args

def sizeList : List (Dag s) → Nat
  | [] => 0
  | d :: ds => size d + sizeList ds
end

/-- Lexicographic comparison of paired arguments. -/
def lexBy (c : Dag s → Dag s → Ordering) : List (Dag s × Dag s) → Ordering
  | [] => .eq
  | (a, b) :: rest => match c a b with
    | .eq => lexBy c rest
    | o => o

/-- Comparison of paired runs, multiplicity first. -/
def pairsBy (c : Dag s → Dag s → Ordering) : List ((Dag s × Nat) × (Dag s × Nat)) → Ordering
  | [] => .eq
  | ((a, m), (b, k)) :: rest =>
    if m ≠ k then compare m k else
    match c a b with
    | .eq => pairsBy c rest
    | o => o

/-- `DagNode::compare` with a bound on the depth of the comparison: by top
symbol, then by arguments; AC arguments by the number of runs, then run by
run, multiplicity first. Only the order of answers depends on it. -/
def cmpN (r : Ranks s) (sortOf : Nat → Option SortId) : Nat → Dag s → Dag s → Ordering
  | 0, _, _ => .eq
  | n + 1, x, y =>
    let tx := top r sortOf x
    let ty := top r sortOf y
    if tx ≠ ty then compare tx ty else
    match x, y with
    | .var i, .var j => compare (r.name i) (r.name j)
    | .atom a, .atom b => compare (r.atomArg a) (r.atomArg b)
    | .free _ xs, .free _ ys => lexBy (cmpN r sortOf n) (xs.zip ys)
    | .comm _ a b, .comm _ c d => lexBy (cmpN r sortOf n) [(a, c), (b, d)]
    | .ac _ xs, .ac _ ys =>
      let rx := runs xs
      let ry := runs ys
      if rx.length ≠ ry.length then compare rx.length ry.length else
      pairsBy (cmpN r sortOf n) (rx.zip ry)
    | _, _ => .eq

/-- The comparison of two dags with the same top rank. -/
def cmpBody (r : Ranks s) (c : Dag s → Dag s → Ordering) : Dag s → Dag s → Ordering
  | .var i, .var j => compare (r.name i) (r.name j)
  | .atom a, .atom b => compare (r.atomArg a) (r.atomArg b)
  | .free _ xs, .free _ ys => lexBy c (xs.zip ys)
  | .comm _ a b, .comm _ c' d => lexBy c [(a, c'), (b, d)]
  | .ac _ xs, .ac _ ys =>
    let rx := runs xs
    let ry := runs ys
    if rx.length ≠ ry.length then compare rx.length ry.length else
    pairsBy c (rx.zip ry)
  | _, _ => .eq

theorem cmpN_succ (r : Ranks s) (sortOf : Nat → Option SortId) (n : Nat) (x y : Dag s) :
    cmpN r sortOf (n + 1) x y =
      if top r sortOf x ≠ top r sortOf y then compare (top r sortOf x) (top r sortOf y)
      else cmpBody r (cmpN r sortOf n) x y := by
  cases x <;> cases y <;> rfl

/-- Whether two dags have the same top symbol, hence the same top rank. -/
def sameTop (sortOf : Nat → Option SortId) : Dag s → Dag s → Bool
  | .var i, .var j => sortOf i == sortOf j
  | .atom a, .atom b => decide (a = b)
  | .free f _, .free g _ => decide (f = g)
  | .comm f _ _, .comm g _ _ => decide (f = g)
  | .ac f _, .ac g _ => decide (f = g)
  | _, _ => false

theorem top_eq_of_sameTop (r : Ranks s) {sortOf : Nat → Option SortId} {x y : Dag s} :
    sameTop sortOf x y = true → top r sortOf x = top r sortOf y := by
  intro h
  cases x <;> cases y <;> simp_all [sameTop, top]

/-- `cmpN` that skips the ranks of equal top symbols. -/
def cmpNFast (r : Ranks s) (sortOf : Nat → Option SortId) : Nat → Dag s → Dag s → Ordering
  | 0, _, _ => .eq
  | n + 1, x, y =>
    if sameTop sortOf x y then cmpBody r (cmpNFast r sortOf n) x y else
    let tx := top r sortOf x
    let ty := top r sortOf y
    if tx ≠ ty then compare tx ty else cmpBody r (cmpNFast r sortOf n) x y

@[csimp] theorem cmpN_eq_cmpNFast : @cmpN = @cmpNFast := by
  funext s i1 i2 i3 i4 r sortOf n
  induction n with
  | zero => funext x y; rfl
  | succ n ih =>
    funext x y
    rw [cmpN_succ, cmpNFast, ih]
    by_cases h : sameTop sortOf x y = true
    · have e := top_eq_of_sameTop r h
      simp only [h, e, ne_eq, not_true_eq_false, ite_false, ite_true]
    · simp only [h, Bool.false_eq_true, ite_false]

/-- Maude's term order on dags. -/
def cmp (r : Ranks s) (sortOf : Nat → Option SortId) (x y : Dag s) : Ordering :=
  cmpN r sortOf (size x) x y

/-- Splice the arguments that are themselves nonempty products of `f`. -/
def flat (f : s.ACSym) : List (Dag s) → List (Dag s)
  | [] => []
  | .ac g inner :: rest => if g = f ∧ inner ≠ [] then inner ++ flat f rest else .ac g inner :: flat f rest
  | d :: rest => d :: flat f rest

/-- Maude's normal form of the arguments of an AC node: flattened and sorted
by the term order (`dumbNormalizeAtTop`, `sortAndUniquize`). -/
def normAC (r : Ranks s) (sortOf : Nat → Option SortId) (f : s.ACSym) (args : List (Dag s)) :
    List (Dag s) :=
  (flat f args).mergeSort fun a b => cmp r sortOf a b != .gt

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem size_pos (d : Dag s) : 0 < size d := by
  cases d <;> simp only [size] <;> omega

/-- A dag with its top rank and, for a variable, the rank of its name, so
that sorting compares numbers first. -/
def keyed (r : Ranks s) (sortOf : Nat → Option SortId) (d : Dag s) : Dag s × Nat × Nat :=
  (d, top r sortOf d, match d with | .var i => r.name i | _ => 0)

/-- The term order on keyed dags. -/
def cmpKeyed (r : Ranks s) (sortOf : Nat → Option SortId) (a b : Dag s × Nat × Nat) : Ordering :=
  if a.2.1 ≠ b.2.1 then compare a.2.1 b.2.1 else
  match a.1, b.1 with
  | .var _, .var _ => compare a.2.2 b.2.2
  | x, y => cmpBody r (cmpN r sortOf (size x - 1)) x y

theorem cmpKeyed_keyed (r : Ranks s) (sortOf : Nat → Option SortId) (a b : Dag s) :
    cmpKeyed r sortOf (keyed r sortOf a) (keyed r sortOf b) = cmp r sortOf a b := by
  unfold cmp
  obtain ⟨n, hn⟩ : ∃ n, size a = n + 1 := ⟨size a - 1, by have := size_pos a; omega⟩
  rw [hn, cmpN_succ]
  unfold cmpKeyed keyed
  simp only
  split
  · rfl
  · cases a <;> cases b <;> simp_all [cmpBody]

/-- `normAC` sorting keyed dags. -/
def normACKeyed (r : Ranks s) (sortOf : Nat → Option SortId) (f : s.ACSym) (args : List (Dag s)) :
    List (Dag s) :=
  (((flat f args).map (keyed r sortOf)).mergeSort fun a b => cmpKeyed r sortOf a b != .gt).map (·.1)

@[csimp] theorem normAC_eq_normACKeyed : @normAC = @normACKeyed := by
  funext s i1 i2 i3 i4 r sortOf f args
  unfold normAC normACKeyed
  rw [← List.map_mergeSort (fun a _ b _ => by rw [cmpKeyed_keyed]), List.map_map]
  have : (Prod.fst ∘ keyed r sortOf) = id := by funext d; rfl
  rw [this, List.map_id]

/-- A C node with its arguments in the term order. -/
def mkComm (r : Ranks s) (sortOf : Nat → Option SortId) (f : s.CSym) (a b : Dag s) : Dag s :=
  if cmp r sortOf b a == .lt then .comm f b a else .comm f a b

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] in
theorem flat_eq_nil {f : s.ACSym} {args : List (Dag s)} : flat f args = [] ↔ args = [] := by
  cases args with
  | nil => simp [flat]
  | cons d rest =>
    simp only [reduceCtorEq, iff_false]
    cases d with
    | ac g inner =>
      unfold flat
      split
      · next h => simp [h.2]
      · simp
    | _ => simp [flat]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] in
theorem eval_flat (ρ : Nat → Term s) (f : s.ACSym) (args : List (Dag s)) :
    EquivB (product f ((flat f args).map (eval ρ))) (product f (args.map (eval ρ))) := by
  induction args with
  | nil => exact .refl _
  | cons d rest ih =>
    have plain : EquivB (product f ((d :: flat f rest).map (eval ρ))) (product f ((d :: rest).map (eval ρ))) := by
      by_cases hr : rest = []
      · subst hr; exact .refl _
      · have hf : flat f rest ≠ [] := fun h => hr (flat_eq_nil.mp h)
        simp only [List.map_cons]
        rw [product_cons _ (by simpa using hf), product_cons _ (by simpa using hr)]
        exact .ac_congr f (.refl _) ih
    cases d with
    | ac g inner =>
      unfold flat
      split
      · next h =>
        obtain ⟨rfl, hi⟩ := h
        have hI : inner.map (eval ρ) ≠ [] := by simpa using hi
        simp only [List.map_cons, List.map_append]
        rw [eval_ac]
        by_cases hr : rest = []
        · subst hr; simp [flat, product]
          obtain ⟨u, us, hu⟩ := List.exists_cons_of_ne_nil hI
          rw [hu]; exact .refl _
        · have hf : (flat g rest).map (eval ρ) ≠ [] := by
            simpa using fun h => hr (flat_eq_nil.mp h)
          rw [product_cons _ (by simpa using hr)]
          exact .trans (product_append g hI hf) (.ac_congr g (.refl _) ih)
      · exact plain
    | var | atom | free | comm => exact plain

theorem eval_normAC (r : Ranks s) (sortOf : Nat → Option SortId) (ρ : Nat → Term s) (f : s.ACSym)
    (args : List (Dag s)) :
    EquivB (eval ρ (.ac f (normAC r sortOf f args))) (eval ρ (.ac f args)) := by
  rw [eval_ac, eval_ac, normAC]
  exact .trans (product_perm f ((List.mergeSort_perm _ _).map _)) (eval_flat ρ f args)

theorem eval_mkComm (r : Ranks s) (sortOf : Nat → Option SortId) (ρ : Nat → Term s) (f : s.CSym)
    (a b : Dag s) : EquivB (eval ρ (mkComm r sortOf f a b)) (eval ρ (.comm f a b)) := by
  unfold mkComm
  split
  · rw [eval_comm, eval_comm]; exact .comm_swap f _ _
  · exact .refl _

/-- Equality modulo B of two ground dags: syntactic equality, or else the
reference decision. With injective ranks both normal forms are unique and the
second test never succeeds where the first fails, as in Maude's `equal`. -/
def same (d e : Dag s) : Bool :=
  d == e || ReferenceMatching.equal (eval (fun _ => dflt) d) (eval (fun _ => dflt) e)

theorem same_iff {d e : Dag s} (hd : d.ground = true) (he : e.ground = true) (ρ : Nat → Term s) :
    same d e = true ↔ EquivB (eval ρ d) (eval ρ e) := by
  rw [eval_ground hd ρ (fun _ => dflt), eval_ground he ρ (fun _ => dflt)]
  unfold same
  rw [Bool.or_eq_true, ReferenceMatching.equal_iff]
  constructor
  · rintro (h | h)
    · rw [beq_iff_eq.mp h]; exact .refl _
    · exact h
  · exact .inr

/-- The arguments of a rebuilt product: the arguments that did not change keep
their order, and the normalized instances of the others are merged in. -/
def instArgs (r : Ranks s) (sortOf : Nat → Option SortId) (f : s.ACSym) (parts : List (Bool × Dag s)) :
    List (Dag s) :=
  List.merge ((parts.filter fun p => !p.1).map (·.2)) (normAC r sortOf f ((parts.filter (·.1)).map (·.2)))
    fun a b => cmp r sortOf a b != .gt

/-- Whether every slot of the dag passes a test, without building the list. -/
@[specialize] def allVars (p : Nat → Bool) : Dag s → Bool
  | .var i => p i
  | .atom _ => true
  | .free _ args => args.attach.all fun ⟨d, _⟩ => allVars p d
  | .comm _ a b => allVars p a && allVars p b
  | .ac _ args => args.attach.all fun ⟨d, _⟩ => allVars p d

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem allVars_eq (p : Nat → Bool) (d : Dag s) : allVars p d = d.vars.all p := by
  induction d using induct' with
  | var i => simp [allVars, vars]
  | atom a => simp [allVars, vars]
  | free f args ih =>
    rw [allVars, vars_free, List.all_flatMap]
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall]
    exact ⟨fun h d hd => by have := h d hd; rw [ih d hd, List.all_eq_true] at this; exact this,
      fun h d hd => by rw [ih d hd, List.all_eq_true]; exact h d hd⟩
  | comm f a b ia ib => simp [allVars, vars, ia, ib, List.all_append]
  | ac f args ih =>
    rw [allVars, vars_ac, List.all_flatMap]
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall]
    exact ⟨fun h d hd => by have := h d hd; rw [ih d hd, List.all_eq_true] at this; exact this,
      fun h d hd => by rw [ih d hd, List.all_eq_true]; exact h d hd⟩

/-- Whether `σ` binds a slot of the dag. -/
def touched (σ : Nat → Option (Dag s)) : Dag s → Bool
  | .var i => (σ i).isSome
  | .atom _ => false
  | .free _ args => args.attach.any fun ⟨d, _⟩ => touched σ d
  | .comm _ a b => touched σ a || touched σ b
  | .ac _ args => args.attach.any fun ⟨d, _⟩ => touched σ d

/-- The dag with the slots that `σ` binds replaced by their values, and every
rebuilt AC and C node normalized again (`DagNode::instantiate`). A node that
`σ` does not touch is kept as it is, as in Maude. -/
def inst (r : Ranks s) (sortOf : Nat → Option SortId) (σ : Nat → Option (Dag s)) : Dag s → Dag s
  | .var i => (σ i).getD (.var i)
  | .atom a => .atom a
  | .free f args =>
    if touched σ (.free f args) then .free f (args.attach.map fun ⟨d, _⟩ => inst r sortOf σ d)
    else .free f args
  | .comm f a b =>
    if touched σ (.comm f a b) then mkComm r sortOf f (inst r sortOf σ a) (inst r sortOf σ b)
    else .comm f a b
  | .ac f args =>
    if touched σ (.ac f args) then
      .ac f (instArgs r sortOf f (args.attach.map fun ⟨d, _⟩ => (touched σ d, inst r sortOf σ d)))
    else .ac f args

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
/-- A dag that `σ` does not touch mentions only slots that `σ` leaves free. -/
theorem untouched {σ : Nat → Option (Dag s)} (d : Dag s) (h : touched σ d = false) :
    ∀ j ∈ d.vars, σ j = none := by
  induction d using induct' with
  | var i =>
    intro j hj
    simp only [vars, List.mem_singleton] at hj
    subst hj
    simpa [touched] using h
  | atom a => intro j hj; simp [vars] at hj
  | free f args ih =>
    intro j hj
    rw [vars_free, List.mem_flatMap] at hj
    obtain ⟨d, hd, hj⟩ := hj
    simp only [touched, List.any_eq_false] at h
    exact ih d hd (by simpa using h ⟨d, hd⟩ (List.mem_attach _ _)) j hj
  | comm f a b ia ib =>
    intro j hj
    simp only [touched, Bool.or_eq_false_iff] at h
    simp only [vars, List.mem_append] at hj
    rcases hj with hj | hj
    · exact ia h.1 j hj
    · exact ib h.2 j hj
  | ac f args ih =>
    intro j hj
    rw [vars_ac, List.mem_flatMap] at hj
    obtain ⟨d, hd, hj⟩ := hj
    simp only [touched, List.any_eq_false] at h
    exact ih d hd (by simpa using h ⟨d, hd⟩ (List.mem_attach _ _)) j hj

/-- The valuation that gives each bound slot the denotation of its value. -/
def through (ρ : Nat → Term s) (σ : Nat → Option (Dag s)) (i : Nat) : Term s :=
  match σ i with
  | some d => eval ρ d
  | none => ρ i

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem eval_untouched {σ : Nat → Option (Dag s)} (ρ : Nat → Term s) (d : Dag s) (h : touched σ d = false) :
    eval ρ d = eval (through ρ σ) d :=
  eval_congr d fun j hj => by rw [through, untouched d h j hj]

theorem inst_untouched (r : Ranks s) (sortOf : Nat → Option SortId) {σ : Nat → Option (Dag s)} (d : Dag s)
    (h : touched σ d = false) : inst r sortOf σ d = d := by
  cases d with
  | var i =>
    rw [inst]
    have : σ i = none := by simpa [touched] using h
    rw [this]; rfl
  | atom a => rw [inst]
  | free f args => rw [inst]; simp [h]
  | comm f a b => rw [inst]; simp [h]
  | ac f args => rw [inst]; simp [h]

/-- The arguments of a rebuilt product, as the untouched ones and the
normalized instances of the touched ones. -/
theorem instArgs_perm (r : Ranks s) (sortOf : Nat → Option SortId) (σ : Nat → Option (Dag s)) (f : s.ACSym)
    (args : List (Dag s)) :
    (instArgs r sortOf f (args.attach.map fun ⟨d, _⟩ => (touched σ d, inst r sortOf σ d))).Perm
      (args.filter (fun d => !touched σ d) ++
        normAC r sortOf f ((args.filter (touched σ)).map (inst r sortOf σ))) := by
  unfold instArgs
  refine List.Perm.trans (List.merge_perm_append _) ?_
  have hm : (args.attach.map fun (x : {d // d ∈ args}) => (touched σ x.val, inst r sortOf σ x.val)) =
      args.map fun d => (touched σ d, inst r sortOf σ d) := by simp
  rw [hm]
  have hl : ((args.map fun d => (touched σ d, inst r sortOf σ d)).filter
      fun p => !p.1).map (·.2) = args.filter (fun d => !touched σ d) := by
    rw [List.filter_map, List.map_map]
    have e : ((fun p : Bool × Dag s => !p.fst) ∘ fun d => (touched σ d, inst r sortOf σ d)) =
      fun d => !touched σ d := rfl
    rw [e]
    have : ∀ d ∈ args.filter (fun d => !touched σ d), ((·.2) ∘ fun d => (touched σ d, inst r sortOf σ d)) d = d := by
      intro d hd
      exact inst_untouched r sortOf d (by simpa using (List.mem_filter.mp hd).2)
    rw [List.map_congr_left this, List.map_id']
  have hr : ((args.map fun d => (touched σ d, inst r sortOf σ d)).filter
      fun p => p.1).map (·.2) = (args.filter (touched σ)).map (inst r sortOf σ) := by
    rw [List.filter_map, List.map_map]
    have e : ((fun p : Bool × Dag s => p.fst) ∘ fun d => (touched σ d, inst r sortOf σ d)) = touched σ := rfl
    rw [e]
    rfl
  rw [hl, hr]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem touched_some {σ : Nat → Option (Dag s)} {f : s.ACSym} {args : List (Dag s)}
    (h : touched σ (.ac f args) = true) : (args.filter (touched σ)) ≠ [] := by
  simp only [touched, List.any_eq_true] at h
  obtain ⟨⟨d, hd⟩, _, hd'⟩ := h
  intro e
  have : d ∈ args.filter (touched σ) := List.mem_filter.mpr ⟨hd, hd'⟩
  rw [e] at this; cases this

theorem eval_instArgs (r : Ranks s) (sortOf : Nat → Option SortId) (σ : Nat → Option (Dag s))
    (ρ : Nat → Term s) (f : s.ACSym) (args : List (Dag s)) (h : touched σ (.ac f args) = true) :
    EquivB (eval ρ (.ac f (instArgs r sortOf f (args.attach.map fun ⟨d, _⟩ => (touched σ d, inst r sortOf σ d)))))
      (eval ρ (.ac f (args.map (inst r sortOf σ)))) := by
  rw [eval_ac, eval_ac]
  refine .trans (product_perm f ((instArgs_perm r sortOf σ f args).map _)) ?_
  generalize hK : args.filter (fun d => !touched σ d) = K
  generalize hC : (args.filter (touched σ)).map (inst r sortOf σ) = C
  have cne : C ≠ [] := by rw [← hC]; simpa using touched_some h
  -- the untouched arguments are their own instances
  have perm : (K ++ C).Perm (args.map (inst r sortOf σ)) := by
    rw [← hK, ← hC]
    have keep : (args.filter (fun d => !touched σ d)).map (inst r sortOf σ) = args.filter (fun d => !touched σ d) := by
      rw [List.map_congr_left (g := fun d => d)
        (fun d hd => inst_untouched r sortOf d (by simpa using (List.mem_filter.mp hd).2)), List.map_id']
    rw [← keep, ← List.map_append]
    exact (List.perm_append_comm.trans (List.filter_append_perm (touched σ) args)).map _
  refine .trans ?_ (product_perm f (perm.map _))
  have ne : normAC r sortOf f C ≠ [] := by
    intro e
    unfold normAC at e
    have hl := (List.mergeSort_perm (flat f C) fun a b => cmp r sortOf a b != .gt).length_eq
    rw [e] at hl
    exact cne (flat_eq_nil.mp (List.eq_nil_of_length_eq_zero hl.symm))
  cases K with
  | nil =>
    simp only [List.nil_append]
    have := eval_normAC r sortOf ρ f C
    rw [eval_ac, eval_ac] at this
    exact this
  | cons k ks =>
    rw [List.map_append, List.map_append]
    refine .trans (product_append f (by simp) (by simpa using ne)) ?_
    refine .trans ?_ (product_append f (by simp) (by simpa using cne)).symm
    have := eval_normAC r sortOf ρ f C
    rw [eval_ac, eval_ac] at this
    exact .ac_congr f (.refl _) this

theorem eval_inst (r : Ranks s) (sortOf : Nat → Option SortId) (σ : Nat → Option (Dag s))
    (ρ : Nat → Term s) (d : Dag s) : EquivB (eval ρ (inst r sortOf σ d)) (eval (through ρ σ) d) := by
  induction d using induct' with
  | var i =>
    rw [inst, eval_var, through]
    cases σ i <;> simp [eval_var] <;> exact .refl _
  | atom a => rw [inst, eval_atom, eval_atom]; exact .refl _
  | free f args ih =>
    rw [inst]
    split
    · rw [eval_free, eval_free]
      apply EquivB.free
      intro i
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.map_attach_eq_pmap]
      cases h : args[i.val]? with
      | none => simp [h]; exact .refl _
      | some d => simpa [List.getElem?_pmap, h] using ih d (List.mem_of_getElem? h)
    · next h => rw [eval_untouched ρ _ (by simpa using h)]; exact .refl _
  | comm f a b ia ib =>
    rw [inst]
    split
    · exact .trans (eval_mkComm r sortOf ρ f _ _) (by rw [eval_comm, eval_comm]; exact .comm_congr f ia ib)
    · next h => rw [eval_untouched ρ _ (by simpa using h)]; exact .refl _
  | ac f args ih =>
    rw [inst]
    split
    · next ht =>
      refine .trans (eval_instArgs r sortOf σ ρ f args ht) ?_
      rw [eval_ac, eval_ac, List.map_map]
      exact product_map_congr f args _ _ fun d hd => ih d hd
    · next h => rw [eval_untouched ρ _ (by simpa using h)]; exact .refl _

/-- The dag of a term: AC applications flattened and sorted, C arguments
sorted, variables in the slots `slot` gives them. -/
def ofTerm (r : Ranks s) (sortOf : Nat → Option SortId) (slot : Variable → Nat) : Term s → Dag s
  | .var v => .var (slot v)
  | .atom a => .atom a
  | .free f xs => .free f (List.ofFn fun i => ofTerm r sortOf slot (xs i))
  | .comm f a b => mkComm r sortOf f (ofTerm r sortOf slot a) (ofTerm r sortOf slot b)
  | .ac f a b => .ac f (normAC r sortOf f [ofTerm r sortOf slot a, ofTerm r sortOf slot b])

theorem eval_ofTerm (r : Ranks s) (sortOf : Nat → Option SortId) (slot : Variable → Nat)
    (ρ : Nat → Term s) (t : Term s) :
    EquivB (eval ρ (ofTerm r sortOf slot t)) (t.subst fun v => ρ (slot v)) := by
  induction t with
  | var v => rw [ofTerm, eval_var]; exact .refl _
  | atom a => rw [ofTerm, eval_atom]; exact .refl _
  | free f xs ih =>
    rw [ofTerm, eval_free, Term.subst]
    apply EquivB.free
    intro i
    simpa [List.getD_eq_getElem?_getD] using ih i
  | comm f a b ia ib =>
    rw [ofTerm, Term.subst]
    exact .trans (eval_mkComm r sortOf ρ f _ _) (by rw [eval_comm]; exact .comm_congr f ia ib)
  | ac f a b ia ib =>
    rw [ofTerm, Term.subst]
    refine .trans (eval_normAC r sortOf ρ f _) ?_
    rw [eval_ac]
    exact .ac_congr f ia ib

end Dag
end Tamarin.MaudeUnify
