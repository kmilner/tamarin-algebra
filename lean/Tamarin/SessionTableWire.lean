import Tamarin.CertifiedReductionWire
import Tamarin.VariantCheckWire
import Tamarin.TotalInputBounds

/-! Table commands that reuse one certificate for many calls. The table
packet of a call is exactly the packet `certifyTable` accepted: declarations,
node rows and rule roots, with no row added. The terms of the call arrive as
further node rows. Row `i` of them has index `nodes.size + i`, and a child
index may name a table row or an earlier further row.

The further rows are read over the dictionary of the table together with all
ambient names. An atom that occurs in a table row is that table name. Any
other atom `(id, sort)` is the ambient name `(id.toNat, sort)`. The rules are
the lifted rules of the table, the ones the certificate speaks about. -/
namespace Tamarin.SessionWire
open TotalUnifyWire TableAmbient SignatureExtension Rewriting MaudeOperations

variable (d : Dictionary)

/-- A table name when the table mentions it, an ambient name otherwise. -/
def name (id : UInt64) (s : SortId) : (sig d).Atom :=
  if h : (id,s) ∈ d.atoms then .inl ⟨(id,s),h⟩ else .inr (id.toNat,s)

def leaf (k id arg : UInt64) : Option (Term (sig d)) := do
  guard (arg ≤ 4)
  if k == 0 then return .var ⟨id.toNat,sortOf arg⟩
  if k == 1 then return .atom (name d id (sortOf arg))
  none

def symbol (ds : List Whole.Decl) (k id : UInt64) : Option (Symbol ds k) :=
  if h : (decl ds k id).isSome then some ⟨id,h⟩ else none

def app (k id : UInt64) (children : List (Term (sig d))) : Option (Term (sig d)) := do
  if k == 2 then
    let f ← symbol d.decls 2 id
    if h : children.length = d.sig.arity f then
      return .free (.inl f) fun i => children.get ⟨i.val,h.symm ▸ i.isLt⟩
    else none
  else if k == 3 then
    let f ← symbol d.decls 3 id
    let [l,r] := children | none
    return .comm (.inl f) l r
  else if k == 4 then
    let f ← symbol d.decls 4 id
    let l :: r :: rs := children | none
    return .ac (.inl f) l (ACRepresentation.fold (.inl f) r rs)
  else none

variable {d}

/-- The term of a node index: a lifted table term, or a term of a further row. -/
def fetch (base : Array (Term d.sig)) (more : Array (Term (sig d))) (i : Nat) :
    Option (Term (sig d)) :=
  if h : i < base.size then some (liftTerm base[i]) else more[i - base.size]?

def node (base : Array (Term d.sig)) (more : Array (Term (sig d))) (row : Array UInt64) :
    Option (Term (sig d)) := do
  let k :: id :: tail := row.toList | none
  if k ≤ 1 then
    let [arg] := tail | none
    leaf d k id arg
  else
    app d k id (← tail.mapM (fun (i : UInt64) => fetch base more i.toNat))

/-- The terms of the further rows, in order. -/
def extend (base : Array (Term d.sig)) (extra : Array (Array UInt64)) :
    Option (Array (Term (sig d))) :=
  extra.foldlM (fun acc r => do return acc.push (← node base acc r)) #[]

/-- Pairs of node indices, read as equations. -/
def pairs (base : Array (Term d.sig)) (more : Array (Term (sig d))) :
    List UInt64 → Option (Problem (sig d))
  | [] => some []
  | i :: j :: rest => do
    return ⟨← fetch base more i.toNat,← fetch base more j.toNat⟩ :: (← pairs base more rest)
  | [_] => none

/-- Postorder triples of a term over the table and the ambient names. An
ambient name is written only when its number fits a word and no table name
has the same number and sort, so that reading it back gives the same name. -/
def write : Term (sig d) → Option (List Token)
  | .var v => do return [⟨0,← WordEncoding.pack v.id,sortCode v.sort⟩]
  | .atom (.inl a) => some [⟨1,a.val.1,sortCode a.val.2⟩]
  | .atom (.inr a) => do
    let id ← WordEncoding.pack a.1
    if (id,a.2) ∈ d.atoms then none else return [⟨1,id,sortCode a.2⟩]
  | .free (.inl f) args => do
    let code ← (List.finRange _).mapM fun i => write (args i)
    return code.flatten ++ [⟨2,f.val,← WordEncoding.pack (d.sig.arity f)⟩]
  | .free (.inr f) _ => nomatch f
  | .comm (.inl f) l r => do return (← write l) ++ (← write r) ++ [⟨3,f.val,2⟩]
  | .comm (.inr f) _ _ => nomatch f
  | .ac (.inl f) l r => do return (← write l) ++ (← write r) ++ [⟨4,f.val,2⟩]
  | .ac (.inr f) _ _ => nomatch f

variable (d)

/-- The reader of a reply: the stack machine of the ordinary packets, with
the leaves and applications of this module. -/
def step (stack : List (Term (sig d))) (t : Token) : Option (List (Term (sig d))) := do
  if t.kind ≤ 1 then return (← leaf d t.kind t.id t.arg) :: stack
  let n := t.arg.toNat
  guard (n ≤ stack.length)
  return (← app d t.kind t.id ((stack.take n).reverse)) :: stack.drop n

def execute (code : List Token) (stack : List (Term (sig d))) := code.foldlM (step d) stack

/-- A reply with status 1 whose words the reader turns into `u`. -/
def Decodes (reply : Array (Array UInt64)) (u : Term (sig d)) : Prop :=
  ∃ words tokens, reply = #[#[1],words] ∧ Packet.tokenize words.toList = some tokens ∧
    execute d tokens [] = some [u]

variable {d}

private theorem execute_append (xs ys : List Token) (stack : List (Term (sig d))) :
    execute d (xs ++ ys) stack = (execute d xs stack).bind (execute d ys) := List.foldlM_append

private theorem execute_single (t : Token) (st : List (Term (sig d))) :
    execute d [t] st = step d st t := by simp [execute]

private theorem step_app (kind id count : UInt64) (args stack : List (Term (sig d)))
    (t : Term (sig d)) (hk : ¬kind ≤ 1) (n : count.toNat = args.length)
    (ok : app d kind id args = some t) :
    step d (args.reverse ++ stack) ⟨kind,id,count⟩ = some (t :: stack) := by
  simp [step,hk,n,ok,guard]

private theorem app_free (f : d.sig.FreeSym) (args : Fin (d.sig.arity f) → Term (sig d)) :
    app d 2 f.val (List.ofFn args) = some (.free (.inl f) args) := by
  simp [app,symbol,f.property,List.get_eq_getElem,List.getElem_ofFn]

private theorem app_comm (f : d.sig.CSym) (l r : Term (sig d)) :
    app d 3 f.val [l,r] = some (.comm (.inl f) l r) := by simp [app,symbol,f.property]

private theorem app_ac (f : d.sig.ACSym) (l r : Term (sig d)) :
    app d 4 f.val [l,r] = some (.ac (.inl f) l r) := by
  simp [app,symbol,f.property,ACRepresentation.fold]

private theorem leaf_var (id : UInt64) (s : SortId) :
    leaf d 0 id (sortCode s) = some (.var ⟨id.toNat,s⟩) := by cases s <;> rfl

private theorem leaf_table (a : d.sig.Atom) :
    leaf d 1 a.val.1 (sortCode a.val.2) = some (.atom (.inl a)) := by
  rcases a with ⟨⟨i,k⟩,h⟩
  cases k <;> simp [leaf,name,sortCode,sortOf,h,guard]

private theorem leaf_ambient (id : UInt64) (s : SortId) (h : (id,s) ∉ d.atoms) :
    leaf d 1 id (sortCode s) = some (.atom (.inr (id.toNat,s))) := by
  cases s <;> simp_all [leaf,name,sortCode,sortOf,guard]

private theorem children {ι : Type} (args : ι → Term (sig d))
    (safe : ∀ i code, write (args i) = some code → ∀ stack,
      execute d code stack = some (args i :: stack))
    (is : List ι) (cs : List (List Token)) (h : is.mapM (fun i => write (args i)) = some cs)
    (stack : List (Term (sig d))) :
    execute d cs.flatten stack = some ((is.map args).reverse ++ stack) := by
  induction is generalizing cs stack with
  | nil => cases h; rfl
  | cons i is ih =>
    cases hx : write (args i) with
    | none => simp [hx] at h
    | some head =>
      cases ht : is.mapM (fun i => write (args i)) with
      | none => simp [hx,ht] at h
      | some tail =>
        simp [hx,ht] at h
        subst cs
        simp [execute_append,safe i head hx,ih tail ht,List.append_assoc]

/-- The reader recovers every written term. -/
theorem write_executes (t : Term (sig d)) (code : List Token) (h : write t = some code)
    (stack : List (Term (sig d))) : execute d code stack = some (t :: stack) := by
  induction t generalizing code stack with
  | var v =>
    cases hp : WordEncoding.pack v.id with
    | none => simp [write,hp] at h
    | some id =>
      simp [write,hp] at h; subst code
      simp [execute,step,leaf_var,(WordEncoding.pack_iff ..).mp hp]
  | atom a =>
    cases a with
    | inl a =>
      cases h
      simp [execute,step,leaf_table]
    | inr a =>
      cases hp : WordEncoding.pack a.1 with
      | none => simp [write,hp] at h
      | some id =>
        by_cases taken : (id,a.2) ∈ d.atoms
        · simp [write,hp,taken] at h
        · simp [write,hp,taken] at h; subst code
          simp [execute,step,leaf_ambient _ _ taken,(WordEncoding.pack_iff ..).mp hp]
  | free f args ih =>
    cases f with
    | inr f => exact nomatch f
    | inl f =>
      simp only [write,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨cs,m,count,n,rfl⟩ := h
      rw [execute_append,children args ih _ _ m,Option.bind_some]
      rw [execute_single]
      simp only [List.finRange,List.map_ofFn,Function.comp_def]
      exact step_app _ _ _ _ _ _ (by decide) (by simpa using (WordEncoding.pack_iff ..).mp n)
        (app_free f args)
  | comm f l r il ir =>
    cases f with
    | inr f => exact nomatch f
    | inl f =>
      cases hl : write l with
      | none => simp [write,hl] at h
      | some left =>
        cases hr : write r with
        | none => simp [write,hl,hr] at h
        | some right =>
          simp [write,hl,hr] at h; subst code
          simp only [execute_append,il _ hl,ir _ hr,Option.bind_some]
          rw [execute_single]
          exact step_app 3 _ 2 [l,r] stack _ (by decide) rfl (app_comm f l r)
  | ac f l r il ir =>
    cases f with
    | inr f => exact nomatch f
    | inl f =>
      cases hl : write l with
      | none => simp [write,hl] at h
      | some left =>
        cases hr : write r with
        | none => simp [write,hl,hr] at h
        | some right =>
          simp [write,hl,hr] at h; subst code
          simp only [execute_append,il _ hl,ir _ hr,Option.bind_some]
          rw [execute_single]
          exact step_app 4 _ 2 [l,r] stack _ (by decide) rfl (app_ac f l r)

/-- Status 1 with the written term, or status 0 when the term has no words. -/
def emit (u : Term (sig d)) : Array (Array UInt64) :=
  match write u with
  | none => #[#[0]]
  | some ts => #[#[1],(ts.flatMap Token.words).toArray]

theorem emit_decodes (u : Term (sig d)) : Decodes d (emit u) u ∨ emit u = #[#[0]] := by
  unfold emit
  cases h : write u with
  | none => exact .inr rfl
  | some ts =>
    exact .inl ⟨_,ts,rfl,by simp [Packet.tokenize_words],write_executes u ts h []⟩

/-- The leaves the writer has words for: variables with word-sized numbers,
table names, and ambient names with word-sized numbers that no table name
shares. -/
def Proper : Term (sig d) → Prop
  | .var v => v.id < UInt64.size
  | .atom (.inl _) => True
  | .atom (.inr a) => a.1 < UInt64.size ∧ (UInt64.ofNat a.1,a.2) ∉ d.atoms
  | .free _ args => ∀ i, Proper (args i)
  | .comm _ l r | .ac _ l r => Proper l ∧ Proper r

theorem proper_equiv {a b : Term (sig d)} (h : EquivB a b) : Proper a ↔ Proper b := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | free f a b _ ih => exact forall_congr' ih
  | ac_congr _ _ _ ih ik | comm_congr _ _ _ ih ik => exact and_congr ih ik
  | ac_swap | comm_swap => exact and_comm
  | ac_assoc => exact and_assoc

private theorem image_proper (p : Term (sig d)) (σ : Substitution (sig d)) (v : Variable)
    (h : p.Occurs v) (ok : Proper (σ.apply p)) : Proper (σ.image v) := by
  induction p with
  | var w => exact h ▸ ok
  | atom => contradiction
  | free _ _ ih => obtain ⟨i,hi⟩ := h; exact ih i hi (ok i)
  | ac _ _ _ ih ik | comm _ _ _ ih ik =>
    exact h.elim (fun hl => ih hl ok.1) (fun hr => ik hr ok.2)

private theorem instance_proper (p : Term d.sig) (σ : Substitution (sig d))
    (env : ∀ v, p.Occurs v → Proper (σ.image v)) : Proper (σ.apply (liftTerm p)) := by
  induction p with
  | var v => exact env v rfl
  | atom => trivial
  | free f args ih => exact fun i => ih i (fun v hv => env v ⟨i,hv⟩)
  | ac _ _ _ il ir | comm _ _ _ il ir =>
    exact ⟨il (fun v hv => env v (.inl hv)),ir (fun v hv => env v (.inr hv))⟩

private theorem step_proper {rs : Problem d.sig} (bound : ReferenceReduction.Bound (liftRules rs))
    {a b : Term (sig d)} (h : Step (ruleRoot (liftRules rs)) a b) (ok : Proper a) : Proper b := by
  induction h with
  | root h =>
    obtain ⟨_,hr,σ,rfl,rfl⟩ := h
    have inside := bound _ hr
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
    exact instance_proper r.rhs σ fun v hv =>
      image_proper _ σ v (inside v ((embed_occurs r.rhs v).mpr hv)) ok
  | free f args i st ih =>
    intro j
    dsimp only
    split
    · exact ih (ok i)
    · exact ok j
  | comm_left _ _ _ ih | ac_left _ _ _ ih => exact ⟨ih ok.1,ok.2⟩
  | comm_right _ _ _ ih | ac_right _ _ _ ih => exact ⟨ok.1,ih ok.2⟩

/-- Rewriting with the lifted table introduces no leaf of its own. -/
theorem reduces_proper {rs : Problem d.sig} (bound : ReferenceReduction.Bound (liftRules rs))
    {a b : Term (sig d)} (red : Reduces (ruleRoot (liftRules rs)) a b) (ok : Proper a) : Proper b :=
  RootNarrowing.reduction_invariant (fun z => Proper z)
    (fun h e => (proper_equiv e).mp h)
    (fun h ⟨_,_,pre,fire,post⟩ => (proper_equiv post).mp (step_proper bound fire ((proper_equiv pre).mp h)))
    red ok

private theorem map_exists {α β : Type} (f : α → Option β) (xs : List α)
    (ok : ∀ x ∈ xs, ∃ y, f x = some y) : ∃ ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons x xs ih =>
    obtain ⟨y,h⟩ := ok x List.mem_cons_self
    obtain ⟨ys,hy⟩ := ih (fun a ha => ok a (List.mem_cons_of_mem _ ha))
    exact ⟨y::ys,by simp [h,hy]⟩

/-- The writer has words for every term with proper leaves. -/
theorem proper_write (widths : ∀ f, d.sig.arity f < UInt64.size) (t : Term (sig d))
    (ok : Proper t) : ∃ ts, write t = some ts := by
  induction t with
  | var v => simp [write,WordEncoding.pack,show v.id < UInt64.size from ok]
  | atom a =>
    cases a with
    | inl a => exact ⟨_,rfl⟩
    | inr a =>
      obtain ⟨small,free⟩ : a.1 < UInt64.size ∧ (UInt64.ofNat a.1,a.2) ∉ d.atoms := ok
      simp [write,WordEncoding.pack,small,free]
  | free f args ih =>
    cases f with
    | inr f => exact nomatch f
    | inl f =>
      obtain ⟨ts,h⟩ := map_exists _ (List.finRange _) (fun i _ => ih i (ok i))
      have fits : (info f).inputs.length < UInt64.size := widths f
      simp only [write,WordEncoding.pack,fits,ite_true,Option.bind_eq_bind,Option.pure_def,
        Option.bind_some]
      exact ⟨_,Option.bind_eq_some_iff.mpr ⟨ts,h,rfl⟩⟩
  | ac f a b ia ib =>
    cases f with
    | inr f => exact nomatch f
    | inl f =>
      obtain ⟨x,hx⟩ := ia ok.1
      obtain ⟨y,hy⟩ := ib ok.2
      simp [write,hx,hy]
  | comm f a b ia ib =>
    cases f with
    | inr f => exact nomatch f
    | inl f =>
      obtain ⟨x,hx⟩ := ia ok.1
      obtain ⟨y,hy⟩ := ib ok.2
      simp [write,hx,hy]

private theorem lift_proper (t : Term d.sig) (fits : Packet.FieldsFit t) : Proper (liftTerm t) := by
  induction t with
  | var v => exact fits
  | atom => trivial
  | free f args ih => exact fun i => ih i (fits.2 i)
  | ac _ _ _ ia ib | comm _ _ _ ia ib => exact ⟨ia fits.1,ib fits.2⟩

private theorem leaf_proper {k id arg : UInt64} {t : Term (sig d)} (h : leaf d k id arg = some t) :
    Proper t := by
  unfold leaf at h
  simp only [guard,Bind.bind,Option.bind] at h
  split at h <;> try contradiction
  split at h
  · cases h; exact UInt64.toNat_lt_size _
  · split at h <;> try contradiction
    cases h
    unfold name
    split
    · trivial
    · next free => exact ⟨UInt64.toNat_lt_size _,by simpa using free⟩

private theorem fold_proper (f : (sig d).ACSym) (t : Term (sig d)) (ts : List (Term (sig d)))
    (h : Proper t) (hs : ∀ a ∈ ts, Proper a) : Proper (ACRepresentation.fold f t ts) := by
  induction ts generalizing t with
  | nil => exact h
  | cons a as ih => exact ⟨h,ih a (hs _ List.mem_cons_self) (fun b hb => hs b (.tail _ hb))⟩

private theorem app_proper {k id : UInt64} {children : List (Term (sig d))} {t : Term (sig d)}
    (ok : app d k id children = some t) (bounded : ∀ a ∈ children, Proper a) : Proper t := by
  unfold app at ok
  split at ok
  · simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at ok
    obtain ⟨f,_,h⟩ := ok
    split at h <;> try contradiction
    cases h
    exact fun i => bounded _ (List.get_mem ..)
  · split at ok
    · simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at ok
      obtain ⟨_,_,h⟩ := ok
      split at h <;> try contradiction
      cases h
      exact ⟨bounded _ (by simp),bounded _ (by simp)⟩
    · split at ok
      · simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at ok
        obtain ⟨_,_,h⟩ := ok
        split at h <;> try contradiction
        cases h
        exact ⟨bounded _ (by simp),fold_proper _ _ _ (bounded _ (by simp))
          (fun a ha => bounded a (by simp [ha]))⟩
      · contradiction

/-- Every term of a node index has proper leaves. -/
theorem fetch_proper {base : Array (Term d.sig)} {more : Array (Term (sig d))}
    (hb : ∀ a ∈ base, Packet.FieldsFit a) (hm : ∀ a ∈ more, Proper a) {i : Nat} {t : Term (sig d)}
    (h : fetch base more i = some t) : Proper t := by
  unfold fetch at h
  split at h
  · cases h
    exact lift_proper _ (hb _ (Array.getElem_mem _))
  · exact hm _ (Array.mem_of_getElem? h)

private theorem node_proper {base : Array (Term d.sig)} {more : Array (Term (sig d))}
    (hb : ∀ a ∈ base, Packet.FieldsFit a) (hm : ∀ a ∈ more, Proper a) {row : Array UInt64}
    {t : Term (sig d)} (h : node base more row = some t) : Proper t := by
  unfold node at h
  split at h <;> try contradiction
  split at h
  · split at h <;> try contradiction
    exact leaf_proper h
  · simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at h
    obtain ⟨cs,hc,ht⟩ := h
    exact app_proper ht (children_fits _ _ (fun _ _ h => fetch_proper hb hm h) _ _ hc)

theorem extend_proper {base : Array (Term d.sig)} (hb : ∀ a ∈ base, Packet.FieldsFit a)
    {extra : Array (Array UInt64)} {more : Array (Term (sig d))} (h : extend base extra = some more) :
    ∀ a ∈ more, Proper a := by
  unfold extend at h
  rw [← Array.foldlM_toList] at h
  have start : ∀ a ∈ (#[] : Array (Term (sig d))), Proper a := fun _ ha => by simp at ha
  generalize (#[] : Array (Term (sig d))) = init at h start
  generalize extra.toList = xs at h
  induction xs generalizing init with
  | nil => cases h; exact start
  | cons r rs ih =>
    simp only [List.foldlM_cons,Option.bind_eq_bind,Option.bind_assoc,Option.bind_eq_some_iff] at h
    obtain ⟨t,ht,a,ha,tail⟩ := h
    cases ha
    apply ih _ (h := tail)
    intro a ha
    rcases Array.mem_push.mp ha with old | rfl
    · exact start a old
    · exact node_proper hb start ht

end Tamarin.SessionWire

/-! Reduction along one rewrite path on the certified table of a session.
Status 1 carries the normal form, 3 requests more rewrite depth, and 0
denotes a malformed packet. -/
namespace Tamarin.SessionReductionWire
open TotalUnifyWire TableAmbient SessionWire Rewriting MaudeOperations

def input (ds : Array UInt64) (ns : Array (Array UInt64)) (es : Array UInt64)
    (extra : Array (Array UInt64)) (root : UInt64) :
    Option ((d : Dictionary) × Problem d.sig × Term (sig d)) := do
  let ⟨d,ts⟩ ← graph ds ns
  let rules ← equations ts es.toList
  let more ← extend ts extra
  let t ← fetch ts more root.toNat
  return ⟨d,rules,t⟩

/-- The table of a call is the table of the rules-only packet. -/
theorem input_table {ds ns es extra root d rs t}
    (decoded : input ds ns es extra root = some ⟨d,rs,t⟩) :
    TableWire.input ds ns es #[] = some ⟨d,rs,[]⟩ := by
  unfold input at decoded
  unfold TableWire.input
  cases graph : TotalUnifyWire.graph ds ns with
  | none => simp [graph] at decoded
  | some graphPair =>
    obtain ⟨dict,terms⟩ := graphPair
    cases eqs : TotalUnifyWire.equations terms es.toList with
    | none => simp [graph,eqs] at decoded
    | some rules =>
      cases ext : extend terms extra with
      | none => simp [graph,eqs,ext] at decoded
      | some more =>
        cases got : fetch terms more root.toNat with
        | none => simp [graph,eqs,ext,got] at decoded
        | some u =>
          simp [graph,eqs,ext,got] at decoded
          obtain ⟨rfl,h⟩ := decoded
          cases eq_of_heq h
          simp [eqs]

/-- The arities of the table and the leaves of the term of a call fit words. -/
theorem input_proper {ds ns es extra root d rs t}
    (decoded : input ds ns es extra root = some ⟨d,rs,t⟩) :
    (∀ f, d.sig.arity f < UInt64.size) ∧ Proper t := by
  unfold input at decoded
  cases graph : TotalUnifyWire.graph ds ns with
  | none => simp [graph] at decoded
  | some graphPair =>
    obtain ⟨dict,terms⟩ := graphPair
    cases eqs : TotalUnifyWire.equations terms es.toList with
    | none => simp [graph,eqs] at decoded
    | some rules =>
      cases ext : extend terms extra with
      | none => simp [graph,eqs,ext] at decoded
      | some more =>
        cases got : fetch terms more root.toNat with
        | none => simp [graph,eqs,ext,got] at decoded
        | some u =>
          simp [graph,eqs,ext,got] at decoded
          obtain ⟨rfl,h⟩ := decoded
          cases eq_of_heq h
          have fits := graph_fieldsFit graph
          exact ⟨graph_widths graph,fetch_proper fits (extend_proper fits ext) got⟩

def run (ds : Array UInt64) (ns : Array (Array UInt64)) (es : Array UInt64)
    (extra : Array (Array UInt64)) (root fuel : UInt64) : Array (Array UInt64) :=
  match input ds ns es extra root with
  | some ⟨_,rs,t⟩ =>
    match CertifiedReductionWire.path (liftRules rs) fuel.toNat t with
    | some u => SessionWire.emit u
    | none => #[#[3]]
  | none => #[#[0]]

abbrev Kernel := Array UInt64 → Array (Array UInt64) → Array UInt64 → Array (Array UInt64) →
  UInt64 → UInt64 → Array (Array UInt64)

/-- The reply decodes to the unique normal form of the term that the further
rows denote, under the lifted rules of the table. -/
def Answer (d : Dictionary) (rs : Problem d.sig) (t : Term (sig d)) (wire : Array (Array UInt64)) :
    Prop :=
  ∃ u, Decodes d wire u ∧ ReductionReply (ruleRoot (liftRules rs)) t u

/-- With a certified table every reply is the unique normal form or a request
for more depth, and every depth that bounds all rewrite paths from the term
under the lifted rules produces the normal form. The bound is on the rewrite
relation, not on any search. -/
structure Correct (kernel : Kernel) : Prop where
  malformed : ∀ ds ns es extra root n, input ds ns es extra root = none →
    kernel ds ns es extra root n = #[#[0]]
  valid : ∀ ds ns es extra root n d rs t, input ds ns es extra root = some ⟨d,rs,t⟩ →
    CertifiedTableWire.Certified rs →
    Answer d rs t (kernel ds ns es extra root n) ∨ kernel ds ns es extra root n = #[#[3]]
  completes : ∀ ds ns es extra root d rs t, input ds ns es extra root = some ⟨d,rs,t⟩ →
    CertifiedTableWire.Certified rs → ∀ n : UInt64,
      CheckedReduction.Within (liftRules rs) n.toNat t → Answer d rs t (kernel ds ns es extra root n)

private theorem answer {ds ns es extra root} {d : Dictionary} {rs : Problem d.sig} {t u : Term (sig d)}
    (decoded : input ds ns es extra root = some ⟨d,rs,t⟩)
    (bound : ReferenceReduction.Bound (liftRules rs))
    (can : CanonicalPresentation (ruleRoot (liftRules rs))) {k : Nat}
    (found : CertifiedReductionWire.path (liftRules rs) k t = some u) :
    Answer d rs t (SessionWire.emit u) := by
  have reply := CertifiedReductionWire.path_reply bound can found
  obtain ⟨widths,ok⟩ := input_proper decoded
  obtain ⟨ts,written⟩ := proper_write widths u (reduces_proper bound reply.normalForm.1 ok)
  rcases emit_decodes u with decodes | none_
  · exact ⟨u,decodes,reply⟩
  · simp [SessionWire.emit,written] at none_

theorem correct : Correct run where
  malformed := fun _ _ _ _ _ _ h => by simp [run,h]
  valid := by
    intro ds ns es extra root n d rs t decoded ⟨bound,can,_⟩
    cases found : CertifiedReductionWire.path (liftRules rs) n.toNat t with
    | none => exact .inr (by simp [run,decoded,found])
    | some u =>
      have out : run ds ns es extra root n = SessionWire.emit u := by simp [run,decoded,found]
      exact .inl (out ▸ answer decoded bound can found)
  completes := by
    intro ds ns es extra root d rs t decoded ⟨bound,can,_⟩ n tree
    obtain ⟨_,chosen⟩ := CheckedReduction.choose_of_within bound _ _ tree
    obtain ⟨u,found⟩ := CertifiedReductionWire.path_some chosen
    have out : run ds ns es extra root n = SessionWire.emit u := by simp [run,decoded,found]
    exact out ▸ answer decoded bound can found

end Tamarin.SessionReductionWire

/-! The variant certificate checker on the certified table of a session. The
observation roots and the node pairs of the proposed variants index the table
rows and the further rows. Replies are those of `VariantCheckWire`. -/
namespace Tamarin.SessionVariantCheckWire
open TotalUnifyWire TableAmbient SessionWire Rewriting MaudeOperations

def input (ds : Array UInt64) (ns : Array (Array UInt64)) (es : Array UInt64)
    (extra : Array (Array UInt64)) (observed : Array UInt64) (family : Array (Array UInt64)) :
    Option ((d : Dictionary) × Problem d.sig × List (Term (sig d)) × List (Substitution (sig d))) := do
  let ⟨d,ts⟩ ← graph ds ns
  let rules ← equations ts es.toList
  let more ← extend ts extra
  let terms ← observed.toList.mapM fun id => fetch ts more id.toNat
  let members ← family.toList.mapM fun row =>
    (pairs ts more row.toList).bind VariantCheckWire.assign
  return ⟨d,rules,terms,members⟩

/-- The table of a call is the table of the rules-only packet. -/
theorem input_table {ds ns es extra roots family d rs q members}
    (decoded : input ds ns es extra roots family = some ⟨d,rs,q,members⟩) :
    TableWire.input ds ns es #[] = some ⟨d,rs,[]⟩ := by
  unfold input at decoded
  unfold TableWire.input
  cases graph : TotalUnifyWire.graph ds ns with
  | none => simp [graph] at decoded
  | some graphPair =>
    obtain ⟨dict,terms⟩ := graphPair
    cases eqs : TotalUnifyWire.equations terms es.toList with
    | none => simp [graph,eqs] at decoded
    | some rules =>
      cases ext : extend terms extra with
      | none => simp [graph,eqs,ext] at decoded
      | some more =>
        cases obs : roots.toList.mapM (fun (i : UInt64) => fetch terms more i.toNat) with
        | none => simp [graph,eqs,ext,obs] at decoded
        | some qs =>
          cases fam : family.toList.mapM
              (fun row => (pairs terms more row.toList).bind VariantCheckWire.assign) with
          | none => simp [graph,eqs,ext,obs,fam] at decoded
          | some ms =>
            simp [graph,eqs,ext,obs,fam] at decoded
            obtain ⟨rfl,h⟩ := decoded
            cases eq_of_heq h
            simp [eqs]

def run (ds : Array UInt64) (ns : Array (Array UInt64)) (es : Array UInt64)
    (extra : Array (Array UInt64)) (roots : Array UInt64) (family : Array (Array UInt64))
    (fuel work : UInt64) : Array (Array UInt64) :=
  match input ds ns es extra roots family with
  | none => #[#[0]]
  | some ⟨_,rs,q,members⟩ =>
    VariantCheckWire.reply (VariantCertificate.check (liftRules rs) q members fuel.toNat work.toNat)

abbrev Kernel := Array UInt64 → Array (Array UInt64) → Array UInt64 → Array (Array UInt64) →
  Array UInt64 → Array (Array UInt64) → UInt64 → UInt64 → Array (Array UInt64)

/-- Only status 1 accepts. On a canonical presentation of the lifted table an
accepted family is a complete set of variants of the observations that the
further rows denote, and its members are the proposed substitutions. -/
structure Correct (kernel : Kernel) : Prop where
  malformed : ∀ ds ns es extra roots family fuel work, input ds ns es extra roots family = none →
    kernel ds ns es extra roots family fuel work = #[#[0]]
  status : ∀ ds ns es extra roots family fuel work d rs q members,
    input ds ns es extra roots family = some ⟨d,rs,q,members⟩ →
    kernel ds ns es extra roots family fuel work = #[#[1]] ∨
      (∃ reason index, kernel ds ns es extra roots family fuel work = #[#[2,reason,index]]) ∨
      kernel ds ns es extra roots family fuel work = #[#[3]]
  accepted : ∀ ds ns es extra roots family fuel work d rs q members,
    input ds ns es extra roots family = some ⟨d,rs,q,members⟩ →
    kernel ds ns es extra roots family fuel work = #[#[1]] →
    CanonicalPresentation (ruleRoot (liftRules rs)) →
    ∃ rows, VariantReply (ruleRoot (liftRules rs)) q [] rows ∧ rows.length = members.length ∧
      ∀ pair ∈ members.zip rows, ∀ v, Observed q v → pair.2.subst.image v = pair.1.image v

theorem correct : Correct run where
  malformed := fun ds ns es extra roots family fuel work h => by simp [run,h]
  status := by
    intro ds ns es extra roots family fuel work d rs q members decoded
    simp only [run,decoded]
    cases VariantCertificate.check (liftRules rs) q members fuel.toNat work.toNat with
    | accepted => exact .inl rfl
    | rejected reason index => exact .inr (.inl ⟨_,_,rfl⟩)
    | exhausted => exact .inr (.inr rfl)
  accepted := by
    intro ds ns es extra roots family fuel work d rs q members decoded ok canonical
    simp only [run,decoded] at ok
    exact VariantCertificate.accepted_reply canonical (VariantCheckWire.reply_accepted ok)

end Tamarin.SessionVariantCheckWire
