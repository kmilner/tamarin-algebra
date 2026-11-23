import Tamarin.TotalUnifyPacket
import Tamarin.CallerFreshening
import Tamarin.UnavailableSort

/-! Names for the variables that the answers of the unifier add to a query.

The caller knows a variable by a name hint, an index and a sort, and a request
of the unifier names it by a row number alone. An answer of the unifier is a
substitution whose range mixes query variables with further ones, and the
caller reads the range of an answer as fresh: no variable of it may be one of
its own. Which variables the caller gets is decided here. The procedure of
this module (`run`) receives the label of every query variable (the
identifier of its hint, and its index) and, for each answer, the variables of
its range. It replies with a table for each answer the caller keeps, which
gives every range variable a target: a label, or a query variable.

The caller does not rename anything. It reads the reply of the unifier
through the tables, as `apply` does: the token of a range variable is the
token of its label, and a row that binds a query variable to a range variable
whose target is that very query variable is left out. A reply that cannot be
read this way has no reading: a variable without a target, a target that is a
query variable anywhere but in such a row, or an answer without a table that
the caller's module could have used.

There are two ways a label is chosen. Without a proposal every range variable
gets the hint `0` and an index above every index of the query, in the order
in which the caller lists them; a caller that sets `low` gets indices the
query does not use where none are left above it. A proposal lists a label
for every range variable. It is used when, in each answer, no two variables get one target at
one sort; a label of a query variable of that sort makes that variable the
target. A proposal that fails is ignored as a whole.

The statement of this module (`Correct`) is about every reply of the unifier
that decodes to a family for a query, and every way to call the procedure: if
the reply can be read through the tables, the reading decodes to a family
that is the given one up to an injective renaming of each answer, hence
complete when the given one is, and no label of its range is the label of a
query variable of the same sort. The tables are tested (`admissible`) on the
very words the caller reads, so nothing has to be proved of how they are
made. -/
namespace Tamarin.UnifierNames
open TotalUnifyWire
variable {d : Dictionary}

/-- The caller's identifier of a name hint, and an index. -/
abbrev Label := UInt64 × UInt64

/-- The label of the variable in row `v.id` of the request: words `2 v.id`
and `2 v.id + 1` of the table. -/
def label (names : Array UInt64) (v : Variable) : Option Label := do
  return (← names[2 * v.id]?, ← names[2 * v.id + 1]?)

/-- The variable a label stands for. Its identifier is at least `base`, so
with `base` above the query it is no variable of the query, and distinct
labels or sorts give distinct variables. -/
def named (base : Nat) (l : Label) (s : SortId) : Variable :=
  ⟨base + (l.1.toNat * UInt64.size + l.2.toNat), s⟩

theorem named_sort (base : Nat) (l : Label) (s : SortId) : (named base l s).sort = s := rfl

/-- The least identifier above the variables of the query. -/
abbrev base (p : Problem d.sig) : Nat := VariablePermutation.freshBound p.variables

def kindOfSort : SortId → UInt64
  | .pub => 5 | .fresh => 6 | .msg => 7 | .node => 8 | .nat => 9

def sortOfKind (k : UInt64) : Option SortId :=
  if k == 5 then some .pub else if k == 6 then some .fresh else if k == 7 then some .msg
  else if k == 8 then some .node else if k == 9 then some .nat else none

theorem sortOfKind_kind (s : SortId) : sortOfKind (kindOfSort s) = some s := by cases s <;> decide

/-- A token of kind 5 to 9 is a labelled variable of the sort the kind
stands for, with the index as its second word and the hint as its third. No
other variable can be written. Every other token is read as in a reply of the
unifier. -/
def step (d : Dictionary) (base : Nat) (stack : List (Term d.sig)) (t : Token) :
    Option (List (Term d.sig)) :=
  match sortOfKind t.kind with
  | some s => some (.var (named base (t.arg, t.id) s) :: stack)
  | none => if t.kind == 0 then none else Packet.step d stack t

def execute (d : Dictionary) (base : Nat) (code : List Token) (stack : List (Term d.sig)) :=
  code.foldlM (step d base) stack

def readBinding (d : Dictionary) (base : Nat) (row : Array UInt64) : Option (Variable × Term d.sig) := do
  let v :: s :: words := row.toList | none
  guard (s ≤ 4)
  let [t] ← execute d base (← Packet.tokenize words) [] | none
  return (⟨v.toNat, sortOf s⟩, t)

/-- An arm is a separator and then one row for each query variable it binds,
in the order of the query. A variable without a row is left alone. -/
inductive Payload (d : Dictionary) (base : Nat) (vs : List Variable) :
    List (Array UInt64) → List (Substitution d.sig) → Prop where
  | nil : Payload d base vs [] []
  | cons {bindings rest images σ answers} :
      bindings.mapM (readBinding d base) = some images →
      (images.map Prod.fst).Sublist vs →
      (∀ v ∈ vs, σ.image v = (images.lookup v).getD (.var v)) →
      Payload d base vs rest answers → Payload d base vs (#[] :: bindings ++ rest) (σ :: answers)

def Decodes (p : Problem d.sig) (wire : Array (Array UInt64)) (answers : List (Substitution d.sig)) :=
  ∃ rows, wire.toList = #[1] :: rows ∧ Payload d (base p) p.variables.eraseDups rows answers

/-- Every query variable has a label, and two of one sort have different ones. -/
structure Labelled (names : Array UInt64) (p : Problem d.sig) : Prop where
  total : ∀ v, p.Occurs v → (label names v).isSome
  distinct : ∀ u v, p.Occurs u → p.Occurs v → u.sort = v.sort → label names u = label names v → u = v

/-- The answer leaves a query variable alone or sends it to a term whose
variables are labelled, with labels that no query variable of their sort has. -/
def Fresh (names : Array UInt64) (p : Problem d.sig) (σ : Substitution d.sig) : Prop :=
  ∀ v, p.Occurs v → σ.image v = .var v ∨
    ∀ w, (σ.image v).Occurs w → ∃ l, w = named (base p) l w.sort ∧
      ∀ u, p.Occurs u → u.sort = w.sort → label names u ≠ some l

/-- Every variable of the range has the hint `0` and an index above every
index of the query. -/
def Above (names : Array UInt64) (p : Problem d.sig) (σ : Substitution d.sig) : Prop :=
  ∀ v, p.Occurs v → ∀ w, (σ.image v).Occurs w → ∃ i : UInt64, w = named (base p) (0, i) w.sort ∧
    ∀ u l, p.Occurs u → label names u = some l → l.2 < i

/-- Every variable of the range has the hint `0` and an index that no
variable of the query has. -/
def Unused (names : Array UInt64) (p : Problem d.sig) (σ : Substitution d.sig) : Prop :=
  ∀ v, p.Occurs v → ∀ w, (σ.image v).Occurs w → ∃ i : UInt64, w = named (base p) (0, i) w.sort ∧
    ∀ u l, p.Occurs u → label names u = some l → l.2 ≠ i

/-- The answers the caller keeps: all of them, or those without a variable of
the sort of natural numbers when its module has no such sort. -/
def kept (nat : Bool) (p : Problem d.sig) (answers : List (Substitution d.sig)) :=
  if nat then answers else answers.filter (UnavailableSort.noNatWitness p)

/-! ### Reading a reply of the unifier through tables -/

/-- What a range variable becomes: a labelled variable, or the query variable
in the given row of the arm, which is bound to it alone. -/
inductive Target where
  | name (l : Label)
  | self (row : Nat)
  deriving DecidableEq

structure Entry where
  source : Variable
  target : Target

/-- Five words for each range variable: its identifier and sort, then `0`
with the hint and the index of its label, or `1` with the row of a query
variable. -/
def entries : List UInt64 → Option (List Entry)
  | id :: sort :: kind :: a :: b :: rest =>
    if sort ≤ 4 then
      (entries rest).bind fun es =>
        if kind == 0 then some (⟨⟨id.toNat, sortOf sort⟩, .name (a, b)⟩ :: es)
        else if kind == 1 then some (⟨⟨id.toNat, sortOf sort⟩, .self a.toNat⟩ :: es)
        else none
    else none
  | [] => some []
  | _ => none

/-- The tables of a family: the identifier and sort words of the query
variables, in the order of the rows of every arm, and for each arm that is
kept its position in the reply and its entries. -/
structure Tables where
  heads : List UInt64
  arms : List (Nat × List Entry)

def tables (words : Array (Array UInt64)) : Option Tables :=
  match words.toList with
  | status :: heads :: rows =>
    if status = #[1] then
      (rows.mapM fun (row : Array UInt64) => match row.toList with
        | arm :: rest => (entries rest).map fun es => (arm.toNat, es)
        | [] => none).map fun arms => ⟨heads.toList, arms⟩
    else none
  | _ => none

def find (es : List Entry) (w : Variable) : Option Target :=
  (es.find? fun e => e.source == w).map (·.target)

def tokenVariable (t : Token) : Option Variable :=
  if t.kind == 0 then some ⟨t.id.toNat, sortOf t.arg⟩ else none

/-- The token of a variable becomes the token of its label. -/
def renameToken (es : List Entry) (t : Token) : Option Token :=
  match tokenVariable t with
  | some w =>
    match find es w with
    | some (.name l) => some ⟨kindOfSort w.sort, l.2, l.1⟩
    | _ => none
  | none => some t

/-- A binding row of a reply of the unifier, with its image left in tokens. -/
structure Row where
  key : UInt64
  sort : UInt64
  code : List Token

def Row.variable (r : Row) : Variable := ⟨r.key.toNat, sortOf r.sort⟩

def Row.variables (r : Row) : List Variable := r.code.filterMap tokenVariable

def parseRow (row : Array UInt64) : Option Row :=
  match row.toList with
  | key :: sort :: words => (Packet.tokenize words).map fun code => ⟨key, sort, code⟩
  | _ => none

/-- An empty row closes the rows gathered after it into an arm. -/
def collect (row : Array UInt64) (s : List (Array UInt64) × List (List (Array UInt64))) :
    List (Array UInt64) × List (List (Array UInt64)) :=
  if row.size = 0 then ([], s.1 :: s.2) else (row :: s.1, s.2)

/-- The row binds its query variable to a range variable, and nothing else,
whose target is the query variable of this row. -/
def stands (es : List Entry) (row : Nat) (r : Row) : Bool :=
  match r.code with
  | [t] =>
    match tokenVariable t with
    | some w => find es w == some (.self row)
    | none => false
  | _ => false

/-- The row with its variables renamed, or nothing for a row that binds a
query variable to the variable that takes its place. -/
def emitRow (es : List Entry) (e : Row × Nat) : Option (Option (Array UInt64)) :=
  if stands es e.2 e.1 then some none
  else (e.1.code.mapM (renameToken es)).map fun (code : List Token) =>
    some (e.1.key :: e.1.sort :: code.flatMap Token.words).toArray

def emitArm (es : List Entry) (arm : List Row) : Option (List (Array UInt64)) :=
  (arm.zipIdx.mapM (emitRow es)).map fun rows => #[] :: rows.filterMap id

/-- No variable of the arm has the sort of natural numbers. -/
def natFree (arm : List Row) : Bool :=
  arm.all fun r => r.variables.all fun w => w.sort != .nat

/-- The arms with a table, in order. An arm without one must have a variable
of the sort of natural numbers, and the caller's module must lack that sort. -/
def select (nat : Bool) : List (List Row × Nat) → List (Nat × List Entry) →
    Option (List (List (Array UInt64)))
  | [], [] => some []
  | [], _ :: _ => none
  | arm :: arms, [] => if !nat && !natFree arm.1 then select nat arms [] else none
  | arm :: arms, t :: ts =>
    if t.1 = arm.2 then (emitArm t.2 arm.1).bind fun out => (select nat arms ts).map (out :: ·)
    else if !nat && !natFree arm.1 then select nat arms (t :: ts) else none

/-- The reply of the unifier read through the tables: the status row and, for
each arm with a table, a separator and the rows the table leaves. Every arm
must list the query variables as the tables do. -/
def apply (words : Array (Array UInt64)) (nat : Bool) (reply : Array (Array UInt64)) :
    Option (Array (Array UInt64)) :=
  (tables words).bind fun t =>
    let state := reply.foldr collect ([], [])
    if state.1 = [#[1]] then
      (state.2.mapM fun (rows : List (Array UInt64)) => rows.mapM parseRow).bind fun arms =>
        if arms.all (fun arm => (arm.flatMap fun r => [r.key, r.sort]) = t.heads) then
          (select nat arms.zipIdx t.arms).map fun out => (#[1] :: out.flatten).toArray
        else none
    else none

/-- The procedure takes the labels of the query variables, their identifier
and sort words, the range variables of each arm as identifier and sort words,
a proposal, whether the caller's module has natural numbers, and whether the
caller settles for indices the query does not use where none are left above
its indices. -/
abbrev Kernel := Array UInt64 → Array UInt64 → Array (Array UInt64) → Array (Array UInt64) → Bool →
  Bool → Array (Array UInt64)

/-- What a reading through the tables of the procedure means, for a reply
that decodes to a family of answers of a request of the unifier. The
procedure does not see the reply, and nothing is assumed about what it is
told of it. -/
structure Correct (kernel : Kernel) : Prop where
  valid : ∀ ds ns es names heads ranges proposal nat low reply d p raw named,
    input ds ns es = some ⟨d, p⟩ → Packet.Decodes p reply raw →
    apply (kernel names heads ranges proposal nat low) nat reply = some named →
    ∃ answers, Decodes p named answers ∧
      (answers ≠ [] → Labelled names p) ∧
      OutputRefinement ⟨p, []⟩ (kept nat p raw) answers ∧
      (∀ σ ∈ answers, Fresh names p σ) ∧
      (proposal = #[] → ∀ σ ∈ answers, Unused names p σ) ∧
      (proposal = #[] → low = false → ∀ σ ∈ answers, Above names p σ)

/-! ### The procedure -/

/-- The positions of the entries of a list, as a table of buckets. -/
structure Index (α : Type) where
  key : α → Nat
  table : Array (List (α × Nat))
  length : Nat

def Index.of {α : Type} (key : α → Nat) (xs : List α) : Index α :=
  ⟨key, Buckets.index key (xs.length + 1) 0 xs, xs.length⟩

/-- The first position of an entry, or the length of the list. -/
def Index.position {α : Type} [BEq α] (ix : Index α) (x : α) : Nat :=
  Buckets.lookup ix.key ix.table ix.length x

theorem Index.position_of {α : Type} [BEq α] [LawfulBEq α] (key : α → Nat) (xs : List α) :
    (Index.of key xs).position = fun x => xs.idxOf x := by
  funext x
  simpa [Index.of, Index.position] using Buckets.lookup_index key (xs.length + 1) (by omega) 0 xs x

/-- Every entry of the list is at the position found for it, counted from
`i`: no entry occurs twice. -/
def distinctFrom {α : Type} (position : α → Nat) : Nat → List α → Bool
  | _, [] => true
  | i, x :: xs => position x == i && distinctFrom position (i + 1) xs

def headVariables : List UInt64 → Option (List Variable)
  | key :: sort :: rest => (headVariables rest).map (⟨key.toNat, sortOf sort⟩ :: ·)
  | [] => some []
  | _ => none

def queryLabels (names : Array UInt64) (vs : List Variable) : Option (List (Variable × Label)) :=
  vs.mapM fun v => (label names v).map fun l => (v, l)

def queryKeys (qs : List (Variable × Label)) : List (Label × SortId) :=
  qs.map fun q => (q.2, q.1.sort)

def queryIndices (qs : List (Variable × Label)) : List Nat :=
  qs.map fun q => q.2.2.toNat

def labelKey (k : Label × SortId) : Nat := k.1.2.toNat + 31 * k.1.1.toNat

def entryKey (e : Entry) : Target × SortId := (e.target, e.source.sort)

def targetKey (k : Target × SortId) : Nat :=
  match k.1 with
  | .name l => l.2.toNat
  | .self row => row

/-- The least index above the indices of the query. -/
def indexBound (qs : List (Variable × Label)) : Nat :=
  qs.foldl (fun b q => max b (q.2.2.toNat + 1)) 0

/-- What the procedure keeps of the query: its variables with their labels,
the positions of the labels by sort, and the least index above its indices. -/
structure Query where
  qs : Array (Variable × Label)
  position : Label × SortId → Nat
  bound : Nat

/-- The query of the given identifier and sort words, if every variable has
a label and no two of one sort have the same. -/
def query (names heads : Array UInt64) : Option Query :=
  ((headVariables heads.toList).bind (queryLabels names)).bind fun qs =>
    let keys := queryKeys qs
    let position := (Index.of labelKey keys).position
    if distinctFrom position 0 keys then some ⟨qs.toArray, position, indexBound qs⟩ else none

/-- The test of the table of an arm: no target twice at one sort, no variable
of a sort the caller lacks, a label only if no query variable of that sort
has it, and a query variable only of the same sort. When `above` is set,
every target is a label with the hint `0` and an index from the bound on, and
when `unused` is set, with the hint `0` and an index of no query variable. -/
def tableOK (q : Query) (nat above unused : Bool) (es : List Entry) : Bool :=
  distinctFrom (Index.of targetKey (es.map entryKey)).position 0 (es.map entryKey) &&
  es.all fun e =>
    (nat || e.source.sort != .nat) &&
    match e.target with
    | .name l =>
      !(q.position (l, e.source.sort) < q.qs.size) &&
      (!above || (l.1 == 0 && q.bound ≤ l.2.toNat)) &&
      (!unused || (l.1 == 0 && q.qs.all fun v => v.2.2 != l.2))
    | .self row =>
      !above && !unused &&
      (match q.qs[row]? with
        | some v => v.1.sort == e.source.sort
        | none => false)

/-- The test of the tables of a family, on the words the caller will read. -/
def admissible (heads : Array UInt64) (q : Query) (nat above unused : Bool)
    (words : Array (Array UInt64)) : Bool :=
  match tables words with
  | none => false
  | some t => t.heads = heads.toList && t.arms.all fun arm => tableOK q nat above unused arm.2

/-- The least index from `c` on that is not in use, among the next `fuel`. -/
def unused (used : Nat → Bool) : Nat → Nat → Nat
  | 0, c => c
  | fuel + 1, c => if used c then unused used fuel (c + 1) else c

def unusedFrom (used : Nat → Bool) (fuel : Nat) (c : Nat) : Nat → List Nat
  | 0 => []
  | count + 1 =>
    let next := unused used fuel c
    next :: unusedFrom used fuel (next + 1) count

/-- The indices of `count` further variables: the least indices the query
does not use, in increasing order, all moved up by the same amount so that
the first is `bound`, the least index above the query. With `low` they are
not moved. -/
def defaultIndices (used : Nat → Bool) (fuel bound count : Nat) (low : Bool) : List Nat :=
  match unusedFrom used fuel 0 count with
  | [] => []
  | first :: rest => if low then first :: rest else (first :: rest).map (· + (bound - first))

def labels : List UInt64 → Option (List Label)
  | hint :: index :: rest => (labels rest).map ((hint, index) :: ·)
  | [] => some []
  | _ => none

/-- The words of an entry: a label of a query variable of the sort stands for
that variable. -/
def entryWords (q : Query) (id sort : UInt64) (l : Label) (acc : Array UInt64) : Array UInt64 :=
  let row := q.position (l, sortOf sort)
  if row < q.qs.size then ((((acc.push id).push sort).push 1).push (UInt64.ofNat row)).push 0
  else ((((acc.push id).push sort).push 0).push l.1).push l.2

def armWords (q : Query) : List UInt64 → List Label → Array UInt64 → Option (Array UInt64)
  | id :: sort :: range, l :: ls, acc => armWords q range ls (entryWords q id sort l acc)
  | [], [], acc => some acc
  | _, _, _ => none

def hasNat : List UInt64 → Bool
  | _ :: sort :: rest => sort == 4 || hasNat rest
  | _ => false

/-- The tables for the arms the caller keeps, with the labels of a proposal
or the default ones. Nothing is proved of them: `run` tests what it returns. -/
def tablesFor (q : Query) (heads : Array UInt64) (ranges : Array (Array UInt64))
    (proposal : Option (List (Array UInt64))) (nat low : Bool) : Option (Array (Array UInt64)) :=
  let kept := ranges.toList.zipIdx.filter fun (e : Array UInt64 × Nat) => nat || !hasNat e.1.toList
  let rows : Option (List (Array UInt64)) := match proposal with
    | some rows =>
      if rows.length = kept.length then
        (kept.zip rows).mapM fun (e : (Array UInt64 × Nat) × Array UInt64) =>
          (labels e.2.toList).bind fun ls => armWords q e.1.1.toList ls #[UInt64.ofNat e.1.2]
      else none
    | none =>
      let indices := Index.of id (queryIndices q.qs.toList)
      let used := fun i => indices.position i < indices.length
      kept.mapM fun (e : Array UInt64 × Nat) =>
        let indices := defaultIndices used (q.qs.size + 1) q.bound (e.1.size / 2) low
        if indices.all (· < UInt64.size) then
          armWords q e.1.toList (indices.map fun i => ((0 : UInt64), UInt64.ofNat i))
            #[UInt64.ofNat e.2]
        else none
  rows.map fun rows => (#[1] :: heads :: rows).toArray

/-- The first to pass its test: the proposed tables, the default tables with
indices above the query, and where the caller settles for them the default
tables with indices the query does not use. -/
def choose (heads : Array UInt64) (q : Query) (nat low : Bool) (proposed : Array (Array UInt64))
    (defaults : Bool → Array (Array UInt64)) : Array (Array UInt64) :=
  if admissible heads q nat false false proposed then proposed
  else
    let high := defaults false
    if admissible heads q nat true false high then high
    else if low then
      let lower := defaults true
      if admissible heads q nat false true lower then lower else #[#[0]]
    else #[#[0]]

def run (names heads : Array UInt64) (ranges proposal : Array (Array UInt64)) (nat low : Bool) :
    Array (Array UInt64) :=
  match query names heads with
  | none => #[#[0]]
  | some q =>
    choose heads q nat low
      (if proposal.size = 0 then #[#[0]]
        else (tablesFor q heads ranges (some proposal.toList) nat false).getD #[#[0]])
      fun low => (tablesFor q heads ranges none nat low).getD #[#[0]]

/-! ### Proofs -/

-- The identifier of a labelled variable is a sum with a multiple of `2 ^ 64`,
-- which a definitional check must never start to evaluate.
attribute [local irreducible] named

/-- Lists related entry by entry. -/
inductive Related {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : Related R [] []
  | cons {a b as bs} : R a b → Related R as bs → Related R (a :: as) (b :: bs)

theorem mapM_cons_some {α β : Type} (f : α → Option β) (a : α) (l : List α) (ys : List β) :
    (a :: l).mapM f = some ys ↔ ∃ y ys', f a = some y ∧ l.mapM f = some ys' ∧ ys = y :: ys' := by
  rw [List.mapM_cons]
  cases f a with
  | none => simp
  | some y =>
    cases l.mapM f with
    | none => simp
    | some ys' => simp [eq_comm]

theorem mapM_related {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
    (h : xs.mapM f = some ys) : Related (fun x y => f x = some y) xs ys := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact .nil
  | cons a l ih =>
    obtain ⟨y, ys', ha, hl, rfl⟩ := (mapM_cons_some f a l ys).mp h
    exact .cons ha (ih ys' hl)

theorem Related.imp {α β : Type} {R S : α → β → Prop} {xs : List α} {ys : List β}
    (h : Related R xs ys) (imp : ∀ a b, R a b → S a b) : Related S xs ys := by
  induction h with
  | nil => exact .nil
  | cons r _ ih => exact .cons (imp _ _ r) ih

/-- Two relations to a common list compose. -/
theorem Related.comp {α β γ : Type} {R : α → β → Prop} {S : β → γ → Prop} {xs : List α}
    {ys : List β} {zs : List γ} (h : Related R xs ys) (k : Related S ys zs) :
    Related (fun a c => ∃ b, R a b ∧ S b c) xs zs := by
  induction h generalizing zs with
  | nil => cases k; exact .nil
  | cons r _ ih =>
    cases k with
    | cons s rest => exact .cons ⟨_, r, s⟩ (ih rest)

theorem Related.flip {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : Related R xs ys) : Related (fun b a => R a b) ys xs := by
  induction h with
  | nil => exact .nil
  | cons r _ ih => exact .cons r ih

/-! Arms of a reply. -/

theorem collect_rows (bs : List (Array UInt64)) (full : ∀ b ∈ bs, b.size ≠ 0)
    (s : List (Array UInt64) × List (List (Array UInt64))) :
    bs.foldr collect s = (bs ++ s.1, s.2) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.foldr_cons, ih fun x hx => full x (List.mem_cons_of_mem _ hx)]
    simp [collect, full b List.mem_cons_self]

theorem readBinding_size (row : Array UInt64) (b : Variable × Term d.sig)
    (h : Packet.readBinding d row = some b) : row.size ≠ 0 := by
  intro empty
  have nil : row.toList = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using empty
  simp [Packet.readBinding, nil] at h

theorem mapM_all {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
    (h : xs.mapM f = some ys) : ∀ x ∈ xs, ∃ y, f x = some y := by
  induction xs generalizing ys with
  | nil => intro x hx; cases hx
  | cons a l ih =>
    obtain ⟨y, ys', ha, hl, rfl⟩ := (mapM_cons_some f a l ys).mp h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨y, ha⟩
    · exact ih ys' hl x hx

/-- The arms of a reply that decodes, each with the bindings it reads as. -/
theorem collect_payload (vs : List Variable) (rows : List (Array UInt64))
    (raw : List (Substitution d.sig)) (h : Packet.Payload d vs rows raw) :
    ∃ groups, rows.foldr collect ([], []) = ([], groups) ∧
      Related (fun g σ => g.mapM (Packet.readBinding d) = some (vs.map fun v => (v, σ.image v)))
        groups raw := by
  induction h with
  | nil => exact ⟨[], rfl, .nil⟩
  | @cons bindings rest σ answers read _ ih =>
    obtain ⟨groups, fold, rel⟩ := ih
    refine ⟨bindings :: groups, ?_, .cons read rel⟩
    have full : ∀ b ∈ bindings, b.size ≠ 0 := fun b hb => by
      obtain ⟨y, hy⟩ := mapM_all _ _ _ read b hb
      exact readBinding_size b y hy
    rw [List.cons_append, List.foldr_cons, List.foldr_append, fold, collect_rows bindings full]
    simp [collect]

/-! Rows and their tokens. -/

theorem parse_read (row : Array UInt64) (v : Variable) (t : Term d.sig) (r : Row)
    (h : Packet.readBinding d row = some (v, t)) (hp : parseRow row = some r) :
    r.variable = v ∧ r.sort ≤ 4 ∧ Packet.execute d r.code [] = some [t] := by
  unfold Packet.readBinding at h
  unfold parseRow at hp
  match hl : row.toList with
  | [] | [_] => simp [hl] at hp
  | key :: sort :: words =>
    simp only [hl] at h hp
    cases htok : Packet.tokenize words with
    | none => simp [htok] at hp
    | some code =>
      simp only [htok, Option.map_some, Option.some.injEq] at hp
      subst hp
      by_cases fits : sort ≤ 4
      · simp only [fits, guard, ↓reduceIte, htok, pure, bind, Option.bind] at h
        cases hex : Packet.execute d code [] with
        | none => simp [hex] at h
        | some st =>
          simp only [hex] at h
          match st, h with
          | [u], h =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            exact ⟨h.1, fits, by rw [h.2]⟩
      · simp [fits, guard, failure] at h

/-- The rows of an arm are the bindings of an answer, in the order of the query. -/
structure ArmOf (d : Dictionary) (vs : List Variable) (σ : Substitution d.sig) (arm : List Row) :
    Prop where
  keys : arm.map Row.variable = vs
  sorts : ∀ r ∈ arm, r.sort ≤ 4
  images : ∀ r ∈ arm, Packet.execute d r.code [] = some [σ.image r.variable]

theorem arm_of (vs : List Variable) (σ : Substitution d.sig) (g : List (Array UInt64)) (arm : List Row)
    (read : g.mapM (Packet.readBinding d) = some (vs.map fun v => (v, σ.image v)))
    (parsed : g.mapM parseRow = some arm) : ArmOf d vs σ arm := by
  induction g generalizing vs arm with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at read parsed
    subst parsed
    cases vs with
    | nil => exact ⟨rfl, fun _ hr => (nomatch hr), fun _ hr => (nomatch hr)⟩
    | cons v vs => simp at read
  | cons row g ih =>
    obtain ⟨b, bs, hb, hbs, eq⟩ := (mapM_cons_some _ row g _).mp read
    obtain ⟨r, rs, hr, hrs, rfl⟩ := (mapM_cons_some _ row g _).mp parsed
    cases vs with
    | nil => simp at eq
    | cons v vs =>
      simp only [List.map_cons, List.cons.injEq] at eq
      obtain ⟨rfl, rfl⟩ := eq
      obtain ⟨key, sort, image⟩ := parse_read row v (σ.image v) r hb hr
      have rest := ih vs rs hbs hrs
      refine ⟨by simp [key, rest.keys], ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact sort
        · exact rest.sorts x hx
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · rw [key]; exact image
        · exact rest.images x hx

theorem tokenVariable_kind {t : Token} {w : Variable} (h : tokenVariable t = some w) :
    (t.kind == 0) = true ∧ w = ⟨t.id.toNat, sortOf t.arg⟩ := by
  unfold tokenVariable at h
  split at h
  · next zero => exact ⟨zero, (Option.some.inj h).symm⟩
  · cases h

theorem tokenVariable_none {t : Token} (h : tokenVariable t = none) : (t.kind == 0) = false := by
  unfold tokenVariable at h
  split at h
  · cases h
  · next rigid => simpa using rigid

private theorem low_of_zero {k : UInt64} (zero : (k == 0) = true) : k ≤ 1 := by
  rw [eq_of_beq zero]; decide

/-- A step keeps the variables on the stack and adds the one of its token. -/
theorem step_occurs (stack stack' : List (Term d.sig)) (t : Token)
    (h : Packet.step d stack t = some stack') (w : Variable) :
    (∃ u ∈ stack', u.Occurs w) ↔ (∃ u ∈ stack, u.Occurs w) ∨ tokenVariable t = some w := by
  unfold Packet.step at h
  by_cases low : t.kind ≤ 1
  · simp only [low, ↓reduceIte, bind, Option.bind, pure] at h
    cases hl : leaf d t.kind t.id t.arg with
    | none => simp [hl] at h
    | some r =>
      simp only [hl, Option.some.injEq] at h
      subst h
      cases zero : t.kind == 0 with
      | true =>
        have var := leaf_zero hl zero
        subst var
        constructor
        · rintro ⟨u, hu, occ⟩
          rcases List.mem_cons.mp hu with rfl | hu
          · refine .inr ?_
            simp only [tokenVariable, zero, ↓reduceIte]
            exact congrArg some (Eq.symm occ)
          · exact .inl ⟨u, hu, occ⟩
        · rintro (⟨u, hu, occ⟩ | hv)
          · exact ⟨u, List.mem_cons_of_mem _ hu, occ⟩
          · refine ⟨_, List.mem_cons_self, ?_⟩
            simp only [tokenVariable, zero, ↓reduceIte, Option.some.injEq] at hv
            exact hv.symm
      | false =>
        have rigid := leaf_rigid hl zero w
        constructor
        · rintro ⟨u, hu, occ⟩
          rcases List.mem_cons.mp hu with rfl | hu
          · exact (rigid occ).elim
          · exact .inl ⟨u, hu, occ⟩
        · rintro (⟨u, hu, occ⟩ | hv)
          · exact ⟨u, List.mem_cons_of_mem _ hu, occ⟩
          · simp [tokenVariable, zero] at hv
  · have rigid : (t.kind == 0) = false := by
      cases zero : t.kind == 0 with
      | true => exact (low (low_of_zero zero)).elim
      | false => rfl
    simp only [low, ↓reduceIte, bind, Option.bind, pure, guard] at h
    by_cases fits : t.arg.toNat ≤ stack.length
    · simp only [fits, ↓reduceIte] at h
      cases ha : app d t.kind t.id (stack.take t.arg.toNat).reverse with
      | none => simp [ha] at h
      | some r =>
        simp only [ha, Option.some.injEq] at h
        subst h
        have occ := app_occurs ha w
        constructor
        · rintro ⟨u, hu, hw⟩
          rcases List.mem_cons.mp hu with rfl | hu
          · obtain ⟨c, hc, hw⟩ := occ.mp hw
            exact .inl ⟨c, List.mem_of_mem_take (List.mem_reverse.mp hc), hw⟩
          · exact .inl ⟨u, List.mem_of_mem_drop hu, hw⟩
        · rintro (⟨c, hc, hw⟩ | hv)
          · rw [← List.take_append_drop t.arg.toNat stack] at hc
            rcases List.mem_append.mp hc with hc | hc
            · exact ⟨r, List.mem_cons_self, occ.mpr ⟨c, List.mem_reverse.mpr hc, hw⟩⟩
            · exact ⟨c, List.mem_cons_of_mem _ hc, hw⟩
          · simp [tokenVariable, rigid] at hv
    · simp [fits, failure] at h

theorem execute_occurs (code : List Token) (stack stack' : List (Term d.sig))
    (h : Packet.execute d code stack = some stack') (w : Variable) :
    (∃ u ∈ stack', u.Occurs w) ↔ (∃ u ∈ stack, u.Occurs w) ∨ w ∈ code.filterMap tokenVariable := by
  induction code generalizing stack with
  | nil =>
    simp only [Packet.execute, List.foldlM_nil, pure, Option.some.injEq] at h
    subst h
    simp
  | cons t ts ih =>
    simp only [Packet.execute, List.foldlM_cons, bind, Option.bind] at h
    cases hs : Packet.step d stack t with
    | none => simp [hs] at h
    | some mid =>
      simp only [hs] at h
      rw [ih mid h, step_occurs stack mid t hs w, List.filterMap_cons]
      cases hv : tokenVariable t with
      | none => simp
      | some u => simp [or_assoc, eq_comm]

/-- The variables of the image of a row are those of its tokens. -/
theorem row_occurs (r : Row) (t : Term d.sig) (h : Packet.execute d r.code [] = some [t])
    (w : Variable) : t.Occurs w ↔ w ∈ r.variables := by
  have := execute_occurs r.code [] [t] h w
  simpa [Row.variables] using this

/-- A row of one variable token binds its query variable to that variable. -/
theorem row_single (t : Token) (w : Variable) (u : Term d.sig) (hv : tokenVariable t = some w)
    (h : Packet.execute d [t] [] = some [u]) : u = .var w := by
  obtain ⟨zero, rfl⟩ := tokenVariable_kind hv
  simp only [Packet.execute, List.foldlM_cons, List.foldlM_nil, bind, Option.bind, pure] at h
  cases hs : Packet.step d [] t with
  | none => simp [hs] at h
  | some mid =>
    simp only [hs, Option.some.injEq] at h
    subst h
    unfold Packet.step at hs
    simp only [low_of_zero zero, ↓reduceIte, bind, Option.bind, pure] at hs
    cases hl : leaf d t.kind t.id t.arg with
    | none => simp [hl] at hs
    | some r =>
      simp only [hl, Option.some.injEq, List.cons.injEq, and_true] at hs
      rw [← hs]
      exact leaf_zero hl zero

/-! Renaming through a table. -/

/-- The variable a target stands for, with the query variables by row. -/
def Target.variable (base : Nat) (vs : List Variable) (w : Variable) : Target → Variable
  | .name l => named base l w.sort
  | .self row =>
    match vs[row]? with
    | some v => if v.sort = w.sort then v else w
    | none => w

/-- What a table makes of a range variable. -/
def assign (base : Nat) (vs : List Variable) (es : List Entry) (w : Variable) : Variable :=
  match find es w with
  | some t => t.variable base vs w
  | none => w

theorem assign_sort (base : Nat) (vs : List Variable) (es : List Entry) (w : Variable) :
    (assign base vs es w).sort = w.sort := by
  unfold assign
  cases find es w with
  | none => rfl
  | some t =>
    cases t with
    | name l => exact named_sort base l w.sort
    | self row =>
      show (Target.variable base vs w (.self row)).sort = w.sort
      simp only [Target.variable]
      split
      · split
        · assumption
        · rfl
      · rfl

abbrev rename (d : Dictionary) (base : Nat) (vs : List Variable) (es : List Entry) :
    Variable → Term d.sig := fun w => .var (assign base vs es w)

theorem sortOfKind_low {k : UInt64} (low : k ≤ 1) : sortOfKind k = none := by
  unfold sortOfKind
  repeat' split
  all_goals first
    | rfl
    | (next h => rw [eq_of_beq h] at low; exact absurd low (by decide))

theorem sortOfKind_app {k : UInt64} (h : (k == 2) = true ∨ (k == 3) = true ∨ (k == 4) = true) :
    sortOfKind k = none := by
  rcases h with h | h | h <;> rw [eq_of_beq h] <;> decide

/-- A step that reads no variable commutes with a substitution of the stack. -/
theorem packet_step_map (ρ : Variable → Term d.sig) (stack stack' : List (Term d.sig)) (t : Token)
    (h : Packet.step d stack t = some stack') (rigid : (t.kind == 0) = false) :
    Packet.step d (stack.map (Term.subst ρ)) t = some (stack'.map (Term.subst ρ)) ∧
      sortOfKind t.kind = none := by
  unfold Packet.step at h ⊢
  by_cases low : t.kind ≤ 1
  · simp only [low, ↓reduceIte, bind, Option.bind, pure] at h ⊢
    cases hl : leaf d t.kind t.id t.arg with
    | none => simp [hl] at h
    | some r =>
      simp only [hl, Option.some.injEq] at h
      subst h
      simp [leaf_subst ρ _ _ _ r hl rigid, sortOfKind_low low]
  · simp only [low, ↓reduceIte, bind, Option.bind, pure, guard] at h ⊢
    by_cases fits : t.arg.toNat ≤ stack.length
    · simp only [fits, ↓reduceIte] at h
      cases ha : app d t.kind t.id (stack.take t.arg.toNat).reverse with
      | none => simp [ha] at h
      | some r =>
        simp only [ha, Option.some.injEq] at h
        subst h
        have moved := app_subst ρ t.kind t.id (stack.take t.arg.toNat).reverse
        rw [ha, List.map_reverse, List.map_take] at moved
        simp [fits, moved, List.map_drop, sortOfKind_app (app_kind ha)]
    · simp [fits, failure] at h

theorem step_rename (base : Nat) (vs : List Variable) (es : List Entry)
    (stack stack' : List (Term d.sig)) (t t' : Token) (hr : renameToken es t = some t')
    (hs : Packet.step d stack t = some stack') :
    step d base (stack.map (Term.subst (rename d base vs es))) t' =
      some (stack'.map (Term.subst (rename d base vs es))) := by
  unfold renameToken at hr
  cases hv : tokenVariable t with
  | some w =>
    simp only [hv] at hr
    cases hf : find es w with
    | none => simp [hf] at hr
    | some target =>
      cases target with
      | self row => simp [hf] at hr
      | name l =>
        simp only [hf, Option.some.injEq] at hr
        subst hr
        obtain ⟨zero, weq⟩ := tokenVariable_kind hv
        unfold Packet.step at hs
        simp only [low_of_zero zero, ↓reduceIte, bind, Option.bind, pure] at hs
        cases hl : leaf d t.kind t.id t.arg with
        | none => simp [hl] at hs
        | some r =>
          simp only [hl, Option.some.injEq] at hs
          subst hs
          have var := leaf_zero hl zero
          rw [← weq] at var
          subst var
          simp [step, sortOfKind_kind, Term.subst, assign, Target.variable, hf]
  | none =>
    simp only [hv, Option.some.injEq] at hr
    subst hr
    have rigid := tokenVariable_none hv
    obtain ⟨moved, kind⟩ := packet_step_map (rename d base vs es) stack stack' t hs rigid
    simp [step, kind, rigid, moved]

theorem execute_rename (base : Nat) (vs : List Variable) (es : List Entry) (code code' : List Token)
    (stack stack' : List (Term d.sig)) (hr : code.mapM (renameToken es) = some code')
    (hs : Packet.execute d code stack = some stack') :
    execute d base code' (stack.map (Term.subst (rename d base vs es))) =
      some (stack'.map (Term.subst (rename d base vs es))) := by
  induction code generalizing code' stack with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at hr
    subst hr
    simp only [Packet.execute, List.foldlM_nil, pure, Option.some.injEq] at hs
    subst hs
    rfl
  | cons t ts ih =>
    obtain ⟨t', ts', ht, hts, rfl⟩ := (mapM_cons_some _ t ts code').mp hr
    simp only [Packet.execute, List.foldlM_cons, bind, Option.bind] at hs
    cases hm : Packet.step d stack t with
    | none => simp [hm] at hs
    | some mid =>
      simp only [hm] at hs
      simp only [execute, List.foldlM_cons, bind, Option.bind, step_rename base vs es stack mid t t' ht hm]
      exact ih ts' mid hts hs

/-- The variables of a row that is renamed all have a label. -/
theorem renamed_named (es : List Entry) (code code' : List Token)
    (hr : code.mapM (renameToken es) = some code') :
    ∀ w ∈ code.filterMap tokenVariable, ∃ l, find es w = some (.name l) := by
  intro w hw
  obtain ⟨t, ht, hv⟩ := List.mem_filterMap.mp hw
  obtain ⟨t', renamed⟩ := mapM_all _ _ _ hr t ht
  unfold renameToken at renamed
  simp only [hv] at renamed
  cases hf : find es w with
  | none => simp [hf] at renamed
  | some target =>
    cases target with
    | self row => simp [hf] at renamed
    | name l => exact ⟨l, rfl⟩

theorem stands_spec (es : List Entry) (row : Nat) (r : Row) (h : stands es row r = true) :
    ∃ t w, r.code = [t] ∧ tokenVariable t = some w ∧ find es w = some (.self row) := by
  unfold stands at h
  split at h
  · next t code =>
    cases hv : tokenVariable t with
    | none => simp [hv] at h
    | some w =>
      simp only [hv, beq_iff_eq] at h
      exact ⟨t, w, code, hv, h⟩
  · cases h

theorem emitRow_none (es : List Entry) (x : Row × Nat) (h : emitRow es x = some none) :
    stands es x.2 x.1 = true := by
  unfold emitRow at h
  split at h
  · assumption
  · cases hm : x.1.code.mapM (renameToken es) <;> simp [hm] at h

/-- A row that is written reads as the binding of its variable to the renamed image. -/
theorem emitRow_some (base : Nat) (vs : List Variable) (es : List Entry) (x : Row × Nat)
    (row : Array UInt64) (t : Term d.sig) (h : emitRow es x = some (some row))
    (sort : x.1.sort ≤ 4) (image : Packet.execute d x.1.code [] = some [t]) :
    stands es x.2 x.1 = false ∧
      (∃ code', x.1.code.mapM (renameToken es) = some code') ∧
      readBinding d base row = some (x.1.variable, t.subst (rename d base vs es)) := by
  unfold emitRow at h
  split at h
  · cases h
  · next no =>
    cases hm : x.1.code.mapM (renameToken es) with
    | none => simp [hm] at h
    | some code' =>
      simp only [hm, Option.map_some, Option.some.injEq] at h
      subst h
      refine ⟨by simpa using no, ⟨code', rfl⟩, ?_⟩
      have run := execute_rename base vs es x.1.code code' [] [t] hm image
      simp only [List.map_nil, List.map_cons] at run
      simp [readBinding, sort, guard, Packet.tokenize_words, run, Row.variable]

/-! What the tests of the procedure establish. -/

theorem distinctFrom_spec {α : Type} (position : α → Nat) (i : Nat) (xs : List α)
    (h : distinctFrom position i xs = true) : ∀ j (hj : j < xs.length), position xs[j] = i + j := by
  induction xs generalizing i with
  | nil => intro j hj; exact absurd hj (Nat.not_lt_zero j)
  | cons x xs ih =>
    simp only [distinctFrom, Bool.and_eq_true, beq_iff_eq] at h
    intro j hj
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have := ih (i + 1) h.2 j (by simpa using hj)
      simp only [List.getElem_cons_succ]
      omega

theorem named_inj {base : Nat} {l l' : Label} {s s' : SortId} (h : named base l s = named base l' s') :
    l = l' ∧ s = s' := by
  simp only [named, Variable.mk.injEq] at h
  have a := l.2.toNat_lt
  have b := l'.2.toNat_lt
  have size : UInt64.size = 2 ^ 64 := rfl
  rw [size] at h
  have first : l.1.toNat = l'.1.toNat := by omega
  have second : l.2.toNat = l'.2.toNat := by omega
  exact ⟨Prod.ext (UInt64.toNat_inj.mp first) (UInt64.toNat_inj.mp second), h.2⟩

theorem base_le_named (base : Nat) (l : Label) (s : SortId) : base ≤ (named base l s).id := by
  unfold named
  exact Nat.le_add_right _ _

private theorem foldl_bound (qs : List (Variable × Label)) (b : Nat) :
    b ≤ qs.foldl (fun b q => max b (q.2.2.toNat + 1)) b ∧
      ∀ e ∈ qs, e.2.2.toNat < qs.foldl (fun b q => max b (q.2.2.toNat + 1)) b := by
  induction qs generalizing b with
  | nil => exact ⟨Nat.le_refl _, fun e he => (nomatch he)⟩
  | cons x xs ih =>
    obtain ⟨le, rest⟩ := ih (max b (x.2.2.toNat + 1))
    simp only [List.foldl_cons]
    refine ⟨by omega, fun e he => ?_⟩
    rcases List.mem_cons.mp he with rfl | he
    · omega
    · exact rest e he

theorem indexBound_spec (qs : List (Variable × Label)) : ∀ e ∈ qs, e.2.2.toNat < indexBound qs :=
  (foldl_bound qs 0).2

theorem queryLabels_spec (names : Array UInt64) (vs : List Variable) (qs : List (Variable × Label))
    (h : queryLabels names vs = some qs) :
    qs.map Prod.fst = vs ∧ ∀ e ∈ qs, label names e.1 = some e.2 := by
  unfold queryLabels at h
  induction vs generalizing qs with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun e he => (nomatch he)⟩
  | cons v vs ih =>
    obtain ⟨y, ys, hy, hys, rfl⟩ := (mapM_cons_some _ v vs qs).mp h
    obtain ⟨keys, labelled⟩ := ih ys hys
    cases hl : label names v with
    | none => simp [hl] at hy
    | some l =>
      simp only [hl, Option.map_some, Option.some.injEq] at hy
      subst hy
      refine ⟨by simp [keys], fun e he => ?_⟩
      rcases List.mem_cons.mp he with rfl | he
      · exact hl
      · exact labelled e he

/-- What `query` returns, for the variables of its words. -/
structure QueryOf (names : Array UInt64) (vs : List Variable) (q : Query)
    (qs : List (Variable × Label)) : Prop where
  vars : qs.map Prod.fst = vs
  labelled : ∀ e ∈ qs, label names e.1 = some e.2
  array : q.qs = qs.toArray
  position : q.position = fun k => (queryKeys qs).idxOf k
  bound : q.bound = indexBound qs
  distinct : ∀ j (hj : j < (queryKeys qs).length), (queryKeys qs).idxOf (queryKeys qs)[j] = j

theorem query_of (names heads : Array UInt64) (q : Query) (vs : List Variable)
    (h : query names heads = some q) (hv : headVariables heads.toList = some vs) :
    ∃ qs, QueryOf names vs q qs := by
  unfold query at h
  simp only [hv, Option.bind_some] at h
  cases hq : queryLabels names vs with
  | none => simp [hq] at h
  | some qs =>
    simp only [hq, Option.bind_some] at h
    split at h
    · next ok =>
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨vars, labelled⟩ := queryLabels_spec names vs qs hq
      rw [Index.position_of] at ok
      refine ⟨qs, vars, labelled, rfl, Index.position_of _ _, rfl, fun j hj => ?_⟩
      simpa using distinctFrom_spec _ 0 _ ok j hj
    · cases h

/-- What `tableOK` establishes of the entries of an arm. -/
structure TableOf (qs : List (Variable × Label)) (nat above unused : Bool) (es : List Entry) :
    Prop where
  distinct : ∀ a b (ha : a < es.length) (hb : b < es.length), entryKey es[a] = entryKey es[b] → a = b
  sorts : ∀ e ∈ es, nat = true ∨ e.source.sort ≠ .nat
  name : ∀ e ∈ es, ∀ l, e.target = .name l →
    (l, e.source.sort) ∉ queryKeys qs ∧ (above = true → l.1 = 0 ∧ indexBound qs ≤ l.2.toNat) ∧
      (unused = true → l.1 = 0 ∧ ∀ v ∈ qs, v.2.2 ≠ l.2)
  self : ∀ e ∈ es, ∀ row, e.target = .self row →
    above = false ∧ unused = false ∧ ∃ v, qs[row]? = some v ∧ v.1.sort = e.source.sort

theorem tableOf {names : Array UInt64} {vs : List Variable} {q : Query} {qs : List (Variable × Label)}
    (hq : QueryOf names vs q qs) (nat above unused : Bool) (es : List Entry)
    (ok : tableOK q nat above unused es = true) : TableOf qs nat above unused es := by
  unfold tableOK at ok
  rw [Index.position_of, Bool.and_eq_true, List.all_eq_true] at ok
  obtain ⟨keys, each⟩ := ok
  have at_ := distinctFrom_spec _ 0 _ keys
  refine ⟨fun a b ha hb same => ?_, fun e he => ?_, fun e he l target => ?_, fun e he row target => ?_⟩
  · have pa := at_ a (by simpa using ha)
    have pb := at_ b (by simpa using hb)
    simp only [List.getElem_map, Nat.zero_add] at pa pb
    rw [same, pb] at pa
    exact pa.symm
  · have := each e he
    simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne] at this
    exact this.1
  · have := each e he
    simp only [target, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq, beq_iff_eq] at this
    obtain ⟨_, ⟨outside, bound⟩, low⟩ := this
    refine ⟨fun mem => outside ?_, fun set => ?_, fun set => ?_⟩
    · rw [hq.position, hq.array]
      simpa [queryKeys] using List.idxOf_lt_length_iff.mpr mem
    · rcases bound with off | on
      · rw [set] at off; cases off
      · exact ⟨on.1, hq.bound ▸ on.2⟩
    · rcases low with off | on
      · rw [set] at off; cases off
      · refine ⟨on.1, fun v hv => ?_⟩
        have all := on.2
        rw [hq.array] at all
        simp only [List.all_toArray, List.all_eq_true, bne_iff_ne, ne_eq] at all
        exact all v hv
  · have := each e he
    simp only [target, Bool.and_eq_true, Bool.not_eq_true'] at this
    obtain ⟨_, ⟨off, low⟩, found⟩ := this
    refine ⟨off, low, ?_⟩
    rw [hq.array, List.getElem?_toArray] at found
    cases hr : qs[row]? with
    | none => simp [hr] at found
    | some v => exact ⟨v, rfl, by simpa [hr] using found⟩

theorem find_mem (es : List Entry) (w : Variable) (t : Target) (h : find es w = some t) :
    ∃ e ∈ es, e.source = w ∧ e.target = t := by
  unfold find at h
  cases hf : es.find? (fun e => e.source == w) with
  | none => simp [hf] at h
  | some e =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    exact ⟨e, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, h⟩

/-! One arm read through its table. -/

/-- The answer of an arm with its range renamed by the table. -/
def renamed (σ : Substitution d.sig) (base : Nat) (vs : List Variable) (es : List Entry) :
    Substitution d.sig where
  image v := if v ∈ vs then (σ.image v).subst (rename d base vs es) else .var v
  support := vs
  outside v hv := ite_eq_right hv
  sorted v := by
    split
    · exact (σ.sorted v).subst _ fun w => assign_sort base vs es w ▸ HasSort.var _
    · exact .var v

/-- The bindings that the rows of an arm leave. -/
def images (σ : Substitution d.sig) (base : Nat) (vs : List Variable) (es : List Entry)
    (xs : List (Row × Nat)) : List (Variable × Term d.sig) :=
  xs.filterMap fun x =>
    if stands es x.2 x.1 then none
    else some (x.1.variable, (σ.image x.1.variable).subst (rename d base vs es))

theorem rows_read (σ : Substitution d.sig) (base : Nat) (vs : List Variable) (es : List Entry)
    (xs : List (Row × Nat)) (rs : List (Option (Array UInt64))) (h : xs.mapM (emitRow es) = some rs)
    (ok : ∀ x ∈ xs, x.1.sort ≤ 4 ∧ Packet.execute d x.1.code [] = some [σ.image x.1.variable]) :
    (rs.filterMap id).mapM (readBinding d base) = some (images σ base vs es xs) := by
  induction xs generalizing rs with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    rfl
  | cons x xs ih =>
    obtain ⟨y, ys, hy, hys, rfl⟩ := (mapM_cons_some _ x xs rs).mp h
    have rest := ih ys hys fun z hz => ok z (List.mem_cons_of_mem _ hz)
    cases y with
    | none =>
      have st := emitRow_none es x hy
      simpa [images, st] using rest
    | some row =>
      obtain ⟨sort, image⟩ := ok x List.mem_cons_self
      obtain ⟨st, _, read⟩ := emitRow_some base vs es x row _ hy sort image
      simp only [List.filterMap_cons, id, images, st, Bool.false_eq_true, ↓reduceIte]
      rw [List.mapM_cons, read]
      simp only [images] at rest
      simp [rest]

theorem images_sublist (σ : Substitution d.sig) (base : Nat) (vs : List Variable) (es : List Entry)
    (xs : List (Row × Nat)) :
    ((images σ base vs es xs).map Prod.fst).Sublist (xs.map fun x => x.1.variable) := by
  induction xs with
  | nil => exact .slnil
  | cons x xs ih =>
    simp only [images, List.filterMap_cons, List.map_cons]
    split
    · next none => exact .cons _ ih
    · next b some =>
      split at some
      · cases some
      · simp only [Option.some.injEq] at some
        subst some
        exact .cons_cons _ ih

theorem images_lookup (σ : Substitution d.sig) (base : Nat) (vs : List Variable) (es : List Entry)
    (τ : Variable → Term d.sig) (xs : List (Row × Nat))
    (stand : ∀ x ∈ xs, stands es x.2 x.1 = true → τ x.1.variable = .var x.1.variable)
    (other : ∀ x ∈ xs, stands es x.2 x.1 = false →
      τ x.1.variable = (σ.image x.1.variable).subst (rename d base vs es)) (v : Variable) :
    ((images σ base vs es xs).lookup v).getD (.var v) =
      if v ∈ xs.map (fun x => x.1.variable) then τ v else .var v := by
  induction xs with
  | nil => simp [images]
  | cons x xs ih =>
    have rest := ih (fun z hz => stand z (List.mem_cons_of_mem _ hz))
      (fun z hz => other z (List.mem_cons_of_mem _ hz))
    simp only [images] at rest
    cases st : stands es x.2 x.1 with
    | true =>
      have here := stand x List.mem_cons_self st
      simp only [images, List.filterMap_cons, st, ↓reduceIte, List.map_cons, List.mem_cons]
      rw [rest]
      by_cases same : v = x.1.variable
      · subst same
        rw [ite_eq_left (Or.inl rfl)]
        split
        · rfl
        · exact here.symm
      · simp only [same, false_or]
    | false =>
      have here := other x List.mem_cons_self st
      simp only [images, List.filterMap_cons, st, Bool.false_eq_true, ↓reduceIte, List.map_cons,
        List.mem_cons, List.lookup_cons]
      by_cases same : v = x.1.variable
      · subst same
        simp [here]
      · have ne : (v == x.1.variable) = false := by simpa using same
        simp only [ne, same, false_or]
        exact rest

/-- Every range variable of an arm that is read has a label, or it is the
whole image of the query variable of its row and stands for it. -/
theorem arm_targets {vs : List Variable} {σ : Substitution d.sig} {arm : List Row} {es : List Entry}
    {rs : List (Option (Array UInt64))} (armOf : ArmOf d vs σ arm)
    (emitted : arm.zipIdx.mapM (emitRow es) = some rs) :
    ∀ r ∈ arm, ∀ w ∈ r.variables,
      (∃ l, find es w = some (.name l)) ∨
      (∃ i, find es w = some (.self i) ∧ vs[i]? = some r.variable ∧
        σ.image r.variable = .var w ∧ r.variables = [w]) := by
  intro r hr w hw
  obtain ⟨i, at_⟩ := List.mem_iff_getElem?.mp hr
  have member : (r, i) ∈ arm.zipIdx := List.mem_zipIdx_iff_getElem?.mpr at_
  obtain ⟨y, hy⟩ := mapM_all _ _ _ emitted (r, i) member
  cases y with
  | none =>
    obtain ⟨t, w0, code, hv, target⟩ := stands_spec es i r (emitRow_none es (r, i) hy)
    have only : r.variables = [w0] := by simp [Row.variables, code, hv]
    rw [only] at hw
    obtain rfl : w = w0 := by simpa using hw
    refine .inr ⟨i, target, ?_, ?_, only⟩
    · rw [← armOf.keys, List.getElem?_map, at_]
      rfl
    · exact row_single t w _ hv (code ▸ armOf.images r hr)
  | some row =>
    obtain ⟨_, ⟨code', renamedCode⟩, _⟩ :=
      emitRow_some 0 vs es (r, i) row _ hy (armOf.sorts r hr) (armOf.images r hr)
    exact .inl (renamed_named es r.code code' renamedCode w hw)

/-- An arm that is read through a table that passed the test is the answer of
the arm under an injective renaming of its range, with fresh labels. -/
theorem arm_named {p : Problem d.sig} {names : Array UInt64} {q : Query}
    {qs : List (Variable × Label)} {nat above unused : Bool} {σ : Substitution d.sig}
    {arm : List Row} {es : List Entry} {o : List (Array UInt64)}
    (hq : QueryOf names p.variables.eraseDups q qs) (ok : tableOK q nat above unused es = true)
    (armOf : ArmOf d p.variables.eraseDups σ arm) (emitted : emitArm es arm = some o) :
    ∃ τ : Substitution d.sig,
      (∃ a : CallerFreshening.Allocation (CallerFreshening.sources p σ),
        CallerFreshening.Represents p σ τ a) ∧
      Fresh names p τ ∧ (above = true → Above names p τ) ∧ (unused = true → Unused names p τ) ∧
      (nat = false → UnavailableSort.noNatWitness p σ = true) ∧
      ∃ rows found, o = #[] :: rows ∧ rows.mapM (readBinding d (base p)) = some found ∧
        (found.map Prod.fst).Sublist p.variables.eraseDups ∧
        ∀ v ∈ p.variables.eraseDups, τ.image v = (found.lookup v).getD (.var v) := by
  have table := tableOf hq nat above unused es ok
  unfold emitArm at emitted
  cases hm : arm.zipIdx.mapM (emitRow es) with
  | none => simp [hm] at emitted
  | some rs =>
  simp only [hm, Option.map_some, Option.some.injEq] at emitted
  subst emitted
  have inVs : ∀ v, v ∈ p.variables.eraseDups ↔ p.Occurs v := fun v => by
    rw [List.mem_eraseDups, Problem.mem_variables]
  have targets := arm_targets armOf hm
  have rowOf : ∀ v, p.Occurs v → ∃ r ∈ arm, r.variable = v := by
    intro v hv
    have : v ∈ arm.map Row.variable := by rw [armOf.keys]; exact (inVs v).mpr hv
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp this
    exact ⟨r, hr, rfl⟩
  have rowIn : ∀ r ∈ arm, p.Occurs r.variable := fun r hr =>
    (inVs _).mp (armOf.keys ▸ List.mem_map_of_mem hr)
  have source : ∀ w ∈ CallerFreshening.sources p σ, ∃ r ∈ arm, w ∈ r.variables := by
    intro w hw
    obtain ⟨v, hv, occ⟩ := List.mem_flatMap.mp hw
    obtain ⟨r, hr, rfl⟩ := rowOf v ((p.mem_variables v).mp hv)
    exact ⟨r, hr, (row_occurs r _ (armOf.images r hr) w).mp ((Term.mem_variables _ w).mp occ)⟩
  have nameAt : ∀ w l, find es w = some (.name l) →
      assign (base p) p.variables.eraseDups es w = named (base p) l w.sort := by
    intro w l h
    simp [assign, Target.variable, h]
  have selfAt : ∀ (r : Row) w i, find es w = some (.self i) →
      p.variables.eraseDups[i]? = some r.variable →
      assign (base p) p.variables.eraseDups es w = r.variable := by
    intro r w i h at_
    obtain ⟨e, he, src, tgt⟩ := find_mem es w _ h
    obtain ⟨_, _, v, hv, sort⟩ := table.self e he i tgt
    have there : p.variables.eraseDups[i]? = some v.1 := by
      rw [← hq.vars, List.getElem?_map, hv]
      rfl
    rw [at_] at there
    have eq : r.variable = v.1 := Option.some.inj there
    have sorted : r.variable.sort = w.sort := by rw [eq, sort, src]
    simp [assign, Target.variable, h, at_, sorted]
  have inj : ∀ u ∈ CallerFreshening.sources p σ, ∀ v ∈ CallerFreshening.sources p σ,
      assign (base p) p.variables.eraseDups es u = assign (base p) p.variables.eraseDups es v →
        u = v := by
    intro u hu v hv same
    obtain ⟨ru, hru, uin⟩ := source u hu
    obtain ⟨rv, hrv, vin⟩ := source v hv
    have below : ∀ r ∈ arm, r.variable.id < base p := fun r hr =>
      VariablePermutation.lt_freshBound p.variables r.variable ((p.mem_variables _).mpr (rowIn r hr))
    rcases targets ru hru u uin with ⟨lu, fu⟩ | ⟨iu, fu, atu, imu, _⟩ <;>
      rcases targets rv hrv v vin with ⟨lv, fv⟩ | ⟨iv, fv, atv, imv, _⟩
    · rw [nameAt u lu fu, nameAt v lv fv] at same
      obtain ⟨leq, seq⟩ := named_inj same
      obtain ⟨eu, heu, su, tu⟩ := find_mem es u _ fu
      obtain ⟨ev, hev, sv, tv⟩ := find_mem es v _ fv
      obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem heu
      obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hev
      have key : entryKey es[a] = entryKey es[b] := by
        simp [entryKey, tu, tv, su, sv, leq, seq]
      have := table.distinct a b ha hb key
      subst this
      exact su.symm.trans sv
    · rw [nameAt u lu fu, selfAt rv v iv fv atv] at same
      have big := base_le_named (base p) lu u.sort
      rw [same] at big
      exact absurd (below rv hrv) (Nat.not_lt.mpr big)
    · rw [selfAt ru u iu fu atu, nameAt v lv fv] at same
      have big := base_le_named (base p) lv v.sort
      rw [← same] at big
      exact absurd (below ru hru) (Nat.not_lt.mpr big)
    · rw [selfAt ru u iu fu atu, selfAt rv v iv fv atv] at same
      rw [same, imv] at imu
      exact (Term.var.inj imu).symm
  let a : CallerFreshening.Allocation (CallerFreshening.sources p σ) :=
    ⟨assign (base p) p.variables.eraseDups es, fun w _ => assign_sort _ _ _ w, inj⟩
  refine ⟨renamed σ (base p) p.variables.eraseDups es, ⟨a, fun v => ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show (if v ∈ p.variables.eraseDups then _ else _) = _
    simp only [List.mem_eraseDups]
    rfl
  · intro v hv
    obtain ⟨r, hr, rfl⟩ := rowOf v hv
    have here : r.variable ∈ p.variables.eraseDups := (inVs _).mpr hv
    by_cases hself : ∃ w ∈ r.variables, ∃ i, find es w = some (.self i)
    · obtain ⟨w, hw, i, fw⟩ := hself
      rcases targets r hr w hw with ⟨l, fl⟩ | ⟨j, fj, at_, im, _⟩
      · rw [fw] at fl; cases fl
      · left
        show (if r.variable ∈ p.variables.eraseDups then _ else _) = _
        rw [ite_eq_left here, im]
        show Term.var (assign _ _ _ w) = _
        rw [selfAt r w j fj at_]
    · right
      intro w' occ
      have occ' : ((σ.image r.variable).subst (rename d (base p) p.variables.eraseDups es)).Occurs w' := by
        have : (renamed σ (base p) p.variables.eraseDups es).image r.variable =
            (σ.image r.variable).subst (rename d (base p) p.variables.eraseDups es) := ite_eq_left here
        rw [← this]
        exact occ
      obtain ⟨w, hw, rfl⟩ := (Term.occurs_rename _ _ _).mp occ'
      have win := (row_occurs r _ (armOf.images r hr) w).mp hw
      rcases targets r hr w win with ⟨l, fl⟩ | ⟨j, fj, _⟩
      · refine ⟨l, ?_, fun u hu sort lab => ?_⟩
        · rw [assign_sort]
          exact nameAt w l fl
        · rw [assign_sort] at sort
          obtain ⟨e, he, src, tgt⟩ := find_mem es w _ fl
          apply (table.name e he l tgt).1
          have uin : u ∈ qs.map Prod.fst := by rw [hq.vars]; exact (inVs u).mpr hu
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp uin
          have known := hq.labelled x hx
          rw [lab] at known
          have leq : l = x.2 := Option.some.inj known
          exact List.mem_map.mpr ⟨x, hx, by rw [leq, src, sort]⟩
      · exact (hself ⟨w, win, j, fj⟩).elim
  · intro on v hv w' occ
    obtain ⟨r, hr, rfl⟩ := rowOf v hv
    have here : r.variable ∈ p.variables.eraseDups := (inVs _).mpr hv
    have occ' : ((σ.image r.variable).subst (rename d (base p) p.variables.eraseDups es)).Occurs w' := by
      have : (renamed σ (base p) p.variables.eraseDups es).image r.variable =
          (σ.image r.variable).subst (rename d (base p) p.variables.eraseDups es) := ite_eq_left here
      rw [← this]
      exact occ
    obtain ⟨w, hw, rfl⟩ := (Term.occurs_rename _ _ _).mp occ'
    have win := (row_occurs r _ (armOf.images r hr) w).mp hw
    rcases targets r hr w win with ⟨l, fl⟩ | ⟨j, fj, _⟩
    · obtain ⟨e, he, src, tgt⟩ := find_mem es w _ fl
      obtain ⟨zero, bound⟩ := (table.name e he l tgt).2.1 on
      refine ⟨l.2, ?_, fun u lu hu lab => ?_⟩
      · rw [assign_sort, nameAt w l fl]
        have : l = (0, l.2) := Prod.ext zero rfl
        rw [← this]
      · have uin : u ∈ qs.map Prod.fst := by rw [hq.vars]; exact (inVs u).mpr hu
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp uin
        have known := hq.labelled x hx
        rw [lab] at known
        have leq : lu = x.2 := Option.some.inj known
        have small := indexBound_spec qs x hx
        rw [leq]
        exact UInt64.lt_iff_toNat_lt.mpr (Nat.lt_of_lt_of_le small bound)
    · obtain ⟨e, he, _, tgt⟩ := find_mem es w _ fj
      have off := (table.self e he j tgt).1
      rw [on] at off
      cases off
  · intro on v hv w' occ
    obtain ⟨r, hr, rfl⟩ := rowOf v hv
    have here : r.variable ∈ p.variables.eraseDups := (inVs _).mpr hv
    have occ' : ((σ.image r.variable).subst (rename d (base p) p.variables.eraseDups es)).Occurs w' := by
      have : (renamed σ (base p) p.variables.eraseDups es).image r.variable =
          (σ.image r.variable).subst (rename d (base p) p.variables.eraseDups es) := ite_eq_left here
      rw [← this]
      exact occ
    obtain ⟨w, hw, rfl⟩ := (Term.occurs_rename _ _ _).mp occ'
    have win := (row_occurs r _ (armOf.images r hr) w).mp hw
    rcases targets r hr w win with ⟨l, fl⟩ | ⟨j, fj, _⟩
    · obtain ⟨e, he, src, tgt⟩ := find_mem es w _ fl
      obtain ⟨zero, apart⟩ := (table.name e he l tgt).2.2 on
      refine ⟨l.2, ?_, fun u lu hu lab => ?_⟩
      · rw [assign_sort, nameAt w l fl]
        have : l = (0, l.2) := Prod.ext zero rfl
        rw [← this]
      · have uin : u ∈ qs.map Prod.fst := by rw [hq.vars]; exact (inVs u).mpr hu
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp uin
        have known := hq.labelled x hx
        rw [lab] at known
        have leq : lu = x.2 := Option.some.inj known
        rw [leq]
        exact apart x hx
    · obtain ⟨e, he, _, tgt⟩ := find_mem es w _ fj
      have off := (table.self e he j tgt).2.1
      rw [on] at off
      cases off
  · intro off
    simp only [UnavailableSort.noNatWitness, List.all_eq_true, bne_iff_ne, ne_eq]
    intro v hv w hw
    obtain ⟨r, hr, win⟩ := source w (List.mem_flatMap.mpr ⟨v, hv, hw⟩)
    have : ∃ t, find es w = some t := by
      rcases targets r hr w win with ⟨l, f⟩ | ⟨i, f, _⟩ <;> exact ⟨_, f⟩
    obtain ⟨t, ft⟩ := this
    obtain ⟨e, he, src, _⟩ := find_mem es w t ft
    rcases table.sorts e he with on | sort
    · rw [off] at on; cases on
    · rwa [src] at sort
  · have rowsOf : ∀ x ∈ arm.zipIdx, x.1 ∈ arm ∧ p.variables.eraseDups[x.2]? = some x.1.variable := by
      intro x hx
      have at_ := List.mem_zipIdx_iff_getElem?.mp hx
      refine ⟨List.mem_of_getElem? at_, ?_⟩
      rw [← armOf.keys, List.getElem?_map, at_]
      rfl
    have keys : (arm.zipIdx.map fun x => x.1.variable) = p.variables.eraseDups := by
      have e : (arm.zipIdx.map fun x => x.1.variable) = (arm.zipIdx.map Prod.fst).map Row.variable :=
        (List.map_map (g := Row.variable) (f := Prod.fst) (l := arm.zipIdx)).symm
      rw [e, List.zipIdx_map_fst, armOf.keys]
    refine ⟨rs.filterMap id, images σ (base p) p.variables.eraseDups es arm.zipIdx, rfl, ?_, ?_, ?_⟩
    · exact rows_read σ (base p) _ es _ rs hm fun x hx =>
        ⟨armOf.sorts x.1 (rowsOf x hx).1, armOf.images x.1 (rowsOf x hx).1⟩
    · rw [← keys]
      exact images_sublist σ (base p) _ es _
    · intro v hv
      have look := images_lookup σ (base p) p.variables.eraseDups es
        (renamed σ (base p) p.variables.eraseDups es).image arm.zipIdx ?_ ?_ v
      · rw [look, keys, ite_eq_left hv]
      · intro x hx st
        obtain ⟨hr, at_⟩ := rowsOf x hx
        obtain ⟨t, w, code, hvar, target⟩ := stands_spec es x.2 x.1 st
        have win : w ∈ x.1.variables := by simp [Row.variables, code, hvar]
        have im : σ.image x.1.variable = .var w :=
          row_single t w _ hvar (code ▸ armOf.images x.1 hr)
        show (if x.1.variable ∈ p.variables.eraseDups then _ else _) = _
        rw [ite_eq_left ((inVs _).mpr (rowIn x.1 hr)), im]
        show Term.var (assign _ _ _ w) = _
        rw [selfAt x.1 w x.2 target at_]
      · intro x hx _
        exact ite_eq_left ((inVs _).mpr (rowIn x.1 (rowsOf x hx).1))

/-! The family. -/

/-- An answer under an injective renaming of its range. -/
abbrev Renaming (p : Problem d.sig) (σ τ : Substitution d.sig) : Prop :=
  ∃ a : CallerFreshening.Allocation (CallerFreshening.sources p σ), CallerFreshening.Represents p σ τ a

theorem related_refinement (p : Problem d.sig) (xs ys : List (Substitution d.sig))
    (h : Related (Renaming p) xs ys) : OutputRefinement ⟨p, []⟩ xs ys := by
  induction h with
  | nil => exact ⟨fun ρ => by simp, fun σ hσ => (nomatch hσ), fun σ hσ => (nomatch hσ)⟩
  | @cons σ τ xs ys rep _ ih =>
    obtain ⟨a, rep⟩ := rep
    refine ⟨fun ρ => ?_, fun υ hυ => ?_, fun υ _ v _ w _ _ hin => (nomatch hin)⟩
    · have here := CallerFreshening.instance_iff rep ρ
      have rest := ih.equivalent ρ
      constructor
      · rintro ⟨υ, hυ, inst⟩
        rcases List.mem_cons.mp hυ with rfl | hυ
        · exact ⟨τ, List.mem_cons_self, here.mp inst⟩
        · obtain ⟨φ, hφ, inst⟩ := rest.mp ⟨υ, hυ, inst⟩
          exact ⟨φ, List.mem_cons_of_mem _ hφ, inst⟩
      · rintro ⟨υ, hυ, inst⟩
        rcases List.mem_cons.mp hυ with rfl | hυ
        · exact ⟨σ, List.mem_cons_self, here.mpr inst⟩
        · obtain ⟨φ, hφ, inst⟩ := rest.mpr ⟨υ, hυ, inst⟩
          exact ⟨φ, List.mem_cons_of_mem _ hφ, inst⟩
    · rcases List.mem_cons.mp hυ with rfl | hυ
      · exact rep.modulo.outside
      · exact ih.domain υ hυ

theorem natFree_iff {p : Problem d.sig} {σ : Substitution d.sig} {arm : List Row}
    (armOf : ArmOf d p.variables.eraseDups σ arm) :
    natFree arm = UnavailableSort.noNatWitness p σ := by
  rw [Bool.eq_iff_iff]
  simp only [natFree, UnavailableSort.noNatWitness, List.all_eq_true, bne_iff_ne, ne_eq]
  constructor
  · intro all v hv w hw
    have : v ∈ arm.map Row.variable := by rw [armOf.keys]; exact List.mem_eraseDups.mpr hv
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp this
    exact all r hr w ((row_occurs r _ (armOf.images r hr) w).mp ((Term.mem_variables _ w).mp hw))
  · intro all r hr w hw
    have : r.variable ∈ p.variables := List.mem_eraseDups.mp (armOf.keys ▸ List.mem_map_of_mem hr)
    exact all r.variable this w
      ((Term.mem_variables _ w).mpr ((row_occurs r _ (armOf.images r hr) w).mpr hw))

theorem kept_filter (nat : Bool) (p : Problem d.sig) (raw : List (Substitution d.sig)) :
    kept nat p raw = raw.filter fun σ => nat || UnavailableSort.noNatWitness p σ := by
  cases nat with
  | false => simp [kept]
  | true => exact (List.filter_eq_self.mpr fun _ _ => rfl).symm

/-- The arms that are read, each through a table that passed the test. -/
theorem select_named {p : Problem d.sig} {names : Array UInt64} {q : Query}
    {qs : List (Variable × Label)} {nat above unused : Bool}
    (hq : QueryOf names p.variables.eraseDups q qs) (arms : List (List Row))
    (raw : List (Substitution d.sig))
    (rel : Related (fun arm σ => ArmOf d p.variables.eraseDups σ arm) arms raw) (k : Nat)
    (ts : List (Nat × List Entry)) (out : List (List (Array UInt64)))
    (ok : ∀ t ∈ ts, tableOK q nat above unused t.2 = true)
    (h : select nat (arms.zipIdx k) ts = some out) :
    ∃ answers, Payload d (base p) p.variables.eraseDups out.flatten answers ∧
      Related (Renaming p) (raw.filter fun σ => nat || UnavailableSort.noNatWitness p σ) answers ∧
      (∀ τ ∈ answers, Fresh names p τ) ∧ (above = true → ∀ τ ∈ answers, Above names p τ) ∧
      (unused = true → ∀ τ ∈ answers, Unused names p τ) := by
  induction rel generalizing k ts out with
  | nil =>
    cases ts with
    | nil =>
      simp only [List.zipIdx_nil, select, Option.some.injEq] at h
      subst h
      exact ⟨[], .nil, .nil, fun τ hτ => (nomatch hτ), fun _ τ hτ => (nomatch hτ),
        fun _ τ hτ => (nomatch hτ)⟩
    | cons t ts => simp [select] at h
  | @cons arm σ arms raw armOf _ ih =>
    have skip : ∀ ts, (∀ t ∈ ts, tableOK q nat above unused t.2 = true) →
        (!nat && !natFree arm) = true → select nat (arms.zipIdx (k + 1)) ts = some out →
        ∃ answers, Payload d (base p) p.variables.eraseDups out.flatten answers ∧
          Related (Renaming p)
            ((σ :: raw).filter fun σ => nat || UnavailableSort.noNatWitness p σ) answers ∧
          (∀ τ ∈ answers, Fresh names p τ) ∧ (above = true → ∀ τ ∈ answers, Above names p τ) ∧
          (unused = true → ∀ τ ∈ answers, Unused names p τ) := by
      intro ts ok cond rest
      obtain ⟨answers, payload, related, fresh, high, low⟩ := ih (k + 1) ts out ok rest
      refine ⟨answers, payload, ?_, fresh, high, low⟩
      rw [natFree_iff armOf] at cond
      have dropped : (nat || UnavailableSort.noNatWitness p σ) = false := by
        cases nat <;> simp_all
      rw [List.filter_cons, dropped]
      exact related
    rw [List.zipIdx_cons] at h
    cases ts with
    | nil =>
      simp only [select] at h
      split at h
      · next cond => exact skip [] ok cond h
      · cases h
    | cons t ts =>
      simp only [select] at h
      split at h
      · cases ha : emitArm t.2 arm with
        | none => simp [ha] at h
        | some o =>
          cases hs : select nat (arms.zipIdx (k + 1)) ts with
          | none => simp [ha, hs] at h
          | some rest =>
            simp only [ha, hs, Option.bind_some, Option.map_some, Option.some.injEq] at h
            subst h
            obtain ⟨answers, payload, related, fresh, high, low⟩ :=
              ih (k + 1) ts rest (fun u hu => ok u (List.mem_cons_of_mem _ hu)) hs
            obtain ⟨τ, rep, fr, hi, lo, noNat, rows, found, rfl, read, sub, look⟩ :=
              arm_named hq (ok t List.mem_cons_self) armOf ha
            have keep : (nat || UnavailableSort.noNatWitness p σ) = true := by
              cases hn : nat with
              | true => rfl
              | false => simpa using noNat hn
            refine ⟨τ :: answers, ?_, ?_, ?_, ?_, ?_⟩
            · rw [List.flatten_cons]
              exact .cons read sub look payload
            · rw [List.filter_cons, keep]
              exact .cons rep related
            · intro υ hυ
              rcases List.mem_cons.mp hυ with rfl | hυ
              · exact fr
              · exact fresh υ hυ
            · intro on υ hυ
              rcases List.mem_cons.mp hυ with rfl | hυ
              · exact hi on
              · exact high on υ hυ
            · intro on υ hυ
              rcases List.mem_cons.mp hυ with rfl | hυ
              · exact lo on
              · exact low on υ hυ
      · split at h
        · next cond => exact skip (t :: ts) ok cond h
        · cases h

theorem heads_variables (arm : List Row) :
    headVariables (arm.flatMap fun r => [r.key, r.sort]) = some (arm.map Row.variable) := by
  induction arm with
  | nil => rfl
  | cons r rs ih => simp [headVariables, ih, Row.variable]

theorem admissible_declined (heads : Array UInt64) (q : Query) (nat above unused : Bool) :
    admissible heads q nat above unused #[#[0]] = false := by
  simp [admissible, tables]

/-- What `choose` returns: the decline word, or tables that passed a test. -/
theorem choose_cases (heads : Array UInt64) (q : Query) (nat low : Bool)
    (proposed : Array (Array UInt64)) (defaults : Bool → Array (Array UInt64)) :
    choose heads q nat low proposed defaults = #[#[0]] ∨
      (choose heads q nat low proposed defaults = proposed ∧
        admissible heads q nat false false proposed = true) ∨
      admissible heads q nat true false (choose heads q nat low proposed defaults) = true ∨
      (low = true ∧
        admissible heads q nat false true (choose heads q nat low proposed defaults) = true) := by
  unfold choose
  by_cases first : admissible heads q nat false false proposed = true
  · exact .inr (.inl ⟨by simp [first], first⟩)
  · by_cases second : admissible heads q nat true false (defaults false) = true
    · exact .inr (.inr (.inl (by simp [first, second])))
    · cases low with
      | false => exact .inl (by simp [first, second])
      | true =>
        by_cases third : admissible heads q nat false true (defaults true) = true
        · exact .inr (.inr (.inr ⟨rfl, by simp [first, second, third]⟩))
        · exact .inl (by simp [first, second, third])

/-- What `run` returns: the decline word, or tables that passed a test. -/
theorem run_tables (names heads : Array UInt64) (ranges proposal : Array (Array UInt64))
    (nat low : Bool) :
    run names heads ranges proposal nat low = #[#[0]] ∨
      ∃ q above unused, query names heads = some q ∧
        admissible heads q nat above unused (run names heads ranges proposal nat low) = true ∧
        (proposal = #[] → above = true ∨ unused = true) ∧
        (proposal = #[] → low = false → above = true) := by
  unfold run
  cases hq : query names heads with
  | none => exact .inl rfl
  | some q =>
    simp only
    rcases choose_cases heads q nat low
      (if proposal.size = 0 then #[#[0]]
        else (tablesFor q heads ranges (some proposal.toList) nat false).getD #[#[0]])
      (fun low => (tablesFor q heads ranges none nat low).getD #[#[0]]) with
      declined | ⟨same, ok⟩ | ok | ⟨settled, ok⟩
    · exact .inl declined
    · have absurd : proposal ≠ #[] := by
        intro empty
        subst empty
        simp [admissible_declined] at ok
      exact .inr ⟨q, false, false, rfl, by rw [same]; exact ok,
        fun empty => (absurd empty).elim, fun empty => (absurd empty).elim⟩
    · exact .inr ⟨q, true, false, rfl, ok, fun _ => .inl rfl, fun _ _ => rfl⟩
    · refine .inr ⟨q, false, true, rfl, ok, fun _ => .inr rfl, fun _ strict => ?_⟩
      rw [settled] at strict
      cases strict

/-- An index above every index of the query is an index of no query variable. -/
theorem Above.unused {names : Array UInt64} {p : Problem d.sig} {σ : Substitution d.sig}
    (h : Above names p σ) : Unused names p σ := by
  intro v hv w hw
  obtain ⟨i, eq, below⟩ := h v hv w hw
  refine ⟨i, eq, fun u l hu lab same => ?_⟩
  have := UInt64.lt_iff_toNat_lt.mp (below u l hu lab)
  rw [same] at this
  exact Nat.lt_irrefl _ this

theorem correct : Correct run := by
  refine ⟨fun ds ns es names heads ranges proposal nat low reply d p raw named _ hdec happ => ?_⟩
  rcases run_tables names heads ranges proposal nat low with
    declined | ⟨q, above, unused, hq, adm, mode, strict⟩
  · rw [declined] at happ
    simp [apply, tables] at happ
  · generalize run names heads ranges proposal nat low = words at happ adm
    unfold admissible at adm
    cases ht : tables words with
    | none => simp [ht] at adm
    | some t =>
    simp only [ht, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at adm
    obtain ⟨headsEq, tablesOk⟩ := adm
    unfold apply at happ
    simp only [ht, Option.bind_some] at happ
    obtain ⟨rows, shape, payload⟩ := hdec
    obtain ⟨groups, fold, rel⟩ := collect_payload _ rows raw payload
    have state : reply.foldr collect ([], []) = ([#[1]], groups) := by
      rw [← Array.foldr_toList, shape, List.foldr_cons, fold]
      simp [collect]
    simp only [state, ↓reduceIte] at happ
    cases hp : groups.mapM (fun (rows : List (Array UInt64)) => rows.mapM parseRow) with
    | none => simp [hp] at happ
    | some arms =>
    simp only [hp, Option.bind_some] at happ
    split at happ
    · next headsOk =>
      cases hs : select nat arms.zipIdx t.arms with
      | none => simp [hs] at happ
      | some out =>
      simp only [hs, Option.map_some, Option.some.injEq] at happ
      subst happ
      have armsRel : Related (fun arm σ => ArmOf d p.variables.eraseDups σ arm) arms raw :=
        ((mapM_related _ _ _ hp).flip.comp rel).imp fun arm σ ⟨g, parsed, read⟩ =>
          arm_of _ σ g arm read parsed
      rw [kept_filter]
      cases armsRel with
      | nil =>
        cases hts : t.arms with
        | cons u us => simp [hts, select] at hs
        | nil =>
          simp only [hts, List.zipIdx_nil, select, Option.some.injEq] at hs
          subst hs
          exact ⟨[], ⟨[], by simp, .nil⟩, fun ne => (ne rfl).elim, related_refinement p _ _ .nil,
            fun σ hσ => (nomatch hσ), fun _ σ hσ => (nomatch hσ), fun _ _ σ hσ => (nomatch hσ)⟩
      | @cons arm σ arms raw armOf rest =>
        have first : (arm.flatMap fun r => [r.key, r.sort]) = heads.toList := by
          have := (List.all_eq_true.mp headsOk) arm List.mem_cons_self
          rw [← headsEq]
          simpa using this
        have vars : headVariables heads.toList = some p.variables.eraseDups := by
          rw [← first, heads_variables, armOf.keys]
        obtain ⟨qs, hq⟩ := query_of names heads q _ hq vars
        obtain ⟨answers, payload, related, fresh, high, lower⟩ :=
          select_named hq (arm :: arms) (σ :: raw) (.cons armOf rest) 0 t.arms out
            (fun u hu => tablesOk u hu) hs
        refine ⟨answers, ⟨out.flatten, by simp, payload⟩,
          fun _ => ⟨fun v hv => ?_, fun u v hu hv sort lab => ?_⟩,
          related_refinement p _ _ related, fresh, fun empty σ hσ => ?_,
          fun empty off => high (strict empty off)⟩
        · have vin : v ∈ qs.map Prod.fst := by
            rw [hq.vars, List.mem_eraseDups, Problem.mem_variables]; exact hv
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp vin
          rw [hq.labelled x hx]
          rfl
        · have uin : u ∈ qs.map Prod.fst := by
            rw [hq.vars, List.mem_eraseDups, Problem.mem_variables]; exact hu
          have vin : v ∈ qs.map Prod.fst := by
            rw [hq.vars, List.mem_eraseDups, Problem.mem_variables]; exact hv
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp uin
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp vin
          rw [hq.labelled x hx, hq.labelled y hy] at lab
          obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hx
          obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hy
          have la : a < (queryKeys qs).length := by simpa [queryKeys] using ha
          have lb : b < (queryKeys qs).length := by simpa [queryKeys] using hb
          have key : (queryKeys qs)[a] = (queryKeys qs)[b] := by
            simp only [queryKeys, List.getElem_map]
            rw [Option.some.inj lab, sort]
          have pa := hq.distinct a la
          rw [key, hq.distinct b lb] at pa
          subst pa
          rfl
        · rcases mode empty with on | on
          · exact (high on σ hσ).unused
          · exact lower on σ hσ
    · cases happ

/-- The decline word of the unifier has no reading. -/
theorem apply_declined (words : Array (Array UInt64)) (nat : Bool) : apply words nat #[#[0]] = none := by
  unfold apply
  cases tables words with
  | none => rfl
  | some t => simp [collect]

end Tamarin.UnifierNames
