import Tamarin.MaudeUnifyWire
import Tamarin.TotalUnifyPacket

/-!
# Maude's unification of a query, under the caller's ranks

The port of Maude's unification algorithm (`Tamarin.MaudeUnify.unify`) run on
the query of an ordinary unification packet (`TotalUnifyWire.input`) with
ranks the caller chooses, so that a caller that gives Maude's ranks gets the
unifiers Maude would print, in Maude's order. Nothing below depends on the
ranks being Maude's: whatever they are, the answers form a complete set of
unifiers (`run_valid`).

The rank words are rows of `ranks`, an entry that is missing counting as 0:

* row 0, 1, 2: the rank of the free, C and AC symbol with id `i` at index `i`;
* row 3: the rank of the operator of the name constants of a sort, at the
  sort's code (`TotalUnifyWire.sortCode`); a name constant of id `k` has
  argument `k`;
* row 4: the rank of the variable symbol of the error sort at index 0 and of
  each sort at its code plus one;
* row 5: the index of the error sort and of each sort, at the same places.

A variable of the query has its identifier as the code of its name.

The variables of the query get the slots in the order in which they occur in
the sides of the equations, each side normalised with these ranks (AC
arguments sorted, C arguments ordered), equation by equation, left side
first: Maude's numbering (`UnificationProblem::UnificationProblem`). The reply
lists the bindings of every answer in that order. The variables of an answer
are numbered from the least identifier above the query's variables, in the
order of the port's output slots, which is Maude's `#1, #2, …`.
-/
namespace Tamarin.MaudeUnifyExport
open TotalUnifyWire MaudeUnify

variable {d : Dictionary}

/-- The rank word at `row`, `i`, or 0. -/
def word (w : Array (Array UInt64)) (row i : Nat) : Nat := ((w.getD row #[]).getD i 0).toNat

/-- The index of an optional sort in rows 4 and 5. -/
def optCode : Option SortId → Nat
  | none => 0
  | some x => (sortCode x).toNat + 1

/-- The ranks: those of the rank words, and for the variable in slot `j` of
`vs` its identifier, for a later slot a number above every identifier. -/
def ranks (w : Array (Array UInt64)) (vs : List Variable) : Ranks d.sig where
  atom a := word w 3 (sortCode a.val.2).toNat
  atomArg a := a.val.1.toNat
  free f := word w 0 f.val.toNat
  comm f := word w 1 f.val.toNat
  ac f := word w 2 f.val.toNat
  varSym o := word w 4 (optCode o)
  name j := match vs[j]? with
    | some v => v.id
    | none => UInt64.size + j
  sortIndex o := word w 5 (optCode o)

/-- Maude's slots: the variables of the query by first occurrence in the
sides normalised with the ranks, equation by equation, left side first.
The provisional slots of the normalisation are those of first occurrence in
the query; the order of two variables does not depend on their slots. -/
def slotOrder (w : Array (Array UInt64)) (p : Problem d.sig) : List Variable :=
  let vs := varsOf p
  nub ((((dagsOf (ranks w vs) vs p).flatMap fun q => q.1.vars ++ q.2.vars).filterMap
    fun i => vs[i]?) ++ vs)

theorem nub_nodup {α : Type} [DecidableEq α] (l : List α) : (nub l).Nodup := by
  have gen : ∀ (l acc : List α), acc.Nodup →
      (l.foldl (fun acc x => if x ∈ acc then acc else x :: acc) acc).Nodup := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons y ys ih =>
      intro acc h
      simp only [List.foldl_cons]
      apply ih
      by_cases hy : y ∈ acc
      · rw [ite_eq_left hy]; exact h
      · rw [ite_eq_right hy]; exact List.nodup_cons.mpr ⟨hy, h⟩
  unfold nub
  exact List.pairwise_reverse.mpr ((gen l [] List.nodup_nil).imp fun h e => h e.symm)

theorem mem_slotOrder (w : Array (Array UInt64)) (p : Problem d.sig) (v : Variable) :
    v ∈ slotOrder w p ↔ p.Occurs v := by
  unfold slotOrder
  simp only [mem_nub, List.mem_append]
  rw [← varsOf_occurs]
  constructor
  · rintro (h | h)
    · obtain ⟨i, _, e⟩ := List.mem_filterMap.mp h
      exact List.mem_of_getElem? e
    · exact h
  · exact .inr

theorem slotOrder_nodup (w : Array (Array UInt64)) (p : Problem d.sig) : (slotOrder w p).Nodup :=
  nub_nodup _

/-- The reply that lists `answers`, each binding the variables `vs` in that
order: `TotalUnifyWire.pack` with the order given. `none` when a variable or
an arity does not fit a word. -/
def packIn (vs : List Variable) (answers : List (Substitution d.sig)) : Option (Array (Array UInt64)) := do
  return (#[1] :: (← answers.mapM (arm vs)).flatten).toArray

private theorem map_read {α β γ : Type} (f : α → Option β) (g : β → Option γ)
    (value : α → γ) (agree : ∀ x y, f x = some y → g y = some (value x))
    (xs : List α) (ys : List β) (h : xs.mapM f = some ys) : ys.mapM g = some (xs.map value) := by
  induction xs generalizing ys with
  | nil => cases h; rfl
  | cons a as ih =>
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases tail : as.mapM f with
      | none => simp [ha,tail] at h
      | some bs =>
        simp [ha,tail] at h; subst ys
        simp [agree _ _ ha,ih _ tail]

private theorem payload (vs : List Variable) (answers : List (Substitution d.sig)) (rows)
    (h : answers.mapM (arm vs) = some rows) : Packet.Payload d vs rows.flatten answers := by
  induction answers generalizing rows with
  | nil => cases h; exact .nil
  | cons σ answers ih =>
    cases head : vs.mapM (binding σ) with
    | none => simp [arm,head] at h
    | some bs =>
      have one : arm vs σ = some (#[] :: bs) := by simp [arm,head]
      cases tail : answers.mapM (arm vs) with
      | none => simp [one,tail] at h
      | some rest =>
        simp [one,tail] at h; subst rows
        exact .cons (map_read _ _ _ (Packet.binding_read σ) _ _ head) (ih _ tail)

theorem packIn_payload (vs : List Variable) (answers : List (Substitution d.sig)) {wire}
    (h : packIn vs answers = some wire) :
    ∃ rows, wire.toList = #[1] :: rows ∧ Packet.Payload d vs rows answers := by
  cases result : answers.mapM (arm vs) with
  | none => simp [packIn,result] at h
  | some rs =>
    simp [packIn,result] at h; subst wire
    exact ⟨rs.flatten,by simp,payload _ _ _ result⟩

/-- The give-up word: the port ran out of fuel, or a variable or an arity of
an answer does not fit a word. -/
def gaveUp : Array (Array UInt64) := #[#[3]]

section
variable [Interrupt]

/-- The port on a decoded query, its answers listed in the slot order. -/
def answer (w : Array (Array UInt64)) (fuel : Nat) (p : Problem d.sig) : Array (Array UInt64) :=
  let vs := slotOrder w p
  match portSolveWith (ranks w vs) vs fuel p (fun v o => (mem_slotOrder w p v).mpr o) [] with
  | some answers => (packIn vs answers).getD gaveUp
  | none => gaveUp

/-- The export: `#[#[0]]` for a packet that does not decode. -/
def run (decls : Array UInt64) (w : Array (Array UInt64)) (fuel : UInt64) (nodes : Array (Array UInt64))
    (roots : Array UInt64) : Array (Array UInt64) :=
  match input decls nodes roots with
  | some ⟨_, p⟩ => answer w fuel.toNat p
  | none => #[#[0]]

end

theorem run_malformed {decls : Array UInt64} {nodes : Array (Array UInt64)} {roots : Array UInt64}
    (h : input decls nodes roots = none) (w : Array (Array UInt64)) (fuel : UInt64) :
    run decls w fuel nodes roots = #[#[0]] := by
  simp only [run, h]

theorem answer_valid (w : Array (Array UInt64)) (fuel : Nat) (p : Problem d.sig) :
    answer w fuel p = gaveUp ∨
      ∃ answers vs rows, (Outcome.complete answers).CorrectIn p [] ∧ vs.Nodup ∧
        (∀ v, v ∈ vs ↔ p.Occurs v) ∧ (answer w fuel p).toList = #[1] :: rows ∧
        Packet.Payload d vs rows answers := by
  unfold answer
  simp only
  split
  · next answers h =>
    cases packed : packIn (slotOrder w p) answers with
    | none => exact .inl rfl
    | some wire =>
      right
      obtain ⟨rows, shape, pl⟩ := packIn_payload _ _ packed
      obtain ⟨complete, rest⟩ := portSolveWith_spec _ _ fuel p _
        (fun v hv => (mem_slotOrder w p v).mp hv) [] h
      exact ⟨answers, slotOrder w p, rows,
        ⟨complete, fun σ hσ => (rest σ hσ).1, fun σ hσ => (rest σ hσ).2⟩,
        slotOrder_nodup w p, mem_slotOrder w p, by simpa using shape, pl⟩
  · exact .inl rfl

theorem run_valid {decls : Array UInt64} {nodes : Array (Array UInt64)} {roots : Array UInt64}
    {d : Dictionary} {p : Problem d.sig} (h : input decls nodes roots = some ⟨d, p⟩)
    (w : Array (Array UInt64)) (fuel : UInt64) :
    run decls w fuel nodes roots = gaveUp ∨
      ∃ answers vs rows, (Outcome.complete answers).CorrectIn p [] ∧ vs.Nodup ∧
        (∀ v, v ∈ vs ↔ p.Occurs v) ∧ (run decls w fuel nodes roots).toList = #[1] :: rows ∧
        Packet.Payload d vs rows answers := by
  have e : run decls w fuel nodes roots = answer w fuel.toNat p := by simp only [run, h]
  rw [e]
  exact answer_valid w fuel.toNat p

end Tamarin.MaudeUnifyExport
