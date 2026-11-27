import Tamarin.Unification
import Tamarin.TermEquality
import Tamarin.VariablePermutation
import Tamarin.VariablesFast
import Tamarin.Buckets

/-! Remove repeated answers. Two alignments of a commutative pair, or two
selections of AC generators, can yield the same substitution on the query
variables. Only the images of the query variables are observable, so keeping
the first answer of each group preserves a complete set. -/
namespace Tamarin.DistinctAnswers
variable {s : Signature} [DecidableEq s.Atom] [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym]

/-- A cheap key read from the top of a term and from the whole right spine of
a product: the answers of one query differ in the later operands of long
products. Symbols are not inspected. -/
private def termKey : Term s → Nat → UInt64
  | _, 0 => 0
  | .var v, _+1 => 2 * v.id.toUInt64 + 1
  | .atom _, _+1 => 2
  | .free f xs, d+1 => Fin.foldl (s.arity f) (fun acc i => acc * 31 + termKey (xs i) d) 3
  | .comm _ a b, d+1 => (termKey a d * 31 + termKey b d) * 37 + 5
  | .ac _ a b, d+1 => (termKey a d * 31 + termKey b (d+1)) * 41 + 7

private def bucketOf (seen : Array (List (List (Term s)))) (key : List (Term s)) : Nat :=
  (key.foldl (fun h t => h * 1000003 + termKey t 4) 7).toNat % seen.size

private def bucket (seen : Array (List (List (Term s)))) (i : Nat) : List (List (Term s)) :=
  (seen[i]?).getD []

/-- Keep the first answer of each group. An answer is compared only with the
kept answers whose images have the same key. -/
private def prune (vars : List Variable) :
    List (Substitution s) → Array (List (List (Term s))) → List (Substitution s)
  | [], _ => []
  | σ :: rest, seen =>
    let key := vars.map σ.image
    let i := bucketOf seen key
    if key ∈ bucket seen i then prune vars rest seen
    else σ :: prune vars rest (seen.modify i (key :: ·))

/-- `prune` carrying the kept answers, so that its stack does not grow with
the number of answers. -/
private def pruneLoop (vars : List Variable) :
    List (Substitution s) → Array (List (List (Term s))) → List (Substitution s) →
      List (Substitution s)
  | [], _, kept => kept.reverse
  | σ :: rest, seen, kept =>
    let key := vars.map σ.image
    let i := bucketOf seen key
    if key ∈ bucket seen i then pruneLoop vars rest seen kept
    else pruneLoop vars rest (seen.modify i (key :: ·)) (σ :: kept)

private theorem pruneLoop_eq (vars : List Variable) (xs : List (Substitution s))
    (seen : Array (List (List (Term s)))) (kept : List (Substitution s)) :
    pruneLoop vars xs seen kept = kept.reverse ++ prune vars xs seen := by
  induction xs generalizing seen kept with
  | nil => simp [pruneLoop, prune]
  | cons σ rest ih =>
    simp only [pruneLoop, prune]
    split
    · exact ih _ _
    · rw [ih]; simp

private def pruneFast (vars : List Variable) (xs : List (Substitution s))
    (seen : Array (List (List (Term s)))) : List (Substitution s) :=
  pruneLoop vars xs seen []

@[csimp] private theorem prune_eq_fast : @prune = @pruneFast := by
  funext s _ _ _ _ vars xs seen
  simp [pruneFast, pruneLoop_eq]

private theorem prune_subset (vars : List Variable) (xs : List (Substitution s))
    (seen : Array (List (List (Term s)))) : ∀ σ ∈ prune vars xs seen, σ ∈ xs := by
  induction xs generalizing seen with
  | nil => intro σ h; cases h
  | cons τ rest ih =>
    intro σ h
    simp only [prune] at h
    split at h
    · exact List.mem_cons_of_mem _ (ih _ σ h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ σ h)

omit [DecidableEq s.Atom] [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] in
private theorem bucket_modify (seen : Array (List (List (Term s)))) (i j : Nat)
    (key k : List (Term s)) (h : k ∈ bucket (seen.modify i (key :: ·)) j) :
    k = key ∨ k ∈ bucket seen j := by
  unfold bucket at h ⊢
  rw [Array.getElem?_modify] at h
  split at h
  · next same =>
    subst same
    cases at_i : seen[i]? with
    | none => simp [at_i] at h
    | some old =>
      simp only [at_i, Option.map_some, Option.getD_some, List.mem_cons] at h ⊢
      exact h
  · exact .inr h

private theorem prune_keeps (vars : List Variable) (xs : List (Substitution s))
    (seen : Array (List (List (Term s)))) : ∀ σ ∈ xs, (∃ i, vars.map σ.image ∈ bucket seen i) ∨
      ∃ τ ∈ prune vars xs seen, vars.map τ.image = vars.map σ.image := by
  induction xs generalizing seen with
  | nil => intro σ h; cases h
  | cons τ rest ih =>
    intro σ h
    simp only [prune]
    split
    · next old =>
      rcases List.mem_cons.mp h with rfl | h
      · exact .inl ⟨_,old⟩
      · exact ih seen σ h
    · rcases List.mem_cons.mp h with rfl | h
      · exact .inr ⟨_, List.mem_cons_self, rfl⟩
      · rcases ih _ σ h with ⟨j,known⟩ | ⟨υ,hυ,same⟩
        · rcases bucket_modify seen _ j _ _ known with first | known
          · exact .inr ⟨τ, List.mem_cons_self, first.symm⟩
          · exact .inl ⟨j,known⟩
        · exact .inr ⟨υ, List.mem_cons_of_mem _ hυ, same⟩

/-- A single answer needs no comparison. -/
def distinct (p : Problem s) (xs : List (Substitution s)) : List (Substitution s) :=
  if xs.length ≤ 1 then xs
  else prune (Buckets.dedup Variable.id p.variables) xs (Array.replicate (2 * xs.length + 1) [])

theorem distinct_subset (p : Problem s) (xs : List (Substitution s)) :
    ∀ σ ∈ distinct p xs, σ ∈ xs := by
  unfold distinct
  split
  · exact fun _ h => h
  · exact prune_subset _ xs _

theorem distinct_keeps (p : Problem s) (xs : List (Substitution s)) :
    ∀ σ ∈ xs, ∃ τ ∈ distinct p xs, ∀ v, p.Occurs v → τ.image v = σ.image v := by
  intro σ h
  unfold distinct
  split
  · exact ⟨σ, h, fun _ _ => rfl⟩
  · rcases prune_keeps (Buckets.dedup Variable.id p.variables) xs
      (Array.replicate (2 * xs.length + 1) []) σ h with ⟨i,none⟩ | ⟨τ,hτ,same⟩
    · unfold bucket at none
      rw [Array.getElem?_replicate] at none
      split at none <;> cases none
    · rw [Buckets.dedup_eq] at same
      exact ⟨τ, hτ, fun v hv => List.map_inj_left.mp same v
        (List.mem_eraseDups.mpr ((p.mem_variables v).mpr hv))⟩

/-- The same unifier without repeated answers. -/
def unifier (u : VerifiedUnifier s (fun _ => True)) : VerifiedUnifier s (fun _ => True) where
  solve p hp avoid := distinct p (u.solve p hp avoid)
  correct p hp avoid := by
    constructor
    · exact fun σ h => (u.correct p hp avoid).sound σ (distinct_subset p _ σ h)
    · intro ρ sol
      obtain ⟨σ,hσ,δ,inst⟩ := (u.correct p hp avoid).covers ρ sol
      obtain ⟨τ,hτ,same⟩ := distinct_keeps p _ σ hσ
      refine ⟨τ, hτ, δ, fun v hv => ?_⟩
      have at_v := inst v hv
      change EquivB _ (δ.apply (σ.image v)) at at_v
      change EquivB _ (δ.apply (τ.image v))
      rw [same v hv]
      exact at_v
  domain p hp avoid σ h := u.domain p hp avoid σ (distinct_subset p _ σ h)
  fresh p hp avoid σ h := u.fresh p hp avoid σ (distinct_subset p _ σ h)

end Tamarin.DistinctAnswers
