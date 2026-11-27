import Tamarin.PresentationComponents
import Tamarin.SubtermDecrease
import Tamarin.SignatureExtension
import Tamarin.DestructorTable

/-! A class of tables that the certifier has to accept: constructor-pattern
rules whose results are subterms or constants. Every left side is a free
application over arguments that contain no head of a left side. The rules of
one head either all return the subterm at one common position below the
root, or all return one closed term that contains no head of a left side and
has fewer symbols than the left side. Every result has the sort of its left
side.

This is the shape of the equations of pairing, symmetric and asymmetric
encryption, signatures with a `true` constant, and of user equations in the
subterm-convergent form without nested defined symbols. Nothing here says how
such a table is recognized. -/
namespace Tamarin.SubtermTable
open Rewriting ConstructorVariants SignatureExtension
variable {s : Signature}

/-- The number of positions of a term that hold an operator or a name. -/
def symbols : Term s → Nat
  | .var _ => 0
  | .atom _ => 1
  | .free _ xs => 1 + (List.ofFn fun i => symbols (xs i)).sum
  | .comm _ a b => 1 + symbols a + symbols b
  | .ac _ a b => 1 + symbols a + symbols b

structure Presentation (rs : Problem s) : Prop where
  patterns : ∀ r ∈ rs, ∃ f xs, r.lhs = .free f xs ∧ ∀ i, ConstructorRows.Inert rs (xs i)
  results : ∀ r ∈ rs,
    (∃ p : List Nat, p ≠ [] ∧ ∀ q ∈ rs, head q.lhs = head r.lhs →
      DestructorTable.atPath q.lhs p = some q.rhs) ∨
    (r.rhs.Ground ∧ ConstructorRows.Inert rs r.rhs ∧ symbols r.rhs < symbols r.lhs ∧
      ∀ q ∈ rs, head q.lhs = head r.lhs → q.rhs = r.rhs)
  typed : ∀ r ∈ rs, HasSort r.rhs r.lhs.rootSort

theorem rank_one (t : Term s) : SymbolWeight.rank (fun _ => 1) t = symbols t := by
  induction t with
  | var => rfl
  | atom => rfl
  | free f xs ih =>
    change (List.ofFn fun i => SymbolWeight.rank (fun _ => 1) (xs i)).sum + 1 = _
    simp only [ih,symbols]
    omega
  | comm f a b ia ib =>
    change SymbolWeight.rank (fun _ => 1) a + SymbolWeight.rank (fun _ => 1) b + 1 = _
    simp only [ia,ib,symbols]
    omega
  | ac f a b ia ib =>
    change SymbolWeight.rank (fun _ => 1) a + SymbolWeight.rank (fun _ => 1) b + 1 = _
    simp only [ia,ib,symbols]
    omega

theorem atPath_subterm {t u : Term s} {p : List Nat} (h : DestructorTable.atPath t p = some u) :
    u ∈ MixedUnification.subterms t := by
  induction p generalizing t with
  | nil =>
    simp only [DestructorTable.atPath,Option.some.injEq] at h
    subst h
    cases t <;> simp [MixedUnification.subterms]
  | cons i p ih =>
    cases t <;> simp only [DestructorTable.atPath] at h <;> try contradiction
    split at h <;> try contradiction
    next f xs hi =>
      simp only [MixedUnification.subterms]
      exact List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨⟨i,hi⟩,rfl⟩,ih h⟩)

/-- The term at a position below the root is a proper subterm. -/
theorem atPath_proper {t u : Term s} {p : List Nat} (h : DestructorTable.atPath t p = some u)
    (below : p ≠ []) : u ∈ (MixedUnification.subterms t).tail := by
  cases p with
  | nil => exact absurd rfl below
  | cons i p =>
    cases t <;> simp only [DestructorTable.atPath] at h <;> try contradiction
    split at h <;> try contradiction
    next f xs hi =>
      simp only [MixedUnification.subterms,List.tail_cons]
      exact List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨⟨i,hi⟩,rfl⟩,atPath_subterm h⟩

variable {x : Signature}

/-- The head of a term in an extension of the signature. -/
def liftHead (x : Signature) : Head s → Head (joined s x)
  | .var v => .var v
  | .atom a => .atom (.inl a)
  | .free f => .free (.inl f)
  | .comm f => .comm (.inl f)
  | .ac f => .ac (.inl f)

theorem liftHead_inj {a b : Head s} (h : liftHead x a = liftHead x b) : a = b := by
  cases a <;> cases b <;> simp_all [liftHead]

theorem head_embed (t : Term s) : head (embed x t) = liftHead x (head t) := by
  cases t <;> rfl

theorem operators_embed (t : Term s) : operators (embed x t) = (operators t).map (liftHead x) := by
  induction t with
  | var => rfl
  | atom => rfl
  | free f xs ih =>
    change Head.free (Sum.inl f) :: (List.ofFn fun i => operators (embed x (xs i))).flatten = _
    simp only [ih,operators,List.map_cons,List.map_flatten,List.map_ofFn,liftHead]
    rfl
  | comm f a b ia ib =>
    change Head.comm (Sum.inl f) :: (operators (embed x a) ++ operators (embed x b)) = _
    simp [ia,ib,operators,liftHead]
  | ac f a b ia ib =>
    change Head.ac (Sum.inl f) :: (operators (embed x a) ++ operators (embed x b)) = _
    simp [ia,ib,operators,liftHead]

theorem ruleHeads_query (rs : Problem s) : ruleHeads (query x rs) = (ruleHeads rs).map (liftHead x) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    change head (embed x r.lhs) :: ruleHeads (query x rs) =
      liftHead x (head r.lhs) :: (ruleHeads rs).map (liftHead x)
    rw [ih,head_embed]
    rfl

theorem inert_embed {rs : Problem s} {t : Term s} (h : ConstructorRows.Inert rs t) :
    ConstructorRows.Inert (query x rs) (embed x t) := by
  intro f hf hr
  rw [operators_embed] at hf
  rw [ruleHeads_query] at hr
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hf
  obtain ⟨b,hb,eq⟩ := List.mem_map.mp hr
  exact h a ha (liftHead_inj eq ▸ hb)

theorem atPath_embed (t : Term s) (p : List Nat) :
    DestructorTable.atPath (embed x t) p = (DestructorTable.atPath t p).map (embed x) := by
  induction p generalizing t with
  | nil => simp [DestructorTable.atPath]
  | cons i p ih =>
    cases t with
    | free f xs =>
      change (if h : i < s.arity f then DestructorTable.atPath (embed x (xs ⟨i,h⟩)) p else none) = _
      simp only [DestructorTable.atPath]
      split
      · exact ih _
      · rfl
    | var | atom | comm | ac => simp [DestructorTable.atPath,embed]

theorem symbols_embed (t : Term s) : symbols (embed x t) = symbols t := by
  induction t with
  | var => rfl
  | atom => rfl
  | free f xs ih =>
    change 1 + (List.ofFn fun i => symbols (embed x (xs i))).sum = _
    simp only [ih,symbols]
  | comm f a b ia ib =>
    change 1 + symbols (embed x a) + symbols (embed x b) = _
    simp only [ia,ib,symbols]
  | ac f a b ia ib =>
    change 1 + symbols (embed x a) + symbols (embed x b) = _
    simp only [ia,ib,symbols]

theorem closed_embed {t : Term s} (ground : t.Ground) : (embed x t).variables = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro v hv
  exact ground v ((embed_occurs t v).mp ((Term.mem_variables _ v).mp hv))

variable [DecidableEq (joined s x).FreeSym] [DecidableEq (joined s x).CSym]
  [DecidableEq (joined s x).ACSym] [DecidableEq (joined s x).Atom]

/-- A table of the class passes the test for tables without components, in
every extension of its signature and at every depth. -/
theorem accepted {rs : Problem s} (cls : Presentation rs) (fuel : Nat) :
    PresentationComponents.accepts [] (SubtermDecrease.proposeWeight (fun _ => 1)) fuel
      (query x rs) = true := by
  have source (r' : Equation (joined s x)) (hr' : r' ∈ query x rs) :
      ∃ r ∈ rs, r' = ⟨embed x r.lhs,embed x r.rhs⟩ := by
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hr'
    exact ⟨r,hr,rfl⟩
  have lifted (r : Equation s) (hr : r ∈ rs) :
      (⟨embed x r.lhs,embed x r.rhs⟩ : Equation (joined s x)) ∈ query x rs :=
    List.mem_map.mpr ⟨r,hr,rfl⟩
  have same_head {q r : Equation s} (h : head (embed x q.lhs) = head (embed x r.lhs)) :
      head q.lhs = head r.lhs := by
    rw [head_embed,head_embed] at h
    exact liftHead_inj h
  apply PresentationComponents.accepts_of_checked
  · intro r' hr'
    obtain ⟨r,hr,rfl⟩ := source r' hr'
    obtain ⟨f,xs,shape,_⟩ := cls.patterns r hr
    exact ⟨.inl f,fun i => embed x (xs i),by rw [shape]; rfl⟩
  · apply List.all_eq_true.mpr
    intro r' hr'
    obtain ⟨r,hr,rfl⟩ := source r' hr'
    obtain ⟨f,xs,shape,_⟩ := cls.patterns r hr
    have typed := cls.typed r hr
    rw [shape] at typed
    simp only [TableDecrease.sortRule,shape]
    exact Term.checkSort_complete (embed_sort (x := x) typed)
  · apply SubtermDecrease.preserves_decreasing
    left
    have strat : SubtermDecrease.Stratified (fun _ => 1) (fun _ => 0) (query x rs) := by
      intro r' hr'
      obtain ⟨r,hr,rfl⟩ := source r' hr'
      rcases cls.results r hr with ⟨p,below,path⟩ | ⟨ground,_,small,_⟩
      · right
        left
        exact atPath_proper (by rw [atPath_embed,path r hr rfl]; rfl) below
      · left
        refine ⟨fun _ _ => rfl,by rw [rank_one,rank_one,symbols_embed,symbols_embed]; exact small,?_⟩
        simp [TableDecrease.nonduplicating,closed_embed ground]
    have dec := SubtermDecrease.decreasing (base := fun _ => 1) (fun _ => Nat.one_pos) strat
    have plain : SubtermDecrease.weights (fun _ => 1) (query x rs) (fun _ => 0) = fun _ => 1 := by
      funext h
      simp [SubtermDecrease.weights]
    rwa [plain] at dec
  · intro r' hr'
    obtain ⟨r,hr,rfl⟩ := source r' hr'
    obtain ⟨f,xs,shape,kids⟩ := cls.patterns r hr
    have shape' : embed x r.lhs = .free (.inl f) fun i => embed x (xs i) := by rw [shape]; rfl
    unfold ConstructorRows.checkedRow
    rcases cls.results r hr with ⟨p,below,path⟩ | ⟨ground,inert,_,same⟩
    · have row : ConstructorRows.projectionRow (query x rs) ⟨embed x r.lhs,embed x r.rhs⟩ = true := by
        apply (ConstructorRows.projectionRow_iff _ _ hr').mpr
        refine ⟨⟨.inl f,_,shape',fun i => inert_embed (kids i)⟩,p,below,fun q' hq' at_head => ?_⟩
        obtain ⟨q,hq,rfl⟩ := source q' hq'
        rw [atPath_embed,path q hq (same_head at_head)]
        rfl
      simp [row]
    · have row : ConstructorRows.groundRow (query x rs) fuel ⟨embed x r.lhs,embed x r.rhs⟩ = true := by
        apply ConstructorRows.groundRow_of_constant
        · change ConstructorRows.Pattern (query x rs) (embed x r.lhs)
          rw [shape']
          exact fun i => inert_embed (kids i)
        · simp [closed_embed ground]
        · exact inert_embed inert
        · intro q' hq' at_head
          obtain ⟨q,hq,rfl⟩ := source q' hq'
          change embed x q.rhs = embed x r.rhs
          rw [same q hq (same_head at_head)]
      simp [row]

end Tamarin.SubtermTable
