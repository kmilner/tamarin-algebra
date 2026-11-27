import Tamarin.MaudeUnifyRun

/-!
# From terms to dags and back

Facts about evaluating dags under substitutions and about the dags of terms.
-/
namespace Tamarin.MaudeUnify
open Cancellation


variable {s : Signature}

namespace Dag

theorem fold_subst (f : s.ACSym) (τ : Variable → Term s) (t : Term s) (ts : List (Term s)) :
    (ACRepresentation.fold f t ts).subst τ = ACRepresentation.fold f (t.subst τ) (ts.map (·.subst τ)) := by
  induction ts generalizing t with
  | nil => rfl
  | cons u us ih => simp only [ACRepresentation.fold, Term.subst, List.map_cons, ih]

theorem product_subst (f : s.ACSym) (τ : Variable → Term s) {ts : List (Term s)} (h : ts ≠ []) :
    (product f ts).subst τ = product f (ts.map (·.subst τ)) := by
  obtain ⟨t, ts, rfl⟩ := List.exists_cons_of_ne_nil h
  exact fold_subst f τ t ts

theorem fold_occurs (f : s.ACSym) {w : Variable} : ∀ (t : Term s) (ts : List (Term s)),
    (ACRepresentation.fold f t ts).Occurs w → ∃ u ∈ t :: ts, u.Occurs w
  | t, [], h => ⟨t, List.mem_cons_self, h⟩
  | t, u :: us, h => by
    rcases h with h | h
    · exact ⟨t, List.mem_cons_self, h⟩
    · obtain ⟨v, hv, o⟩ := fold_occurs f u us h
      exact ⟨v, List.mem_cons_of_mem _ hv, o⟩

theorem product_occurs (f : s.ACSym) {ts : List (Term s)} (h : ts ≠ []) {w : Variable}
    (o : (product f ts).Occurs w) : ∃ u ∈ ts, u.Occurs w := by
  obtain ⟨t, ts, rfl⟩ := List.exists_cons_of_ne_nil h
  exact fold_occurs f t ts o

theorem getD_map_eval (ρ : Nat → Term s) (args : List (Dag s)) (i : Nat) (hi : i < args.length) :
    (args.map (eval ρ)).getD i dflt = eval ρ args[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
  rfl

/-- Substituting into the value of a well-formed dag substitutes into the
values of its slots. -/
theorem eval_subst (τ : Variable → Term s) (ρ : Nat → Term s) (d : Dag s) (hd : d.Wf) :
    (eval ρ d).subst τ = eval (fun i => (ρ i).subst τ) d := by
  induction d using induct' with
  | var i => simp [eval_var]
  | atom a => simp [eval_atom, Term.subst]
  | free f args ih =>
    simp only [Dag.Wf] at hd
    rw [eval_free, eval_free, Term.subst]
    congr 1
    funext i
    have hi : i.val < args.length := by rw [hd.1]; exact i.isLt
    rw [getD_map_eval ρ args i hi, getD_map_eval _ args i hi]
    exact ih _ (List.getElem_mem hi) (hd.2 _ (List.getElem_mem hi))
  | comm f a b ia ib =>
    simp only [Dag.Wf] at hd
    rw [eval_comm, eval_comm, Term.subst, ia hd.1, ib hd.2]
  | ac f args ih =>
    simp only [Dag.Wf] at hd
    have ne : args.map (eval ρ) ≠ [] := by
      intro e; rw [List.map_eq_nil_iff] at e; rw [e] at hd; simp at hd
    rw [eval_ac, eval_ac, product_subst f τ ne, List.map_map]
    congr 1
    apply List.map_congr_left
    intro d hd'
    exact ih d hd' (hd.2 d hd')

/-- A variable of the value of a well-formed dag comes from the value of one of its slots. -/
theorem eval_occurs (ρ : Nat → Term s) (d : Dag s) (hd : d.Wf) {w : Variable} (o : (eval ρ d).Occurs w) :
    ∃ j ∈ d.vars, (ρ j).Occurs w := by
  induction d using induct' with
  | var i => rw [eval_var] at o; exact ⟨i, by simp [vars], o⟩
  | atom a => rw [eval_atom] at o; cases o
  | free f args ih =>
    simp only [Dag.Wf] at hd
    rw [eval_free] at o
    obtain ⟨i, oi⟩ := o
    have hi : i.val < args.length := by rw [hd.1]; exact i.isLt
    simp only at oi
    rw [getD_map_eval ρ args i hi] at oi
    obtain ⟨j, hj, oj⟩ := ih _ (List.getElem_mem hi) (hd.2 _ (List.getElem_mem hi)) oi
    exact ⟨j, by rw [vars_free]; exact List.mem_flatMap.mpr ⟨_, List.getElem_mem hi, hj⟩, oj⟩
  | comm f a b ia ib =>
    simp only [Dag.Wf] at hd
    rw [eval_comm] at o
    rcases o with o | o
    · obtain ⟨j, hj, oj⟩ := ia hd.1 o; exact ⟨j, by simp [vars, hj], oj⟩
    · obtain ⟨j, hj, oj⟩ := ib hd.2 o; exact ⟨j, by simp [vars, hj], oj⟩
  | ac f args ih =>
    simp only [Dag.Wf] at hd
    have ne : args.map (eval ρ) ≠ [] := by
      intro e; rw [List.map_eq_nil_iff] at e; rw [e] at hd; simp at hd
    rw [eval_ac] at o
    obtain ⟨u, hu, ou⟩ := product_occurs f ne o
    obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hu
    obtain ⟨j, hj, oj⟩ := ih d hd' (hd.2 d hd') ou
    exact ⟨j, by rw [vars_ac]; exact List.mem_flatMap.mpr ⟨d, hd', hj⟩, oj⟩

section Fit
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

/-- The dag of a term is well formed and mentions the slots of its variables. -/
theorem ofTerm_fit (r : Ranks s) (sortOf : Nat → Option SortId) (slot : Variable → Nat) (t : Term s) :
    (ofTerm r sortOf slot t).Wf ∧ ∀ j ∈ (ofTerm r sortOf slot t).vars, ∃ v, t.Occurs v ∧ j = slot v := by
  induction t with
  | var v => exact ⟨by simp [ofTerm, Dag.Wf], fun j hj => ⟨v, rfl, by simpa [ofTerm, vars] using hj⟩⟩
  | atom a => exact ⟨by simp [ofTerm, Dag.Wf], fun j hj => by simp [ofTerm, vars] at hj⟩
  | free f xs ih =>
    refine ⟨?_, fun j hj => ?_⟩
    · rw [ofTerm]; simp only [Dag.Wf]
      refine ⟨by simp, fun d hd => ?_⟩
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
      exact (ih i).1
    · rw [ofTerm, vars_free] at hj
      obtain ⟨d, hd, hj⟩ := List.mem_flatMap.mp hj
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
      obtain ⟨v, o, e⟩ := (ih i).2 j hj
      exact ⟨v, ⟨i, o⟩, e⟩
  | comm f a b ia ib =>
    rw [ofTerm]
    refine ⟨wf_mkComm r sortOf f ia.1 ib.1, fun j hj => ?_⟩
    rcases mem_vars_mkComm hj with hj | hj
    · obtain ⟨v, o, e⟩ := ia.2 j hj; exact ⟨v, .inl o, e⟩
    · obtain ⟨v, o, e⟩ := ib.2 j hj; exact ⟨v, .inr o, e⟩
  | ac f a b ia ib =>
    rw [ofTerm]
    refine ⟨wf_normAC r sortOf f (by simp) (fun x hx => ?_), fun j hj => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ia.1
      · exact ib.1
    · obtain ⟨x, hx, hj⟩ := mem_vars_normAC hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · obtain ⟨v, o, e⟩ := ia.2 j hj; exact ⟨v, .inl o, e⟩
      · obtain ⟨v, o, e⟩ := ib.2 j hj; exact ⟨v, .inr o, e⟩

end Fit

end Dag

end Tamarin.MaudeUnify
