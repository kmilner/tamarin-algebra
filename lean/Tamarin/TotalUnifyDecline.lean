import Tamarin.TotalInputBounds
import Tamarin.UnifierDensity

/-! The listing entry point declines a decoded query only when an answer of
its family leaves the 64-bit identifiers. The unifier names the variables it
adds by consecutive identifiers from the fresh bound of the query, so such an
answer adds at least `2^64 - bound` distinct variables. -/
namespace Tamarin.TotalUnifyWire.Packet
variable {d : Dictionary}

/-- With machine-word arities, a term whose variables fit is written in full. -/
theorem fits_of_variables (width : ∀ f, d.sig.arity f < UInt64.size) (t : Term d.sig)
    (small : ∀ w, t.Occurs w → w.id < UInt64.size) : FieldsFit t := by
  induction t with
  | var v => exact small v rfl
  | atom => trivial
  | free f xs ih => exact ⟨width f, fun i => ih i fun w hw => small w ⟨i, hw⟩⟩
  | comm f a b ia ib | ac f a b ia ib =>
    exact ⟨ia fun w hw => small w (.inl hw), ib fun w hw => small w (.inr hw)⟩

theorem correct : Correct run where
  malformed := fun ds ns es h => by simp [run,h]
  valid := by
    intro ds ns es d p hi
    let answers := family p
    have solved : (Outcome.complete answers).CorrectIn p [] := family_correct p
    refine ⟨answers,solved,?_⟩
    cases hw : pack p answers with
    | some wire =>
      have eq : run ds ns es = wire := by simp only [run,hi]; change (pack p answers).getD _ = _; rw [hw]; rfl
      exact .inl (eq ▸ pack_decodes _ _ _ hw)
    | none =>
      have eq : run ds ns es = #[#[0]] := by simp only [run,hi]; change (pack p answers).getD _ = _; rw [hw]; rfl
      refine .inr ⟨eq,?_⟩
      have inputs := input_fieldsFit hi
      have width : ∀ f, d.sig.arity f < UInt64.size := by
        simp only [input,Option.bind_eq_bind,Option.bind_eq_some_iff] at hi
        obtain ⟨⟨_,terms⟩,hd,problem,hp,eq⟩ := hi
        cases eq
        exact graph_widths hd
      have query (v : Variable) (hv : p.Occurs v) : v.id < UInt64.size := by
        obtain ⟨e,he,occ⟩ := hv
        exact occ.elim (fun h => var_fits _ _ h (inputs e he).1) (fun h => var_fits _ _ h (inputs e he).2)
      -- Some image has a variable whose identifier does not fit.
      have large : ∃ σ ∈ answers, ∃ v, p.Occurs v ∧ ∃ w, (σ.image v).Occurs w ∧ UInt64.size ≤ w.id := by
        apply Classical.byContradiction
        intro none
        have fits : Representable p answers := by
          intro σ hσ v hv
          have live := (p.mem_variables v).mp hv
          refine ⟨query v live,fits_of_variables width _ fun w hw => ?_⟩
          apply Classical.byContradiction
          intro big
          exact none ⟨σ,hσ,v,live,w,hw,by omega⟩
        obtain ⟨_,h⟩ := pack_exists _ _ fits
        rw [hw] at h
        cases h
      obtain ⟨σ,hσ,v,live,w,occ,big⟩ := large
      have fresh : UnifierDensity.Fresh p σ w :=
        ⟨fun old => by have := query w old; omega,v,live,occ⟩
      have dense := UnifierDensity.verified_dense p [] σ (family_subset p σ hσ)
      rw [List.append_nil] at dense
      obtain ⟨ws,distinct,many,each⟩ := dense.count fresh big
      exact ⟨σ,hσ,ws,distinct,by omega,each⟩

end Tamarin.TotalUnifyWire.Packet
