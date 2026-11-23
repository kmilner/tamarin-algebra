import Tamarin.VariantCertificate
import Tamarin.TableAmbient
import Tamarin.TableWire

/-! Numeric interface to the variant certificate checker. The packet is a
table packet with observation roots, plus one row per proposed variant. A row
lists node pairs: a variable node followed by the node of its image. A
variable that is not listed keeps itself. Status 1 accepts the family, status
2 rejects it with a reason and a member index, status 3 reports an exhausted
budget, and status 0 denotes a malformed packet. No other reply accepts. -/
namespace Tamarin.VariantCheckWire
open TotalUnifyWire Rewriting MaudeOperations

def bindings {s : Signature} (p : Problem s) : Option (List (Variable × Term s)) :=
  p.mapM fun e =>
    match e.lhs with
    | .var v => if e.rhs.checkSort v.sort then some (v,e.rhs) else none
    | _ => none

theorem bindings_sorted {s : Signature} {p : Problem s} {bs : List (Variable × Term s)}
    (h : bindings p = some bs) : ∀ v t, (v,t) ∈ bs → HasSort t v.sort := by
  intro v t member
  obtain ⟨e,_,made⟩ := VariantCertificate.mapM_some_source _ h (v,t) member
  split at made
  · split at made
    · next ok =>
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj made)
      exact Term.checkSort_sound _ _ ok
    · contradiction
  · contradiction

/-- The substitution of one proposed variant. Every listed image must have
the sort of its variable. The first binding of a repeated variable is used. -/
def assign {s : Signature} (p : Problem s) : Option (Substitution s) :=
  match h : bindings p with
  | none => none
  | some bs => some (Substitution.fromBindings bs (bindings_sorted h))

def input (decls : Array UInt64) (nodes : Array (Array UInt64)) (pairs observed : Array UInt64)
    (family : Array (Array UInt64)) :
    Option ((d : Dictionary) × List (Equation d.sig) × List (Term d.sig) × List (Substitution d.sig)) := do
  let ⟨d,ts⟩ ← graph decls nodes
  let rules ← equations ts pairs.toList
  let terms ← observed.toList.mapM fun id => ts[id.toNat]?
  let members ← family.toList.mapM fun row => (equations ts row.toList).bind assign
  return ⟨d,rules,terms,members⟩

/-- The table and the observations are those of the plain table packet. -/
theorem input_table {ds ns es roots family d rs q members}
    (decoded : input ds ns es roots family = some ⟨d,rs,q,members⟩) :
    TableWire.input ds ns es roots = some ⟨d,rs,q⟩ := by
  unfold input at decoded
  unfold TableWire.input
  cases graph : TotalUnifyWire.graph ds ns with
  | none => simp [graph] at decoded
  | some graphPair =>
    obtain ⟨dict,terms⟩ := graphPair
    cases eqs : TotalUnifyWire.equations terms es.toList with
    | none => simp [graph,eqs] at decoded
    | some rules =>
      cases obs : roots.toList.mapM (fun (i : UInt64) => terms[i.toNat]?) with
      | none => simp [graph,eqs,obs] at decoded
      | some qs =>
        cases fam : family.toList.mapM (fun row => (equations terms row.toList).bind assign) with
        | none => simp [graph,eqs,obs,fam] at decoded
        | some ms =>
          simp [graph,eqs,obs,fam] at decoded
          obtain ⟨rfl,h⟩ := decoded
          cases eq_of_heq h
          simp [eqs,obs]

def reply : VariantCertificate.Verdict → Array (Array UInt64)
  | .accepted => #[#[1]]
  | .rejected reason index => #[#[2,UInt64.ofNat reason,UInt64.ofNat index]]
  | .exhausted => #[#[3]]

theorem reply_accepted {v : VariantCertificate.Verdict} (h : reply v = #[#[1]]) : v = .accepted := by
  cases v with
  | accepted => rfl
  | rejected reason index => simp [reply] at h
  | exhausted => simp [reply] at h

def run (ds : Array UInt64) (ns : Array (Array UInt64)) (rules roots : Array UInt64)
    (family : Array (Array UInt64)) (fuel work : UInt64) : Array (Array UInt64) :=
  match input ds ns rules roots family with
  | none => #[#[0]]
  | some ⟨_,rs,q,members⟩ =>
    reply (VariantCertificate.check (TableAmbient.liftRules rs) (q.map TableAmbient.liftTerm)
      (members.map (SignatureExtension.liftSubst TableAmbient.atoms)) fuel.toNat work.toNat)

abbrev Kernel := Array UInt64 → Array (Array UInt64) → Array UInt64 → Array UInt64 →
  Array (Array UInt64) → UInt64 → UInt64 → Array (Array UInt64)

/-- Only status 1 accepts. On a canonical presentation of the decoded table an
accepted family is a complete set of variants of the decoded observations over
all ambient names, and its members are the proposed substitutions. -/
structure Correct (kernel : Kernel) : Prop where
  malformed : ∀ ds ns es roots family fuel work, input ds ns es roots family = none →
    kernel ds ns es roots family fuel work = #[#[0]]
  status : ∀ ds ns es roots family fuel work d rs q members,
    input ds ns es roots family = some ⟨d,rs,q,members⟩ →
    kernel ds ns es roots family fuel work = #[#[1]] ∨
      (∃ reason index, kernel ds ns es roots family fuel work = #[#[2,reason,index]]) ∨
      kernel ds ns es roots family fuel work = #[#[3]]
  accepted : ∀ ds ns es roots family fuel work d rs q members,
    input ds ns es roots family = some ⟨d,rs,q,members⟩ →
    kernel ds ns es roots family fuel work = #[#[1]] →
    CanonicalPresentation (ruleRoot (TableAmbient.liftRules rs)) →
    ∃ rows, VariantReply (ruleRoot (TableAmbient.liftRules rs)) (q.map TableAmbient.liftTerm) [] rows ∧
      rows.length = members.length ∧
      ∀ pair ∈ members.zip rows, ∀ v, Observed q v →
        pair.2.subst.image v = TableAmbient.liftTerm (pair.1.image v)

theorem correct : Correct run where
  malformed := fun ds ns es roots family fuel work h => by simp [run,h]
  status := by
    intro ds ns es roots family fuel work d rs q members decoded
    simp only [run,decoded]
    cases VariantCertificate.check (TableAmbient.liftRules rs) (q.map TableAmbient.liftTerm)
        (members.map (SignatureExtension.liftSubst TableAmbient.atoms)) fuel.toNat work.toNat with
    | accepted => exact .inl rfl
    | rejected reason index => exact .inr (.inl ⟨_,_,rfl⟩)
    | exhausted => exact .inr (.inr rfl)
  accepted := by
    intro ds ns es roots family fuel work d rs q members decoded ok canonical
    simp only [run,decoded] at ok
    obtain ⟨rows,reply,len,each⟩ := VariantCertificate.accepted_reply canonical (reply_accepted ok)
    refine ⟨rows,reply,by simpa using len,?_⟩
    rintro ⟨σ,a⟩ hpair v hv
    have lifted : Observed (q.map TableAmbient.liftTerm) v := by
      obtain ⟨t,ht,occ⟩ := hv
      exact ⟨_,List.mem_map_of_mem ht,(SignatureExtension.embed_occurs t v).mpr occ⟩
    have paired : (SignatureExtension.liftSubst TableAmbient.atoms σ,a) ∈
        (members.map (SignatureExtension.liftSubst TableAmbient.atoms)).zip rows := by
      rw [List.zip_map_left]
      exact List.mem_map.mpr ⟨(σ,a),hpair,rfl⟩
    exact each _ paired v lifted

end Tamarin.VariantCheckWire
