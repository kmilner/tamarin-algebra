import Tamarin.ConstructorPresentation
import Tamarin.DHConstructorExtension
import Tamarin.DHWireSymbols
import Tamarin.SubtermDecrease
import Tamarin.XorPresentation
import Tamarin.XorTableWire
import Tamarin.GroupTable
import Tamarin.BilinearTableWire
import Tamarin.UserAC
import Tamarin.SubtermTable

/-! Certify the decoded table in its full ambient signature. Symbol and variable
IDs may vary with the query. Matching a characteristic rule only proposes an
interpretation; the certificate checks the complete oriented rule table. -/
namespace Tamarin.CertifiedTable
open TotalUnifyWire Rewriting DHPeer MaudeOperations
variable {d : Dictionary}

private structure Tower (s : Signature) where
  pow : s.FreeSym
  mul : s.ACSym
  x : Variable
  y : Variable
  z : Variable

private def tower {s : Signature} [DecidableEq s.FreeSym] (r : Equation s) : Option (Tower s) := do
  let .free pow args := r.lhs | none
  let [.free inner pair,.var z] := List.ofFn args | none
  let [.var x,.var y] := List.ofFn pair | none
  let .free outer result := r.rhs | none
  let [.var base,.ac mul _ _] := List.ofFn result | none
  guard (inner == pow && outer == pow && base == x)
  return ⟨pow,mul,x,y,z⟩

private def unit {s : Signature} [DecidableEq s.FreeSym] (pow : s.FreeSym) (r : Equation s) : Option s.FreeSym := do
  let .free f args := r.lhs | none
  let [.var x,.free one _] := List.ofFn args | none
  let .var v := r.rhs | none
  guard (f == pow && x == v && s.arity one == 0)
  return one

private def neutral {s : Signature} [DecidableEq s.FreeSym] (pow : s.FreeSym) (r : Equation s) : Option s.FreeSym := do
  let .free f args := r.lhs | none
  let [.free n _,.var _] := List.ofFn args | none
  let .free rhs _ := r.rhs | none
  guard (f == pow && n == rhs && s.arity n == 0)
  return n

private def inverse {s : Signature} [DecidableEq s.FreeSym] (r : Equation s) : Option s.FreeSym := do
  let .free f args := r.lhs | none
  let [.free g xs] := List.ofFn args | none
  let [.var x] := List.ofFn xs | none
  let .var rhs := r.rhs | none
  guard (f == g && x == rhs)
  return f

private def detect (rs : Problem d.sig) : Option (Symbols d.sig × (Fin 3 → Variable)) := do
  let t ← rs.findSome? (tower (s := d.sig))
  let o ← rs.findSome? (unit t.pow)
  let n ← rs.findSome? (neutral t.pow)
  let i ← rs.findSome? (inverse (s := d.sig))
  let decl ← DHWire.readSymbols t.pow i o n t.mul
  return (decl,fun k => match k with | 0 => t.x | 1 => t.y | 2 => t.z)

private def components (xs : List (XorTable.Schema d.sig)) (units : List (UserAC.Schema d.sig)) :
    List (PresentationComponents.Independent (TableAmbient.sig d)) :=
  (xs.map fun x =>
    let a := XorTable.liftSchema x
    ⟨GroupPresentationParts.xorPart a,fun inv apps => GroupPresentationParts.xorLocal a inv apps⟩) ++
  units.map fun u =>
    let a := UserAC.liftSchema u
    ⟨a.part,a.localProof⟩

private def dh (rs : Problem d.sig) (fuel : Nat) (s : Symbols d.sig)
    (ks : Fin 3 → Variable) (xs : List (XorTable.Schema d.sig))
    (parts : List (PresentationComponents.Independent (TableAmbient.sig d))) : Bool :=
  let ambient := TableAmbient.liftRules rs
  let dh := DHWire.liftSymbols s
  let extensions := parts.map (GroupTable.independent dh) ++
    (BilinearTable.detect s rs).map (fun b => GroupTable.bilinear dh (BilinearTable.liftSchema b))
  let base : Head (TableAmbient.sig d) → Nat
    | .ac (.inl f) => if xs.any (fun a => a.f == f) then 2 else 1
    | h => ExactTable.weight h
  let weights := fun (whole : Problem (TableAmbient.sig d)) =>
    let inferred := SubtermDecrease.proposeWeight (fun _ => 1) whole
    if SymbolWeight.decreasing inferred whole then inferred else SubtermDecrease.proposeWeight base whole
  decide (∀ i, (ks i).sort = .msg) && decide (∀ i j, ks i = ks j → i = j) &&
    GroupTable.accepts dh ks extensions weights fuel ambient

private def withoutDH (rs : Problem (TableAmbient.sig d)) (fuel : Nat)
    (parts : List (PresentationComponents.Independent (TableAmbient.sig d))) : Bool :=
  PresentationComponents.accepts (parts.map PresentationComponents.Independent.toPart)
    (SubtermDecrease.proposeWeight (fun _ => 1)) fuel rs

/-! The compiled certifier runs `dh` and `withoutDH` as the definitions below:
each proposed weighting is chosen once, as data (`SubtermDecrease.propose`), and
every weight lookup reads that choice. -/

private def dhProposed (rs : Problem d.sig) (fuel : Nat) (s : Symbols d.sig)
    (ks : Fin 3 → Variable) (xs : List (XorTable.Schema d.sig))
    (parts : List (PresentationComponents.Independent (TableAmbient.sig d))) : Bool :=
  let ambient := TableAmbient.liftRules rs
  let dh := DHWire.liftSymbols s
  let extensions := parts.map (GroupTable.independent dh) ++
    (BilinearTable.detect s rs).map (fun b => GroupTable.bilinear dh (BilinearTable.liftSchema b))
  let base : Head (TableAmbient.sig d) → Nat
    | .ac (.inl f) => if xs.any (fun a => a.f == f) then 2 else 1
    | h => ExactTable.weight h
  let one : Head (TableAmbient.sig d) → Nat := fun _ => 1
  let whole := PresentationComponents.table
    (GroupPresentationParts.dhPart dh ks :: extensions.map GroupTable.Extension.toPart) ambient
  let inferred := (SubtermDecrease.propose one whole).weight one
  let weight := if SymbolWeight.decreasing inferred whole then inferred
    else (SubtermDecrease.propose base whole).weight base
  decide (∀ i, (ks i).sort = .msg) && decide (∀ i j, ks i = ks j → i = j) &&
    GroupTable.accepts dh ks extensions (fun _ => weight) fuel ambient

@[csimp] private theorem dh_eq_proposed : @dh = @dhProposed := by
  funext d rs fuel s ks xs parts
  simp only [dh,dhProposed,GroupTable.accepts]
  conv => lhs; rw [PresentationComponents.accepts_table_weights (s := TableAmbient.sig d)]
  simp only [SubtermDecrease.propose_weight]

private def withoutDHProposed (rs : Problem (TableAmbient.sig d)) (fuel : Nat)
    (parts : List (PresentationComponents.Independent (TableAmbient.sig d))) : Bool :=
  let ps := parts.map PresentationComponents.Independent.toPart
  let one : Head (TableAmbient.sig d) → Nat := fun _ => 1
  let weight := (SubtermDecrease.propose one (PresentationComponents.table ps rs)).weight one
  PresentationComponents.accepts ps (fun _ => weight) fuel rs

@[csimp] private theorem withoutDH_eq_proposed : @withoutDH = @withoutDHProposed := by
  funext d rs fuel parts
  simp only [withoutDH,withoutDHProposed]
  conv => lhs; rw [PresentationComponents.accepts_table_weights (s := TableAmbient.sig d)]
  simp only [SubtermDecrease.propose_weight]

def admits (rs : Problem d.sig) (fuel : Nat) : Bool :=
  let ambient := TableAmbient.liftRules rs
  if rs.any (fun r => match r.lhs with | .ac .. => true | _ => false) then
    let xs := XorTable.candidates rs
    let parts := components xs (UserAC.candidates rs)
    (detect rs).any (fun (s,ks) => dh rs fuel s ks xs parts) || withoutDH ambient fuel parts
  else withoutDH ambient fuel []

theorem admits_sound {rs : Problem d.sig} {fuel} (ok : admits rs fuel) :
    ReferenceReduction.Bound (TableAmbient.liftRules rs) ∧ CanonicalPresentation (ruleRoot (TableAmbient.liftRules rs)) ∧
      FiniteVariantProperty (ruleRoot (TableAmbient.liftRules rs)) := by
  unfold admits at ok
  dsimp only at ok
  split at ok
  · rcases Bool.or_eq_true_iff.mp ok with dhOK | otherOK
    · obtain ⟨⟨s,ks⟩,_,found⟩ := (Option.any_eq_true _ _).mp dhOK
      simp only [dh,Bool.and_eq_true,decide_eq_true_eq] at found
      obtain ⟨⟨typed,distinct⟩,accepted⟩ := found
      exact GroupTable.accepts_sound typed distinct accepted
    · exact PresentationComponents.independent_complete otherOK
  · exact PresentationComponents.independent_complete ok

/-- The certifier accepts every table of constructor-pattern rules whose
results are subterms or constants, at every depth. -/
theorem admits_subterm {rs : Problem d.sig} (cls : SubtermTable.Presentation rs) (fuel : Nat) :
    admits rs fuel = true := by
  have plain : rs.any (fun r => match r.lhs with | .ac .. => true | _ => false) = false := by
    apply List.any_eq_false.mpr
    intro r hr
    obtain ⟨f,xs,shape,_⟩ := cls.patterns r hr
    rw [shape]
    simp
  unfold admits
  simp only [plain]
  exact SubtermTable.accepted cls fuel

/-! The budget is spent only on rows that no component claims. A table that
`admits` accepts at budget zero through components that claim each of its rows
is therefore accepted at every budget. -/

private def claimsAll {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym]
    [DecidableEq s.ACSym] [DecidableEq s.Atom] (ps : List (PresentationComponents.Part s))
    (rs : Problem s) : Bool :=
  (PresentationComponents.table ps rs).all fun r => PresentationComponents.claimed ps (ConstructorVariants.head r.lhs)

private theorem accepts_budget {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym]
    [DecidableEq s.ACSym] [DecidableEq s.Atom] {ps : List (PresentationComponents.Part s)} {w a rs}
    (claims : claimsAll ps rs) (ok : PresentationComponents.accepts ps w a rs) (b : Nat) :
    PresentationComponents.accepts ps w b rs := by
  have owned := List.all_eq_true.mp claims
  have every (check : Equation s → Bool) : ((PresentationComponents.table ps rs).all fun r =>
      PresentationComponents.claimed ps (ConstructorVariants.head r.lhs) || check r) = true :=
    List.all_eq_true.mpr fun r hr => by simp [owned r hr]
  unfold PresentationComponents.accepts at ok ⊢
  simp only [Bool.and_eq_true] at ok ⊢
  exact ⟨ok.1,every _⟩

private def dhBudgetFree (rs : Problem d.sig) (s : Symbols d.sig)
    (ks : Fin 3 → Variable) (parts : List (PresentationComponents.Independent (TableAmbient.sig d))) :
    Bool :=
  let ambient := TableAmbient.liftRules rs
  let dh := DHWire.liftSymbols s
  let extensions := parts.map (GroupTable.independent dh) ++
    (BilinearTable.detect s rs).map (fun b => GroupTable.bilinear dh (BilinearTable.liftSchema b))
  claimsAll (GroupPresentationParts.dhPart dh ks :: extensions.map GroupTable.Extension.toPart) ambient

private theorem dh_budget {rs : Problem d.sig} {s ks xs parts}
    (free : dhBudgetFree rs s ks parts) (ok : dh rs 0 s ks xs parts) (fuel : Nat) :
    dh rs fuel s ks xs parts := by
  simp only [dh,Bool.and_eq_true] at ok ⊢
  exact ⟨ok.1,accepts_budget free ok.2 fuel⟩

/-- Acceptance at budget zero by components that claim every row they check. -/
def budgetFree (rs : Problem d.sig) : Bool :=
  let ambient := TableAmbient.liftRules rs
  if rs.any (fun r => match r.lhs with | .ac .. => true | _ => false) then
    let xs := XorTable.candidates rs
    let parts := components xs (UserAC.candidates rs)
    (detect rs).any (fun (s,ks) => dh rs 0 s ks xs parts && dhBudgetFree rs s ks parts) ||
      (withoutDH ambient 0 parts &&
        claimsAll (parts.map PresentationComponents.Independent.toPart) ambient)
  else withoutDH ambient 0 [] && claimsAll [] ambient

theorem admits_of_budgetFree {rs : Problem d.sig} (ok : budgetFree rs) (fuel : Nat) :
    admits rs fuel = true := by
  unfold budgetFree at ok
  unfold admits
  split at ok
  · rename_i active
    simp only [active,ite_true]
    rcases Bool.or_eq_true_iff.mp ok with dhOK | otherOK
    · obtain ⟨⟨s,ks⟩,found,hit⟩ := (Option.any_eq_true _ _).mp dhOK
      obtain ⟨zero,free⟩ := Bool.and_eq_true_iff.mp hit
      exact Bool.or_eq_true_iff.mpr (.inl ((Option.any_eq_true _ _).mpr
        ⟨⟨s,ks⟩,found,dh_budget free zero fuel⟩))
    · obtain ⟨zero,free⟩ := Bool.and_eq_true_iff.mp otherOK
      exact Bool.or_eq_true_iff.mpr (.inr (accepts_budget free zero fuel))
  · rename_i plain
    simp only [plain]
    obtain ⟨zero,free⟩ := Bool.and_eq_true_iff.mp ok
    exact accepts_budget free zero fuel

end Tamarin.CertifiedTable
