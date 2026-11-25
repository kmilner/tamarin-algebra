import Tamarin.SortClash
import Tamarin.VariablePermutation
import Tamarin.VariablesFast
import Tamarin.Buckets

/-! Maude solves the underlying component problem before assigning sorts to
the free variables of a solved form. A schematic image here is raw syntax.
Only the final arm is a sort-respecting substitution. -/
namespace Tamarin.UnifierSorts
variable {s : Signature}

abbrev Template (s : Signature) := Variable → Term s

/-- Raw component solutions may have unsorted parameters. One instantiation
must account for every variable observed in the input. -/
structure CompleteTemplates (p : Problem s) (rows : List (Template s)) : Prop where
  sound : ∀ θ ∈ rows, ∀ e ∈ p, EquivB (e.lhs.subst θ) (e.rhs.subst θ)
  covers : ∀ ρ : Substitution s, p.Solves ρ →
    ∃ θ ∈ rows, ∃ μ : Variable → Term s,
      ∀ v, p.Occurs v → EquivB (ρ.image v) ((θ v).subst μ)

/-- The variables of a problem, each once. -/
private def keys (p : Problem s) : List Variable := Buckets.dedup Variable.id p.variables

private theorem mem_keys {p : Problem s} {v : Variable} : v ∈ keys p ↔ v ∈ p.variables := by
  rw [keys, Buckets.dedup_eq]
  exact List.mem_eraseDups

private def slots (p : Problem s) (θ : Template s) :=
  ((keys p).flatMap (fun v => (θ v).variables)).eraseDups

private theorem slot_mem {p : Problem s} {θ : Template s} {v w}
    (live : p.Occurs v) (seen : (θ v).Occurs w) : w ∈ slots p θ := by
  exact List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨v,mem_keys.mpr ((p.mem_variables _).mpr live),
    (Term.mem_variables ..).mpr seen⟩)

private def name (vs : List Variable) (base : Nat) (g : Variable → SortId) (w : Variable) : Variable :=
  ⟨base + vs.idxOf w, g w⟩

private theorem name_injective {vs : List Variable} {base g} {v w : Variable} (hv : v ∈ vs)
    (hw : w ∈ vs) (h : name vs base g v = name vs base g w) : v = w := by
  have e := Nat.add_left_cancel (congrArg Variable.id h)
  have left := List.getElem_idxOf (List.idxOf_lt_length_of_mem hv)
  have right := List.getElem_idxOf (List.idxOf_lt_length_of_mem hw)
  grind

private def images (θ : Template s) (label : Variable → Variable) (v : Variable) :=
  (θ v).subst (fun w => .var (label w))

private def read (p : Problem s) (img : Variable → Term s)
    (sorted : ∀ v ∈ p.variables, (img v).checkSort v.sort = true) : Substitution s where
  image v := if v ∈ p.variables then img v else .var v
  support := p.variables
  outside v hv := ite_eq_right hv
  sorted v := by
    split
    · next h => exact Term.checkSort_sound _ _ (sorted v h)
    · exact .var _

/-- `read` with the variable list computed once, not on every image lookup. -/
private def readShared (p : Problem s) (img : Variable → Term s)
    (sorted : ∀ v ∈ p.variables, (img v).checkSort v.sort = true) : Substitution s :=
  let vars := p.variables
  { image := fun v => if v ∈ vars then img v else .var v
    support := vars
    outside := fun _ hv => ite_eq_right hv
    sorted := (read p img sorted).sorted }

@[csimp] private theorem read_eq_shared : @read = @readShared := rfl

private def arm (p : Problem s) (θ : Template s) (base : Nat) (g : Variable → SortId) :
    Option (Substitution s) :=
  let img := images θ (name (slots p θ) base g)
  if ok : (keys p).all (fun v => (img v).checkSort v.sort) then
    some (read p img (fun v hv => List.all_eq_true.mp ok v (mem_keys.mpr hv)))
  else none

/-- The sort required at each variable occurrence of a term checked at `k`. -/
private def demands : Term s → SortId → List (Variable × SortId)
  | .var v, k => [(v,k)]
  | .atom _, _ => []
  | .free f xs, _ => (List.finRange (s.arity f)).flatMap fun i => demands (xs i) (s.inputSort f i)
  | .comm f a b, _ => demands a (s.cSort f) ++ demands b (s.cSort f)
  | .ac f a b, _ => demands a (s.acSort f) ++ demands b (s.acSort f)

private theorem demands_of_check (t : Term s) (label : Variable → Variable) (k : SortId)
    (typed : (t.subst (fun w => .var (label w))).checkSort k = true) :
    ∀ d ∈ demands t k, Subsort (label d.1).sort d.2 := by
  induction t generalizing k with
  | var v =>
    intro d hd
    obtain rfl := List.mem_singleton.mp hd
    exact (Subsort.check_iff ..).mp typed
  | atom => intro d hd; cases hd
  | free f xs ih =>
    simp only [Term.subst, Term.checkSort, Bool.and_eq_true, List.all_eq_true] at typed
    intro d hd
    obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hd
    exact ih i _ (typed.2 i (List.mem_finRange i)) d hi
  | ac f a b ia ib | comm f a b ia ib =>
    simp only [Term.subst, Term.checkSort, Bool.and_eq_true] at typed
    intro d hd
    rcases List.mem_append.mp hd with h | h
    · exact ia _ typed.1.2 d h
    · exact ib _ typed.2 d h

/-- Rigid positions do not depend on the labels, so any labelling that meets
every demand passes the check that some labelling passed. -/
private theorem check_of_demands (t : Term s) (old label : Variable → Variable) (k : SortId)
    (typed : (t.subst (fun w => .var (old w))).checkSort k = true)
    (fits : ∀ d ∈ demands t k, Subsort (label d.1).sort d.2) :
    (t.subst (fun w => .var (label w))).checkSort k = true := by
  induction t generalizing k with
  | var v => exact (Subsort.check_iff ..).mpr (fits (v,k) (List.mem_singleton_self _))
  | atom => exact typed
  | free f xs ih =>
    simp only [Term.subst, Term.checkSort, Bool.and_eq_true, List.all_eq_true] at typed ⊢
    exact ⟨typed.1, fun i hi => ih i _ (typed.2 i hi)
      (fun d hd => fits d (List.mem_flatMap.mpr ⟨i,List.mem_finRange i,hd⟩))⟩
  | ac f a b ia ib | comm f a b ia ib =>
    simp only [Term.subst, Term.checkSort, Bool.and_eq_true] at typed ⊢
    exact ⟨⟨typed.1.1, ia _ typed.1.2 (fun d hd => fits d (List.mem_append_left _ hd))⟩,
      ib _ typed.2 (fun d hd => fits d (List.mem_append_right _ hd))⟩

private theorem demand_of_occurs (t : Term s) (k : SortId) (w : Variable) (h : t.Occurs w) :
    ∃ j, (w,j) ∈ demands t k := by
  induction t generalizing k with
  | var v => obtain rfl := h; exact ⟨k, List.mem_singleton_self _⟩
  | atom => exact nomatch h
  | free f xs ih =>
    obtain ⟨i,hi⟩ := h
    obtain ⟨j,hj⟩ := ih i _ hi
    exact ⟨j, List.mem_flatMap.mpr ⟨i, List.mem_finRange i, hj⟩⟩
  | ac f a b ia ib | comm f a b ia ib =>
    rcases h with h | h
    · obtain ⟨j,hj⟩ := ia _ h; exact ⟨j, List.mem_append_left _ hj⟩
    · obtain ⟨j,hj⟩ := ib _ h; exact ⟨j, List.mem_append_right _ hj⟩

/-- Greatest lower bound of two sorts, when one exists. -/
private def meet (a b : SortId) : Option SortId :=
  if Subsort.check a b then some a else if Subsort.check b a then some b else none

private theorem meet_le {a b c : SortId} (h : meet a b = some c) : Subsort c a ∧ Subsort c b := by
  have : Subsort.check c a = true ∧ Subsort.check c b = true := by
    revert h; cases a <;> cases b <;> cases c <;> decide
  exact ⟨(Subsort.check_iff ..).mp this.1, (Subsort.check_iff ..).mp this.2⟩

private theorem meet_ge {x a b : SortId} (ha : Subsort x a) (hb : Subsort x b) :
    ∃ c, meet a b = some c ∧ Subsort x c := by
  have ha := (Subsort.check_iff ..).mpr ha
  have hb := (Subsort.check_iff ..).mpr hb
  have : (meet a b).any (Subsort.check x) = true := by
    revert ha hb; cases x <;> cases a <;> cases b <;> decide
  cases h : meet a b with
  | none => simp [h] at this
  | some c => exact ⟨c, rfl, (Subsort.check_iff ..).mp (by simpa [h] using this)⟩

private def glb (acc : SortId) : List SortId → Option SortId
  | [] => some acc
  | k :: ks => match meet acc k with
    | some a => glb a ks
    | none => none

private theorem glb_le {acc : SortId} {ks : List SortId} {c : SortId} (h : glb acc ks = some c) :
    Subsort c acc ∧ ∀ k ∈ ks, Subsort c k := by
  induction ks generalizing acc with
  | nil => obtain rfl := Option.some.inj h; exact ⟨.refl _, nofun⟩
  | cons k ks ih =>
    simp only [glb] at h
    split at h
    · next a hm =>
      have ⟨ca, rest⟩ := ih h
      have ⟨aacc, ak⟩ := meet_le hm
      refine ⟨ca.trans aacc, fun j hj => ?_⟩
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ca.trans ak
      · exact rest j hj
    · contradiction

private theorem glb_ge {x acc : SortId} {ks : List SortId} (ha : Subsort x acc)
    (hk : ∀ k ∈ ks, Subsort x k) : ∃ c, glb acc ks = some c ∧ Subsort x c := by
  induction ks generalizing acc with
  | nil => exact ⟨acc, rfl, ha⟩
  | cons k ks ih =>
    obtain ⟨a, hm, xa⟩ := meet_ge ha (hk k List.mem_cons_self)
    obtain ⟨c, hc, xc⟩ := ih xa (fun j hj => hk j (List.mem_cons_of_mem _ hj))
    exact ⟨c, by simp only [glb, hm]; exact hc, xc⟩

private def pick : List SortId → SortId
  | [] => .msg
  | k :: ks => (glb k ks).getD .msg

private theorem pick_spec {x j : SortId} {ks : List SortId} (mem : j ∈ ks)
    (below : ∀ k ∈ ks, Subsort x k) : Subsort x (pick ks) ∧ Subsort (pick ks) j := by
  cases ks with
  | nil => cases mem
  | cons k ks =>
    obtain ⟨c, hc, xc⟩ := glb_ge (below k List.mem_cons_self)
      (fun i hi => below i (List.mem_cons_of_mem _ hi))
    have ⟨ck, rest⟩ := glb_le hc
    simp only [pick, hc, Option.getD_some]
    refine ⟨xc, ?_⟩
    rcases List.mem_cons.mp mem with rfl | hj
    · exact ck
    · exact rest j hj

/-- The most general sort a slot may take: the meet of the sorts demanded at
its occurrences. Every admissible sort for the slot lies below it. -/
private def principal (ds : List (Variable × SortId)) (w : Variable) : SortId :=
  pick ((ds.filter (·.1 == w)).map (·.2))

private theorem principal_spec (ds : List (Variable × SortId)) (g : Variable → SortId)
    (below : ∀ d ∈ ds, Subsort (g d.1) d.2) :
    ∀ d ∈ ds, Subsort (g d.1) (principal ds d.1) ∧ Subsort (principal ds d.1) d.2 := by
  intro d hd
  apply pick_spec
  · exact List.mem_map.mpr ⟨d, List.mem_filter.mpr ⟨hd, by simp⟩, rfl⟩
  · intro k hk
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
    obtain ⟨he, same⟩ := List.mem_filter.mp he
    have eq : e.1 = d.1 := by simpa using same
    exact eq ▸ below e he

private def assoc : List (Variable × SortId) → Variable → SortId
  | [], _ => .msg
  | (v,k) :: rest, w => if w = v then k else assoc rest w

private theorem assoc_map (f : Variable → SortId) (vs : List Variable) {w : Variable} (hw : w ∈ vs) :
    assoc (vs.map fun v => (v, f v)) w = f w := by
  induction vs with
  | nil => cases hw
  | cons v vs ih =>
    simp only [List.map_cons, assoc]
    split
    · next h => rw [h]
    · next h => exact ih ((List.mem_cons.mp hw).resolve_left h)

private def demandList (p : Problem s) (θ : Template s) :=
  (keys p).flatMap fun v => demands (θ v) v.sort

/-- The principal sort of every slot, computed once per template. -/
private def sortTable (p : Problem s) (θ : Template s) : List (Variable × SortId) :=
  let ds := demandList p θ
  ((ds.map (·.1)).eraseDups).map fun w => (w, principal ds w)

private theorem sortTable_eq {p : Problem s} {θ : Template s} {d : Variable × SortId}
    (hd : d ∈ demandList p θ) :
    assoc (sortTable p θ) d.1 = principal (demandList p θ) d.1 :=
  assoc_map _ _ (List.mem_eraseDups.mpr (List.mem_map.mpr ⟨d, hd, rfl⟩))

/-- Sorts only narrow under instantiation, so the single arm that gives every
slot its principal sort covers every admissible sort assignment. -/
private def perTemplate (p : Problem s) (θ : Template s) (avoid : List Variable) :=
  (arm p θ (VariablePermutation.freshBound (p.variables ++ avoid)) (assoc (sortTable p θ))).toList

private def solveRows (p : Problem s) (rows : List (Template s)) (avoid : List Variable) :=
  rows.flatMap (fun θ => perTemplate p θ avoid)

/-- A template given by its images of the problem variables. -/
private def tabulate : List (Variable × Term s) → Template s
  | [], v => .var v
  | (w,t) :: rest, v => if v = w then t else tabulate rest v

private theorem tabulate_map (θ : Template s) (vs : List Variable) {v : Variable} (hv : v ∈ vs) :
    tabulate (vs.map fun w => (w, θ w)) v = θ v := by
  induction vs with
  | nil => cases hv
  | cons w ws ih =>
    simp only [List.map_cons, tabulate]
    split
    · next h => rw [h]
    · next h => exact ih ((List.mem_cons.mp hv).resolve_left h)

private theorem tabulate_outside (table : List (Variable × Term s)) (v : Variable)
    (h : ∀ e ∈ table, e.1 ≠ v) : tabulate table v = .var v := by
  induction table with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨w,t⟩ := e
    simp only [tabulate]
    split
    · next same => exact absurd same.symm (h (w,t) List.mem_cons_self)
    · exact ih fun e he => h e (List.mem_cons_of_mem _ he)

private theorem tabulate_sorted (table : List (Variable × Term s))
    (h : ∀ e ∈ table, HasSort e.2 e.1.sort) (v : Variable) : HasSort (tabulate table v) v.sort := by
  induction table with
  | nil => exact .var _
  | cons e rest ih =>
    obtain ⟨w,t⟩ := e
    simp only [tabulate]
    split
    · next same => rw [same]; exact h (w,t) List.mem_cons_self
    · exact ih fun e he => h e (List.mem_cons_of_mem _ he)

/-- `arm` for the variables of the problem, their list without repeats and
the slots of the template, all computed by the caller. Every image is computed
once, checked, and kept in a table: `arm` computes it for the check and again
on every read of the substitution. -/
private def armShared (p : Problem s) (ks vars : List Variable) (hk : ks = keys p)
    (hv : vars = p.variables) (θ : Template s) (seen : List Variable) (_hs : seen = slots p θ)
    (base : Nat) (g : Variable → SortId) : Option (Substitution s) :=
  let img := images θ (name seen base g)
  let table := ks.map fun v => (v, img v)
  if ok : table.all (fun e => e.2.checkSort e.1.sort) then
    some {
      image := tabulate table
      support := vars
      outside := fun v out => tabulate_outside table v fun e he same => by
        obtain ⟨w,hw,rfl⟩ := List.mem_map.mp he
        exact out (hv ▸ mem_keys.mp (hk ▸ same ▸ hw))
      sorted := tabulate_sorted table fun e he =>
        Term.checkSort_sound _ _ (List.all_eq_true.mp ok e he) }
  else none

private theorem armShared_eq (p : Problem s) (ks vars : List Variable) (hk : ks = keys p)
    (hv : vars = p.variables) (θ : Template s) (seen : List Variable) (hs : seen = slots p θ)
    (base : Nat) (g : Variable → SortId) :
    armShared p ks vars hk hv θ seen hs base g = arm p θ base g := by
  subst hk hv hs
  have cond : (((keys p).map fun v => (v, images θ (name (slots p θ) base g) v)).all
      (fun e => e.2.checkSort e.1.sort)) =
      (keys p).all (fun v => (images θ (name (slots p θ) base g) v).checkSort v.sort) := by
    rw [List.all_map]
    rfl
  unfold armShared arm
  dsimp only
  split
  · next yes =>
    have yes' := cond ▸ yes
    simp only [yes', ↓reduceDIte]
    congr 1
    have same : tabulate ((keys p).map fun v => (v, images θ (name (slots p θ) base g) v)) =
        fun v => if v ∈ p.variables then images θ (name (slots p θ) base g) v else .var v := by
      funext v
      split
      · next live => exact tabulate_map _ _ (mem_keys.mpr live)
      · next dead =>
        apply tabulate_outside
        intro e he eq
        obtain ⟨w,hw,rfl⟩ := List.mem_map.mp he
        exact dead (eq ▸ mem_keys.mp hw)
    simp only [read, Substitution.mk.injEq, and_true]
    exact same
  · next no =>
    have no' := cond ▸ no
    simp only [no', Bool.false_eq_true, ↓reduceDIte]

/-- `solveRows` with the variables of the problem listed once for all rows,
and the variables of a template listed without repeats through buckets. -/
private def solveRowsShared (p : Problem s) (rows : List (Template s)) (avoid : List Variable) :=
  let vars := p.variables
  let ks := keys p
  let base := VariablePermutation.freshBound (vars ++ avoid)
  rows.flatMap fun θ =>
    let ds := demandList p θ
    (armShared p ks vars rfl rfl θ
      (Buckets.dedup Variable.id (ks.flatMap fun v => (θ v).variables)) (Buckets.dedup_eq ..) base
      (assoc ((Buckets.dedup Variable.id (ds.map (·.1))).map fun w => (w, principal ds w)))).toList

@[csimp] private theorem solveRows_eq_shared : @solveRows = @solveRowsShared := by
  funext s p rows avoid
  unfold solveRows solveRowsShared perTemplate
  dsimp only
  congr 1
  funext θ
  have listed := Buckets.dedup_eq Variable.id ((demandList p θ).map (·.1))
  calc (arm p θ (VariablePermutation.freshBound (p.variables ++ avoid)) (assoc (sortTable p θ))).toList
      = (arm p θ (VariablePermutation.freshBound (p.variables ++ avoid))
          (assoc ((Buckets.dedup Variable.id ((demandList p θ).map (·.1))).map fun w =>
            (w, principal (demandList p θ) w)))).toList := by rw [listed]; rfl
    _ = _ := congrArg Option.toList (armShared_eq ..).symm

/-- A raw solver may return each template as a closure that recomputes its
images. Evaluate every image of a problem variable once before sorting. -/
def solve (p : Problem s) (rows : List (Template s)) (avoid : List Variable) :=
  let once := keys p
  solveRows p ((rows.map fun θ => once.map fun v => (v, θ v)).map tabulate) avoid

private theorem tabulate_complete {p : Problem s} {rows : List (Template s)}
    (h : CompleteTemplates p rows) :
    CompleteTemplates p
      ((rows.map fun θ => p.variables.eraseDups.map fun v => (v, θ v)).map tabulate) := by
  have same (θ : Template s) (v) (hv : p.Occurs v) :
      tabulate (p.variables.eraseDups.map fun w => (w, θ w)) v = θ v :=
    tabulate_map θ _ (List.mem_eraseDups.mpr ((p.mem_variables v).mpr hv))
  constructor
  · intro τ hm e he
    obtain ⟨table,ht,rfl⟩ := List.mem_map.mp hm
    obtain ⟨θ,hθ,rfl⟩ := List.mem_map.mp ht
    rw [Term.subst_eq_of_agree _ θ e.lhs (fun v hv => same θ v ⟨e,he,.inl hv⟩),
      Term.subst_eq_of_agree _ θ e.rhs (fun v hv => same θ v ⟨e,he,.inr hv⟩)]
    exact h.sound θ hθ e he
  · intro ρ sol
    obtain ⟨θ,hθ,μ,agree⟩ := h.covers ρ sol
    refine ⟨_, List.mem_map_of_mem (List.mem_map_of_mem hθ), μ, fun v hv => ?_⟩
    rw [same θ v hv]
    exact agree v hv

private theorem read_apply (p : Problem s) (θ : Template s) (label : Variable → Variable)
    {ok} (t : Term s) (live : ∀ v, t.Occurs v → p.Occurs v) :
    (read p (images θ label) ok).apply t = (t.subst θ).subst (fun w => .var (label w)) := by
  rw [Term.subst_comp]
  apply Term.subst_eq_of_agree
  intro v hv
  exact ite_eq_left ((p.mem_variables _).mpr (live _ hv))

private theorem sort_at_root {t : Term s} {k} (ht : HasSort t k) : HasSort t t.rootSort := by
  induction ht with
  | widen _ _ ih => exact ih
  | var => exact .var _
  | atom => exact .atom _
  | free _ _ h _ => exact .free _ _ h
  | ac _ _ _ ha hb _ _ => exact .ac _ _ _ ha hb
  | comm _ _ _ ha hb _ _ => exact .comm _ _ _ ha hb

/-- Replacing each actual parameter by a variable of its actual least sort
preserves every sort check. Each occurring parameter has that least sort. -/
private theorem generalizeSorts (t : Term s) (μ : Variable → Term s) (label : Variable → Variable)
    (names : ∀ w, t.Occurs w → (label w).sort = (μ w).rootSort) (k : SortId)
    (typed : (t.subst μ).checkSort k = true) :
    (t.subst (fun w => .var (label w))).checkSort k = true ∧
      ∀ w, t.Occurs w → HasSort (μ w) (label w).sort := by
  induction t generalizing k with
  | var v =>
    have ht := Term.checkSort_sound _ _ typed
    have e := names v rfl
    refine ⟨(Subsort.check_iff ..).mpr (e ▸ Term.rootSort_le ht),?_⟩
    intro w hw
    obtain rfl := hw
    exact e ▸ sort_at_root ht
  | atom => exact ⟨typed, nofun⟩
  | free f xs ih =>
    simp only [Term.subst, Term.checkSort, Bool.and_eq_true, List.all_eq_true] at typed ⊢
    have child i := ih i (fun w hw => names w ⟨i,hw⟩) _ (typed.2 i (List.mem_finRange i))
    exact ⟨⟨typed.1, fun i _ => (child i).1⟩, fun w ⟨i,hw⟩ => (child i).2 w hw⟩
  | ac f a b ia ib | comm f a b ia ib =>
    simp only [Term.subst, Term.checkSort, Bool.and_eq_true] at typed ⊢
    have left := ia (fun w hw => names w (.inl hw)) _ typed.1.2
    have right := ib (fun w hw => names w (.inr hw)) _ typed.2
    exact ⟨⟨⟨typed.1.1,left.1⟩,right.1⟩,fun w hw => hw.elim (left.2 w) (right.2 w)⟩

private theorem realize (vs : List Variable) (label : Variable → Variable) (μ : Variable → Term s)
    (inj : ∀ v ∈ vs, ∀ w ∈ vs, label v = label w → v = w)
    (typed : ∀ v ∈ vs, HasSort (μ v) (label v).sort) :
    ∃ δ : Substitution s, ∀ v ∈ vs, δ.image (label v) = μ v := by
  classical
  let δ : Substitution s := {
    image := fun w => if h : ∃ v ∈ vs, label v = w then μ h.choose else .var w
    support := vs.map label
    outside := by
      intro w hw
      exact dite_eq_right (fun h => hw (List.mem_map.mpr h))
    sorted := by
      intro w
      split
      · next h =>
        have ok := typed h.choose h.choose_spec.1
        rwa [h.choose_spec.2] at ok
      · exact .var w }
  refine ⟨δ,fun v hv => ?_⟩
  have h : ∃ w ∈ vs, label w = label v := ⟨v,hv,rfl⟩
  simp only [δ,dite_eq_left h]
  exact congrArg μ (inj h.choose h.choose_spec.1 v hv h.choose_spec.2)

private theorem perTemplate_sound {p : Problem s} {θ : Template s} {avoid σ}
    (mem : σ ∈ perTemplate p θ avoid)
    (solves : ∀ e ∈ p, EquivB (e.lhs.subst θ) (e.rhs.subst θ)) :
    p.Solves σ ∧ DomainRestricted p σ ∧ FreshFor p avoid σ := by
  have hit : arm p θ (VariablePermutation.freshBound (p.variables ++ avoid)) (assoc (sortTable p θ)) = some σ := by
    unfold perTemplate at mem
    cases h : arm p θ (VariablePermutation.freshBound (p.variables ++ avoid)) (assoc (sortTable p θ)) with
    | none => simp [h] at mem
    | some τ => simp [h] at mem; rw [mem]
  simp only [arm] at hit
  split at hit
  · next ok =>
    obtain rfl := Option.some.inj hit
    constructor
    · intro e he
      rw [read_apply p θ _ e.lhs (fun _ hv => ⟨e,he,.inl hv⟩),
        read_apply p θ _ e.rhs (fun _ hv => ⟨e,he,.inr hv⟩)]
      exact (solves e he).subst _
    · constructor
      · intro v off
        exact ite_eq_right (fun mem => off ((p.mem_variables _).mp mem))
      · intro v live w occurs _ clash
        simp only [read, ite_eq_left ((p.mem_variables _).mpr live), images, Term.occurs_rename] at occurs
        obtain ⟨k,_,rfl⟩ := occurs
        have h := VariablePermutation.lt_freshBound (p.variables ++ avoid) _
          (List.mem_append_right _ clash)
        simp only [name] at h
        omega
  · contradiction

private theorem perTemplate_covers {p : Problem s} (θ : Template s) (avoid : List Variable)
    (ρ : Substitution s) (μ : Variable → Term s)
    (agree : ∀ v, p.Occurs v → EquivB (ρ.image v) ((θ v).subst μ)) :
    ∃ σ ∈ perTemplate p θ avoid, Substitution.InstanceOn p.Occurs ρ σ := by
  let vs := slots p θ
  let base := VariablePermutation.freshBound (p.variables ++ avoid)
  let g0 : Variable → SortId := fun w => (μ w).rootSort
  let label0 := name vs base g0
  have checked (v) (hv : p.Occurs v) := generalizeSorts (θ v) μ label0
    (fun _ _ => rfl) v.sort
    (SortClash.check_equiv (agree v hv) v.sort ▸ Term.checkSort_complete (ρ.sorted v))
  have below : ∀ d ∈ demandList p θ, Subsort (g0 d.1) d.2 := by
    intro d hd
    obtain ⟨v,hv,hm⟩ := List.mem_flatMap.mp hd
    exact demands_of_check (θ v) label0 v.sort (checked v ((p.mem_variables v).mp (mem_keys.mp hv))).1 d hm
  have fit : ∀ d ∈ demandList p θ,
      Subsort (g0 d.1) (assoc (sortTable p θ) d.1) ∧ Subsort (assoc (sortTable p θ) d.1) d.2 := by
    intro d hd
    rw [sortTable_eq hd]
    exact principal_spec _ g0 below d hd
  let label := name vs base (assoc (sortTable p θ))
  have ok : ∀ v ∈ p.variables, ((images θ label v).checkSort v.sort) = true := by
    intro v hv
    exact check_of_demands (θ v) label0 label v.sort (checked v ((p.mem_variables v).mp hv)).1
      (fun d hd => (fit d (List.mem_flatMap.mpr ⟨v,mem_keys.mpr hv,hd⟩)).2)
  have typed : ∀ w ∈ vs, HasSort (μ w) (label w).sort := by
    intro w hw
    obtain ⟨v,hv,occ⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp hw)
    have live := (p.mem_variables v).mp (mem_keys.mp hv)
    have seen := (Term.mem_variables ..).mp occ
    obtain ⟨j,hj⟩ := demand_of_occurs (θ v) v.sort w seen
    exact .widen ((checked v live).2 w seen) (fit (w,j) (List.mem_flatMap.mpr ⟨v,hv,hj⟩)).1
  obtain ⟨δ,hδ⟩ := realize vs label μ (fun _ hv _ hw => name_injective hv hw) typed
  have hit : arm p θ base (assoc (sortTable p θ)) = some (read p (images θ label) ok) :=
    dite_eq_left (List.all_eq_true.mpr (fun v hv => ok v (mem_keys.mp hv)))
  refine ⟨read p (images θ label) ok, by simp [perTemplate, base, hit], δ, ?_⟩
  intro v hv
  apply (agree v hv).trans
  change EquivB _ (δ.apply (if v ∈ p.variables then images θ label v else .var v))
  rw [ite_eq_left ((p.mem_variables _).mpr hv)]
  unfold Substitution.apply images
  rw [Term.subst_comp]
  have eq := Term.subst_eq_of_agree μ (fun w => δ.image (label w)) (θ v)
    (fun w hw => (hδ w (slot_mem hv hw)).symm)
  exact eq ▸ EquivB.refl _

private theorem correctRows (p : Problem s) (rows : List (Template s)) (h : CompleteTemplates p rows)
    (avoid : List Variable) : (Outcome.complete (solveRows p rows avoid)).CorrectIn p avoid := by
  have sound (σ) (mem : σ ∈ solveRows p rows avoid) : p.Solves σ ∧ DomainRestricted p σ ∧ FreshFor p avoid σ := by
    obtain ⟨θ,hθ,hm⟩ := List.mem_flatMap.mp mem
    exact perTemplate_sound hm (h.sound θ hθ)
  refine ⟨⟨fun σ hm => (sound σ hm).1,?_⟩,fun σ hm => (sound σ hm).2.1,fun σ hm => (sound σ hm).2.2⟩
  intro ρ hs
  obtain ⟨θ,ht,μ,agree⟩ := h.covers ρ hs
  obtain ⟨σ,hm,instanceOf⟩ := perTemplate_covers θ avoid ρ μ agree
  exact ⟨σ,List.mem_flatMap.mpr ⟨θ,ht,hm⟩,instanceOf⟩

theorem correct (p : Problem s) (rows : List (Template s)) (h : CompleteTemplates p rows)
    (avoid : List Variable) : (Outcome.complete (solve p rows avoid)).CorrectIn p avoid := by
  have same : keys p = p.variables.eraseDups := Buckets.dedup_eq ..
  unfold solve
  rw [same]
  exact correctRows p _ (tabulate_complete h) avoid

private theorem slots_nodup (p : Problem s) (θ : Template s) : (slots p θ).Nodup := by
  have distinct : ∀ xs : List Variable, xs.eraseDups.Nodup := by
    intro xs
    induction h : xs.length using Nat.strongRecOn generalizing xs with
    | ind n ih =>
      cases xs with
      | nil => simp
      | cons x xs =>
        rw [List.eraseDups_cons, List.nodup_cons]
        refine ⟨by simp [List.mem_eraseDups], ih _ ?_ _ rfl⟩
        subst h
        exact Nat.lt_succ_of_le (List.length_filter_le _ _)
  exact distinct _

/-- Every answer renames the parameters of its template to the consecutive
identifiers from the fresh bound. The variables in the images of the problem
variables are exactly the members of a list whose entry `i` has identifier
`bound + i`. -/
theorem solve_range (p : Problem s) (rows : List (Template s)) (avoid : List Variable)
    (σ : Substitution s) (mem : σ ∈ solve p rows avoid) :
    ∃ ws : List Variable,
      (∀ i (h : i < ws.length), ws[i].id = VariablePermutation.freshBound (p.variables ++ avoid) + i) ∧
      ∀ w, (∃ v, p.Occurs v ∧ (σ.image v).Occurs w) ↔ w ∈ ws := by
  unfold solve solveRows at mem
  obtain ⟨θ, -, hm⟩ := List.mem_flatMap.mp mem
  let base := VariablePermutation.freshBound (p.variables ++ avoid)
  have hit : arm p θ base (assoc (sortTable p θ)) = some σ := by
    unfold perTemplate at hm
    cases h : arm p θ (VariablePermutation.freshBound (p.variables ++ avoid)) (assoc (sortTable p θ)) with
    | none => simp [h] at hm
    | some τ => simp [h] at hm; rw [hm]
  simp only [arm] at hit
  split at hit
  · next ok =>
    obtain rfl := Option.some.inj hit
    let label := name (slots p θ) base (assoc (sortTable p θ))
    refine ⟨(slots p θ).map label, ?_, fun w => ⟨?_, ?_⟩⟩
    · intro i h
      have lt : i < (slots p θ).length := by simpa using h
      simp only [List.getElem_map, label, name, (slots_nodup p θ).idxOf_getElem i lt, base]
    · rintro ⟨v, live, occurs⟩
      simp only [read, ite_eq_left ((p.mem_variables _).mpr live), images, Term.occurs_rename] at occurs
      obtain ⟨k, seen, rfl⟩ := occurs
      exact List.mem_map_of_mem (slot_mem live seen)
    · intro hw
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hw
      obtain ⟨v, hv, occ⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp hk)
      have live := (p.mem_variables v).mp (mem_keys.mp hv)
      refine ⟨v, live, ?_⟩
      simp only [read, ite_eq_left ((p.mem_variables _).mpr live), images, Term.occurs_rename]
      exact ⟨k, (Term.mem_variables ..).mp occ, rfl⟩
  · contradiction

/-- One raw component solver valid for every input suffices for sorted and
kind-level Tamarin queries. Sort refinement and caller freshness are discharged here. -/
def unifier (raw : Problem s → List (Template s)) (hc : ∀ p, CompleteTemplates p (raw p)) :
    VerifiedUnifier s (fun _ => True) where
  solve p _ avoid := solve p (raw p) avoid
  correct p _ avoid := (correct p _ (hc p) avoid).mathematical
  domain p _ avoid := (correct p _ (hc p) avoid).domain
  fresh p _ avoid := (correct p _ (hc p) avoid).fresh

/-- The empty problem gets one substitution from one template, and it moves
no variable. -/
theorem solve_nil (x : Template s) (avoid : List Variable) :
    ∃ σ, solve [] [x] avoid = [σ] ∧ ∀ v, σ.image v = .var v := ⟨_, rfl, fun _ => rfl⟩

end Tamarin.UnifierSorts
