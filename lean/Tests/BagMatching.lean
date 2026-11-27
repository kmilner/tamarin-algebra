import Tamarin.ReferenceMatching

namespace Tamarin.BagMatchingTests
open ReferenceMatching ACRepresentation

private abbrev sig : Signature where
  FreeSym := Nat
  arity := fun f => f
  CSym := Nat
  ACSym := Nat
  Atom := Nat
  inputSort := fun _ _ => .msg
  outputSort := fun _ => .msg
  cSort := fun _ => .msg
  acSort := fun _ => .msg
  atomSort := fun n => if n < 100 then .pub else .fresh

private abbrev T := Term sig
private def v (i : Nat) : Variable := ⟨i,.msg⟩
private def x (i : Nat) : T := .var (v i)
private def n (i : Nat) : T := .var ⟨i,.fresh⟩
private def a : T := .atom 1
private def b : T := .atom 2
private def k (i : Nat) : T := .atom (100 + i)
private def h (t : T) : T := .free 1 fun _ => t
private def c (u w : T) : T := .comm 7 u w
private def plus (u w : T) : T := .ac 3 u w
private def times (u w : T) : T := .ac 4 u w
private def bag (xs : List T) : T := (decode (sig := sig) 3 xs).getD a

private def answers (p t : T) : List (Substitution sig) := solve [⟨p,t⟩] p.variables

-- Three variables share {a, b^4, s^m}. The count is the number of ways to
-- give each variable a nonempty sub-bag, not the number of list splits.
private def repeated (m : Nat) : T := bag ([a,b,b,b,b] ++ List.replicate m (x 9))
private def three : T := plus (x 0) (plus (x 1) (x 2))
#guard (answers three (repeated 5)).length == 768
#guard (answers three (repeated 6)).length == 1053
#guard (answers three (repeated 12)).length == 3708
#guard (answers (plus (plus (x 0) (x 1)) (x 2)) (repeated 6)).length == 1053

-- Equality reads both sides as bags, whatever their nesting and order.
#guard equal (repeated 12) (bag (List.replicate 12 (x 9) ++ [b,b,a,b,b]))
#guard !equal (repeated 12) (bag (List.replicate 12 (x 9) ++ [b,b,a,b,a]))
#guard equal (plus (plus a (h (plus b a))) (c b a)) (plus (c a b) (plus (h (plus a b)) a))
#guard !equal (plus a (times b a)) (plus a (times b b))
#guard equal (bag ((List.range 60).map fun i => .atom i)) (bag ((List.range 60).map fun i => .atom i).reverse)

-- Every occurrence of one variable receives the same image.
#guard (answers (plus (x 0) (x 0)) (bag [a,b,a,b])).length == 1
#guard (answers (plus (x 0) (x 0)) (bag [a,b,a,b])).all fun σ => equal (σ.image (v 0)) (plus a b)
#guard (answers (plus (x 0) (x 0)) (bag [a,b,b])).isEmpty
#guard (answers (plus (x 0) (plus (x 0) (x 1))) (bag [a,a,b,b,b])).length == 3
#guard (answers (plus (x 0) (h (x 0))) (bag [h (plus a b), b, a])).length == 1
#guard (answers (plus (x 0) (h (x 0))) (bag [h (plus a b), b, b])).isEmpty

-- Rigid operands are removed first; the variable takes all that is left.
#guard (answers (plus (x 0) (plus a (h b))) (bag ([h b] ++ (List.range 30).map fun i => .atom i))).length == 1
#guard (answers (plus (x 0) (plus a (h b))) (bag ((List.range 30).map fun i => .atom i))).isEmpty

-- A fresh variable takes one fresh operand and never a product.
#guard (answers (plus (n 0) (x 1)) (bag [k 0, k 1, a])).length == 2
#guard (answers (plus (n 0) (x 1)) (bag [a, b, a])).isEmpty
#guard (answers (plus (n 0) (n 1)) (bag [k 0, k 1, k 2])).isEmpty

-- A variable outside the bindable list stays itself.
#guard (solve [⟨plus (x 0) (x 1), plus a (x 1)⟩] [v 0]).length == 1
#guard (solve [⟨plus (x 0) (x 1), plus a b⟩] [v 0]).isEmpty
#guard (solve [⟨plus (x 0) (x 1), plus a b⟩] [v 0, v 1]).length == 2

-- Equations constrain shared variables together.
#guard (solve [⟨plus (x 0) (x 1), bag [a,b,b]⟩, ⟨h (x 0), h (plus b a)⟩] [v 0, v 1]).length == 1
#guard (solve [⟨plus (x 0) (x 1), bag [a,b,b]⟩, ⟨h (x 0), h (plus a a)⟩] [v 0, v 1]).isEmpty

-- The bag matcher and the list-splitting specification give the same
-- assignments on small inputs.
private def image (row : Requirements sig) (w : Variable) : T := (row.lookup w).getD (.var w)
private def coherent (row : Requirements sig) : Bool :=
  row.all fun (w,t) => row.all fun (u,r) => w != u || equal t r
private def covered (vars : List Variable) (rows other : List (Requirements sig)) : Bool :=
  rows.all fun row => other.any fun cand => vars.all fun w => equal (image row w) (image cand w)
private def agrees (p t : T) : Bool :=
  let old := (branches p t).filter coherent
  let new := BagMatching.rows (s := sig) [] (fun _ => true) equal p t
  covered p.variables old new && covered p.variables new old
#guard agrees three (bag [a,b,b,a,x 9])
#guard agrees (plus (x 0) (plus (h (x 1)) (x 0))) (bag [a,b,h (c a b),b,a])
#guard agrees (plus (x 0) (times (x 1) (x 2))) (bag [a,times b (times a b),b])
#guard agrees (c (plus (x 0) (x 1)) (x 2)) (c (h a) (bag [a,b,h a]))
#guard agrees (plus (plus (x 0) a) (plus (x 1) (c (x 2) b))) (bag [c b a,a,b,c a b,a])
#guard agrees (h (plus (x 0) (x 1))) (h a)

-- A variable that occurs k times chooses among at most ⌊m / k⌋ of m equal
-- operands, so wide bags of distinct operands are refuted without a search.
private def wide (n : Nat) : List T := (List.range n).map fun i => .atom i
#guard (answers (plus (x 0) (plus (x 0) (x 1))) (bag (wide 12 ++ wide 12))).length == 4094
#guard (answers (plus (x 0) (plus (x 0) (x 1))) (bag (wide 40))).isEmpty
#guard (answers (plus (x 0) (plus (x 0) (plus (x 0) (x 1)))) (bag (wide 6 ++ wide 6 ++ wide 6 ++ [a]))).length == 63
#guard (answers (plus (x 0) (x 0)) (bag [h (plus a b), h (plus b a)])).length == 1

-- The first answer is the head of the full list, and exists without the rest.
private def headAgrees (p t : T) : Bool :=
  match first [⟨p,t⟩] p.variables, (answers p t).head? with
  | some σ, some τ => p.variables.all fun w => equal (σ.image w) (τ.image w)
  | none, none => true
  | _, _ => false
#guard headAgrees three (repeated 6)
#guard headAgrees (plus (x 0) (plus (x 0) (x 1))) (bag [a,a,b,b,b])
#guard headAgrees (plus (x 0) (x 0)) (bag [a,b,b])
#guard headAgrees (c (plus (x 0) (x 1)) (x 2)) (c (h a) (bag [a,b,h a]))
#guard (first [⟨plus (x 0) (x 1), bag (wide 60)⟩] [v 0, v 1]).isSome
#guard (first [⟨plus (x 0) (x 1), bag [a,b,b]⟩, ⟨h (x 0), h (plus a a)⟩] [v 0, v 1]).isNone

-- A pattern as a proper sub-product keeps the untouched operands as context.
private def parts (p t : T) : List (T × T) := (subproducts (s := sig) 3 p t).map fun (θ,rest) => (θ.apply p,rest)
#guard (parts (plus (x 0) (h (x 0))) (bag [h a, b, a, b])).length == 1
#guard (parts (plus (x 0) (h (x 0))) (bag [h a, b, a, b])).all fun (inst,rest) =>
  equal (plus inst rest) (bag [h a, b, a, b]) && equal rest (plus b b)
#guard (parts (plus (x 0) (x 0)) (bag (wide 30))).isEmpty
#guard (parts (plus (x 0) (x 0)) (bag [a,a,b,b,b])).all fun (inst,rest) => equal (plus inst rest) (bag [a,a,b,b,b])
#guard (parts (plus (x 0) (x 0)) (bag [a,a,b,b,b])).length == 3
#guard (parts (plus a (x 0)) (bag [a,b])).isEmpty
#guard (parts (h (x 0)) (bag [h a, b, h b])).length == 2

-- Every waiting occurrence takes at least one operand, so a bag with as many
-- operands as occurrences has one sharing and a smaller bag has none.
private def keys (m : Nat) : List T := (List.range m).map x
#guard (solve [⟨bag (x 0 :: keys 40), bag (List.replicate 41 (x 99))⟩] ((List.range 40).map v)).length == 1
#guard (first [⟨bag (keys 12), bag (wide 64)⟩] ((List.range 12).map v)).isSome
#guard (first [⟨bag (keys 12), bag (wide 11)⟩] ((List.range 12).map v)).isNone

-- A fresh variable takes the one operand that the repeated variable cannot.
#guard (solve [⟨plus (n 0) (plus (x 1) (x 1)), bag (n 7 :: wide 40 ++ wide 40)⟩] [⟨0,.fresh⟩, v 1]).length == 1

-- Two equations bound the image of a shared variable together. Each of
-- `2X + Y` and `X + 2Y` alone has `2^24` sharings of these bags.
private def evens : List T := (List.range 24).map fun i => .atom (2 * i)
private def odds : List T := (List.range 24).map fun i => .atom (2 * i + 1)
private def twoRows (extra : List T) : Problem sig :=
  [⟨plus (x 0) (plus (x 0) (x 1)), bag (evens ++ evens ++ odds ++ extra)⟩,
    ⟨plus (x 0) (plus (x 1) (x 1)), bag (evens ++ odds ++ odds ++ extra)⟩]
#guard (solve (twoRows []) [v 0, v 1]).length == 1
#guard (solve (twoRows []).reverse [v 0, v 1]).length == 1
#guard (solve (twoRows []) [v 0, v 1]).all fun σ =>
  equal (σ.image (v 0)) (bag evens) && equal (σ.image (v 1)) (bag odds)
#guard (solve (twoRows [a]) [v 0, v 1]).isEmpty
#guard (first (twoRows [a]).reverse [v 0, v 1]).isNone
private def pinned : Problem sig := twoRows [] ++ [⟨h (x 0), h (bag evens.reverse)⟩]
#guard (solve pinned [v 0, v 1]).length == 1

end Tamarin.BagMatchingTests
