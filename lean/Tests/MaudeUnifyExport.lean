import TamarinRuntime

namespace Tamarin.MaudeUnifyExportTests

/-! Two `unify` commands of a captured Maude 3.5.1 session on the module of a
theory with exclusive or and pairing, and Maude's replies, under the ranks of
that module: operators `f p c n list cons nil zero xor fst pair snd` in that
order, the variable symbols `Msg Fresh Pub Node TOP [TOP]` after them. -/

private abbrev kernel := Executable.theoryMaudeUnify fun _ => false

/-- The theory: exclusive or (flag 2) and the three pairing symbols. -/
private def free : Array UInt64 := #[1, 2, 1]

/-- An operator's rank is its arity times `2^24` plus its position. -/
private def rank (arity position : UInt64) : UInt64 := (arity <<< 24) ||| position

private def ranks : Array (Array UInt64) := #[
  #[0, 0, 0, 0, rank 0 7],                           -- zero (free id 4)
  #[],                                               -- no C symbol
  #[0, rank 2 8],                                    -- xor (AC id 1)
  #[rank 1 1, rank 1 0, rank 1 2, rank 1 3, 0],      -- p f c n t
  #[17, 14, 13, 12, 15, 0],                          -- [TOP] Pub Fresh Msg Node TamNat
  #[0, 4, 5, 2, 3, 6]]                               -- sort indices

private def fuel : UInt64 := 1048576

/-- `tamxor(x0:Fresh,x1:Fresh) =? tamxor(x2:s,x3:s)`. -/
private def sums (s : UInt64) : Array (Array UInt64) :=
  #[#[0,0,1], #[0,1,1], #[4,1,0,1], #[0,2,s], #[0,3,s], #[4,1,3,4]]

-- Maude: x0 --> #1, x1 --> #2, x2 --> #1, x3 --> #2; then x0 --> #1,
-- x1 --> #2, x2 --> #2, x3 --> #1, all of sort Fresh. #k is the variable
-- 3 + k, the least identifier above the query being 4.
#guard kernel 2 free 0 ranks fuel (sums 2) #[2,5] == #[#[1],
  #[], #[0,1,0,4,1], #[1,1,0,5,1], #[2,2,0,4,1], #[3,2,0,5,1],
  #[], #[0,1,0,4,1], #[1,1,0,5,1], #[2,2,0,5,1], #[3,2,0,4,1]]

-- Maude: x0 --> #1, x1 --> #2, x2 --> #1, x3 --> #2; then x0 --> #2,
-- x1 --> #1, x2 --> #1, x3 --> #2.
#guard kernel 2 free 0 ranks fuel (sums 1) #[2,5] == #[#[1],
  #[], #[0,1,0,4,1], #[1,1,0,5,1], #[2,1,0,4,1], #[3,1,0,5,1],
  #[], #[0,1,0,5,1], #[1,1,0,4,1], #[2,1,0,4,1], #[3,1,0,5,1]]

-- Other statuses: no unifier, out of fuel, a malformed packet, arguments
-- that are no signature, and a caller that says stop.
#guard kernel 2 free 0 ranks fuel #[#[1,0,0], #[1,1,0]] #[0,1] == #[#[1]]
#guard kernel 2 free 0 ranks 0 (sums 2) #[2,5] == #[#[3]]
#guard kernel 2 free 0 ranks fuel (sums 2) #[2] == #[#[0]]
#guard kernel 4 free 0 ranks fuel (sums 2) #[2,5] == #[#[0]]
#guard Executable.theoryMaudeUnify (fun _ => true) 2 free 0 ranks fuel (sums 2) #[2,5] == #[#[4]]

end Tamarin.MaudeUnifyExportTests
