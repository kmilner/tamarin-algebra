import TamarinRuntime

namespace Tamarin.MaudeVariantsExportTests

/-! Three `get variants` commands of captured Maude 3.5.1 sessions and
Maude's replies, under the ranks of each session's module (an operator's
rank is its arity times `2^24` plus its position in the module; the variable
symbols come after every operator). The reply of the proposer
`tamarin_maude_variants` lists the bindings Maude prints, in Maude's order,
with Maude's `#k` and `%k` as the variant's variable `k - 1`. The `rewrites:`
counts and the variant terms are not part of the reply. -/

/-- The search the export runs when its caller does not say stop: the copy
the compiler specialised inside `Executable.maudeVariantsFor`. `lake env lean`
does not rebuild imports, so run `lake build TamarinRuntime` after changing
the search: the interpreter crashes on a specialised copy left in a stale
`TamarinRuntime.olean`. -/
private abbrev kernel := Executable.maudeVariantsFor Interrupt.never

private def fuel : UInt64 := 1048576

/-! #### Pairing (the `Tutorial` theory)

```
get variants in MSG : list(cons(x0:Msg,cons(tamXCFUfst(x0:Msg),cons(tamXCFUfst(x0:Msg),nil)))) .

Variant 1
rewrites: 0
TOP: list(cons(#1:Msg, cons(tamXCFUfst(#1:Msg), cons(tamXCFUfst(#1:Msg), nil))))
x0:Msg --> #1:Msg

Variant 2
rewrites: 2
TOP: list(cons(tamXCFUpair(%1:Msg, %2:Msg), cons(%1:Msg, cons(%1:Msg, nil))))
x0:Msg --> tamXCFUpair(%1:Msg, %2:Msg)
```

The module's user symbols `adec aenc fst h pair pk snd` (ids 16 to 22), its
equations `adec(aenc(x0,pk(x1)),x1) = x0`, `fst(pair(x0,x1)) = x0` and
`snd(pair(x0,x1)) = x1`. -/

private def tutorialFree : Array UInt64 := #[2, 2, 1, 1, 2, 1, 1]

private def tutorialRanks : Array (Array UInt64) := #[
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    33554539, 33554540, 16777325, 16777326, 16777327, 33554543, 16777329],
  #[], #[],
  #[16777317, 16777316, 16777318, 16777319],    -- p f c n
  #[119, 116, 115, 114, 117, 120],              -- [TOP] Pub Fresh Msg Node TamNat
  #[0, 4, 5, 2, 3, 54],                         -- sort indices
  #[16777320, 33554537, 106]]                   -- list cons nil

private def tutorialNodes : Array (Array UInt64) := #[
  #[0, 0, 2], #[0, 0, 2], #[2, 18, 1], #[0, 0, 2], #[2, 18, 3], #[5, 0, 2, 4],
  #[0, 0, 2], #[0, 1, 2], #[2, 21, 7], #[2, 17, 6, 8], #[0, 1, 2], #[2, 16, 9, 10], #[0, 0, 2],
  #[0, 0, 2], #[0, 1, 2], #[2, 20, 13, 14], #[2, 18, 15], #[0, 0, 2],
  #[0, 0, 2], #[0, 1, 2], #[2, 20, 18, 19], #[2, 22, 20], #[0, 1, 2]]

private def tutorialRoots : Array UInt64 := #[5, 11, 12, 16, 17, 21, 22]

#guard kernel 0 tutorialFree 0 tutorialRanks fuel tutorialNodes tutorialRoots == #[#[1],
  #[], #[0, 2, 0, 0, 2],
  #[], #[0, 2, 0, 0, 2, 0, 1, 2, 2, 20, 2]]

/-! #### Exclusive or (`native_free_variant_context`)

```
get variants in MSG : list(cons(x0:Msg,cons(tamxor(x0:Msg,p(1)),nil))) .

Variant 1:  x0:Msg --> #1:Msg
Variant 2:  x0:Msg --> p(1)
Variant 3:  x0:Msg --> tamxor(%1:Msg, p(1))
Variant 4:  x0:Msg --> tamXCFUzero
```

User symbols `box fst h pair snd` (ids 16 to 20); the equations of pairing
and of exclusive or as the module writes them. -/

private def xorFree : Array UInt64 := #[2, 1, 1, 2, 1]

private def xorRanks : Array (Array UInt64) := #[
  #[0, 0, 0, 0, 107, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33554541, 16777326, 16777327, 33554544, 16777329],
  #[], #[0, 33554540],
  #[16777317, 16777316, 16777318, 16777319],
  #[119, 116, 115, 114, 117, 120],
  #[0, 4, 5, 2, 3, 54],
  #[16777320, 33554537, 106]]

private def xorNodes : Array (Array UInt64) := #[
  #[0, 0, 2], #[0, 0, 2], #[1, 1, 0], #[4, 1, 1, 2], #[5, 0, 3],
  #[0, 0, 2], #[0, 1, 2], #[2, 19, 5, 6], #[2, 17, 7], #[0, 0, 2],
  #[0, 0, 2], #[0, 1, 2], #[2, 19, 10, 11], #[2, 20, 12], #[0, 1, 2],
  #[0, 0, 2], #[0, 0, 2], #[4, 1, 15, 16], #[2, 4],
  #[0, 0, 2], #[0, 0, 2], #[0, 1, 2], #[4, 1, 19, 20, 21], #[0, 1, 2],
  #[0, 0, 2], #[2, 4], #[4, 1, 24, 25], #[0, 0, 2]]

private def xorRoots : Array UInt64 := #[4, 8, 9, 13, 14, 17, 18, 22, 23, 26, 27]

#guard kernel 2 xorFree 0 xorRanks fuel xorNodes xorRoots == #[#[1],
  #[], #[0, 2, 0, 0, 2],
  #[], #[0, 2, 1, 1, 0],
  #[], #[0, 2, 0, 0, 2, 1, 1, 0, 4, 1, 2],
  #[], #[0, 2, 2, 4, 0]]

/-! #### Diffie-Hellman (`native_shared_exponent`), over two layers

```
get variants in MSG : list(cons(x0:Fresh,cons(x1:Msg,cons(tamXCFUexp(p(2),x1:Msg),
  cons(tamXCFUexp(tamXCFUexp(p(2),x1:Msg),x0:Fresh),nil))))) .

Variant 1:  x0:Fresh --> #1:Fresh  x1:Msg --> #2:Msg
Variant 2:  x0:Fresh --> %1:Fresh  x1:Msg --> tamXCFUone
Variant 3:  x0:Fresh --> %2:Fresh  x1:Msg --> tammult(%1:Msg, tamXCFUinv(%2:Fresh))
Variant 4:  x0:Fresh --> %1:Fresh  x1:Msg --> tamXCFUinv(%1:Fresh)
Variant 5:  x0:Fresh --> %3:Fresh  x1:Msg --> tammult(%1:Msg, tamXCFUinv(tammult(%2:Msg, %3:Fresh)))
Variant 6:  x0:Fresh --> %2:Fresh  x1:Msg --> tamXCFUinv(tammult(%1:Msg, %2:Fresh))
```

User symbols `fst pair snd` (ids 16 to 18); the module's thirteen equations
of Diffie-Hellman and pairing in module order. -/

private def dhFree : Array UInt64 := #[1, 2, 1]

private def dhRanks : Array (Array UInt64) := #[
  #[33554541, 16777327, 107, 108, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16777328, 33554545, 16777330],
  #[], #[33554542],
  #[16777317, 16777316, 16777318, 16777319],
  #[120, 117, 116, 115, 118, 121],
  #[0, 4, 5, 2, 3, 54],
  #[16777320, 33554537, 106]]

private def dhNodes : Array (Array UInt64) := #[
  #[0, 0, 1], #[0, 1, 2], #[1, 2, 0], #[0, 1, 2], #[2, 0, 2, 3], #[1, 2, 0], #[0, 1, 2], #[2, 0, 5, 6],
  #[0, 0, 1], #[2, 0, 7, 8], #[5, 0, 1, 4, 9],
  #[0, 0, 2], #[2, 2], #[2, 0, 11, 12], #[0, 0, 2],
  #[2, 3], #[0, 0, 2], #[2, 0, 15, 16], #[2, 3],
  #[0, 0, 2], #[0, 1, 2], #[2, 0, 19, 20], #[0, 2, 2], #[2, 0, 21, 22], #[0, 0, 2], #[0, 1, 2],
  #[0, 2, 2], #[4, 0, 25, 26], #[2, 0, 24, 27],
  #[0, 0, 2], #[0, 1, 2], #[2, 17, 29, 30], #[2, 16, 31], #[0, 0, 2],
  #[0, 0, 2], #[2, 1, 34], #[2, 1, 35], #[0, 0, 2],
  #[2, 2], #[2, 1, 38], #[2, 2],
  #[0, 0, 2], #[0, 1, 2], #[2, 1, 42], #[4, 0, 41, 43], #[2, 1, 44], #[0, 1, 2], #[0, 0, 2], #[2, 1, 47],
  #[4, 0, 46, 48],
  #[0, 0, 2], #[0, 1, 2], #[2, 17, 50, 51], #[2, 18, 52], #[0, 1, 2],
  #[0, 0, 2], #[0, 1, 2], #[0, 0, 2], #[2, 1, 57], #[4, 0, 55, 56, 58], #[0, 1, 2],
  #[0, 0, 2], #[0, 0, 2], #[2, 1, 62], #[4, 0, 61, 63], #[2, 2],
  #[0, 0, 2], #[2, 2], #[4, 0, 66, 67], #[0, 0, 2],
  #[0, 0, 2], #[0, 1, 2], #[0, 0, 2], #[0, 2, 2], #[4, 0, 72, 73], #[2, 1, 74], #[4, 0, 70, 71, 75],
  #[0, 1, 2], #[0, 2, 2], #[2, 1, 78], #[4, 0, 77, 79],
  #[0, 0, 2], #[0, 0, 2], #[0, 1, 2], #[4, 0, 82, 83], #[2, 1, 84], #[4, 0, 81, 85], #[0, 1, 2], #[2, 1, 87],
  #[0, 0, 2], #[0, 1, 2], #[2, 1, 90], #[0, 2, 2], #[2, 1, 92], #[4, 0, 89, 91, 93],
  #[0, 0, 2], #[0, 1, 2], #[0, 2, 2], #[4, 0, 96, 97], #[2, 1, 98], #[4, 0, 95, 99],
  #[0, 0, 2], #[2, 1, 101], #[0, 1, 2], #[2, 1, 103], #[4, 0, 102, 104],
  #[0, 0, 2], #[0, 1, 2], #[4, 0, 106, 107], #[2, 1, 108]]

private def dhRoots : Array UInt64 :=
  #[10, 13, 14, 17, 18, 23, 28, 32, 33, 36, 37, 39, 40, 45, 49, 53, 54, 59, 60, 64, 65, 68, 69, 76, 80, 86, 88,
    94, 100, 105, 109]

#guard kernel 1 dhFree 0 dhRanks fuel dhNodes dhRoots == #[#[1],
  #[], #[0, 1, 0, 0, 1], #[1, 2, 0, 1, 2],
  #[], #[0, 1, 0, 0, 1], #[1, 2, 2, 2, 0],
  #[], #[0, 1, 0, 1, 1], #[1, 2, 0, 0, 2, 0, 1, 1, 2, 1, 1, 4, 0, 2],
  #[], #[0, 1, 0, 0, 1], #[1, 2, 0, 0, 1, 2, 1, 1],
  #[], #[0, 1, 0, 2, 1], #[1, 2, 0, 0, 2, 0, 1, 2, 0, 2, 1, 4, 0, 2, 2, 1, 1, 4, 0, 2],
  #[], #[0, 1, 0, 1, 1], #[1, 2, 0, 0, 2, 0, 1, 1, 4, 0, 2, 2, 1, 1]]

/-! #### Other replies

Out of fuel, a request without a query, an odd number of equation sides, a
row that names a symbol outside the theory, arguments that are no signature,
and a caller that says stop. -/

#guard kernel 2 xorFree 0 xorRanks 0 xorNodes xorRoots == #[#[3]]
#guard kernel 2 xorFree 0 xorRanks fuel xorNodes #[] == #[#[0]]
#guard kernel 2 xorFree 0 xorRanks fuel xorNodes #[4, 8] == #[#[0]]
#guard kernel 2 xorFree 0 xorRanks fuel (xorNodes.push #[2, 21, 0]) xorRoots == #[#[0]]
#guard kernel 32 xorFree 0 xorRanks fuel xorNodes xorRoots == #[#[0]]
#guard Executable.maudeVariants (fun _ => true) 2 xorFree 0 xorRanks fuel xorNodes xorRoots == #[#[4]]

end Tamarin.MaudeVariantsExportTests
