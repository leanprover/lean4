module

/-!
Tests that a `for` loop over a range whose element type is not fixed by its bounds, such as the full
range `*...*` or a range with literal bounds like `1...3`, determines the element type from the loop
variable, e.g. from an ascription on it or from how it is used in the body. The element type is an
`outParam` of `ForIn`, so this relies on the default instances on `instForInOfForIn'` and on the
`ForIn'` instances of the range types.
-/

open Std

set_option pp.mvars.anonymous false

/-- info: [0, 1, 2] -/
#guard_msgs in
#eval do
  let x : List (Fin 3) := *...*.toList
  IO.println x

/--
info: 0
1
2
-/
#guard_msgs in
#eval do
  for (i : Fin 3) in *...* do IO.println i

/-- info: #[0, 1, 2] -/
#guard_msgs in
#eval do
  let mut acc : Array (Fin 3) := #[]
  for i in *...* do acc := acc.push i
  IO.println acc

/--
info: 0
1
2
-/
#guard_msgs in
#eval do
  for _h : (i : Fin 3) in *...* do IO.println i

/-- info: 256 -/
#guard_msgs in
#eval Id.run do
  let mut n := 0
  for (_ : UInt8) in *...* do n := n + 1
  return n

/-- info: 3 -/
#guard_msgs in
#eval Id.run do
  let mut n := 0
  for _h : (_ : Fin 3) in *...* do n := n + 1
  return n

/-! Without any information about the element type, the loop still fails: the default instance only
applies once the element type is known. -/

/--
error: typeclass instance problem is stuck
  ForIn IO (Rii ?_) ?α

Note: Lean will not try to resolve this typeclass instance problem because the second type argument to `ForIn` contains metavariables. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs in
def noElementType : IO Unit := do
  for _ in *...* do pure ()

/-! The full range over `Nat` is infinite and has no `ForIn` instance, so the default instance does
not apply and the problem stays stuck. -/

/--
error: typeclass instance problem is stuck
  ForIn IO (Rii ?_) Nat

Note: Lean will not try to resolve this typeclass instance problem because the second type argument to `ForIn` contains metavariables. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs in
def infiniteRange : IO Unit := do
  for (i : Nat) in *...* do IO.println i

/-! Ranges with literal bounds take the element type of the loop before the literals default to
`Nat`. -/

/--
info: 1
2
-/
#guard_msgs in
#eval do
  for (i : Int) in 1...3 do IO.println i

/--
info: -9
-8
-/
#guard_msgs in
#eval do
  for i in 1...3 do IO.println (i + (-10 : Int))

/-- info: #[1, 2] -/
#guard_msgs in
#eval do
  let mut acc : Array Int := #[]
  for i in 1...3 do acc := acc.push i
  IO.println acc

/--
info: 1
2
-/
#guard_msgs in
#eval do
  for (i : Fin 5) in 1...3 do IO.println i

/--
info: 1
2
-/
#guard_msgs in
#eval do
  for _h : (i : Int) in 1...3 do IO.println i

/--
info: -2
-1
0
-/
#guard_msgs in
#eval do
  for (i : Int) in (-2)...=0 do IO.println i

/--
info: 2
3
-/
#guard_msgs in
#eval do
  for (i : Int) in 1<...=3 do IO.println i

/--
info: 0
1
2
-/
#guard_msgs in
#eval do
  for (i : UInt8) in *...3 do IO.println i

/--
info: -8
-6
-/
#guard_msgs in
#eval do
  for i in 1...3 do IO.println (i * 2 + (-10 : Int))

/-! Without information about the element type, literal bounds still default to `Nat`. -/

/--
info: 0
0
-/
#guard_msgs in
#eval do
  for i in 1...3 do IO.println (i - 5)

/-! The default instance does not apply when the range would have no `ForIn` instance at the
loop's element type: `1...*` over `Int` is infinite, so the literals default to `Nat` as before. -/

/--
error: failed to synthesize instance of type class
  ForIn IO (Rci Nat) Int

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: Aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.

To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-/
#guard_msgs in
#eval do
  for (i : Int) in 1...* do IO.println i
