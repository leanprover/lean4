module

/-!
Tests that a `for` loop over the full range `*...*` determines the range's element type from the
loop variable, e.g. from an ascription on it or from how it is used in the body. The element type
is an `outParam` of `ForIn`, so this relies on the default instances on `instForInOfForIn'` and on
the `ForIn'` instance of `Std.Rii`.
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
