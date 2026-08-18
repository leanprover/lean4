import Std.Internal.Do

/-!
Every form of the intrinsic verification syntax reports that it is experimental, at the keyword that
introduces the form, and `set_option experimental.intrinsic true` silences those reports.
-/

open Std.Internal.Do

set_option mvcgen.warning false

/--
warning: The `requires` clause is part of the experimental intrinsic verification syntax; `set_option experimental.intrinsic true` acknowledges its experimental status and silences this warning.
---
warning: The `ensures` clause is part of the experimental intrinsic verification syntax; `set_option experimental.intrinsic true` acknowledges its experimental status and silences this warning.
-/
#guard_msgs in
def identity (n : Nat) : Id Nat
    requires True
    ensures r => r = n :=
  pure n

/--
warning: The `ensures` clause is part of the experimental intrinsic verification syntax; `set_option experimental.intrinsic true` acknowledges its experimental status and silences this warning.
---
warning: The `assert` element is part of the experimental intrinsic verification syntax; `set_option experimental.intrinsic true` acknowledges its experimental status and silences this warning.
-/
#guard_msgs in
def double (n : Nat) : Id Nat
    ensures r => r = n + n := do
  let d := n + n
  assert d = n + n
  return d

/--
warning: The `invariant` clause is part of the experimental intrinsic verification syntax; `set_option experimental.intrinsic true` acknowledges its experimental status and silences this warning.
-/
#guard_msgs in
def sum (xs : List Nat) : Id Nat := do
  let mut acc := 0
  for _x in xs invariant _pref _suff => 0 ≤ acc do
    acc := acc + 1
  return acc

/-! Acknowledging the experimental status silences every form. -/

set_option experimental.intrinsic true

#guard_msgs in
def identity' (n : Nat) : Id Nat
    requires True
    ensures r => r = n :=
  pure n

#guard_msgs in
def double' (n : Nat) : Id Nat
    ensures r => r = n + n := do
  let d := n + n
  assert d = n + n
  return d

#guard_msgs in
def sum' (xs : List Nat) : Id Nat := do
  let mut acc := 0
  for _x in xs invariant _pref _suff => 0 ≤ acc do
    acc := acc + 1
  return acc
