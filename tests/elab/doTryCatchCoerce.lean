import Lean

/-!
With the legacy `do` elaborator, `try ... catch` accepts a body whose result
type only matches the surrounding expected type up to coercion; outside of
`try ... catch`, neither the `do` nor the term elaborator does. The new
elaborator (`backward.do.legacy false`) drops the `try`/`catch` exception so
that all three forms behave the same.
-/

open Lean

set_option pp.mvars.anonymous false

set_option backward.do.legacy true

example (name : Name) : CoreM (Option Nat) := do
  try
    unsafe evalConstCheck Nat ``Nat name
  catch _ =>
    return none

/-- error: typeclass instance problem is stuck
  MonadOptions ?_ -/
#guard_msgs (substring := true) in
example (name : Name) : CoreM (Option Nat) := do
  unsafe evalConstCheck Nat ``Nat name

/-- error: typeclass instance problem is stuck
  MonadOptions ?_ -/
#guard_msgs (substring := true) in
example (name : Name) : CoreM (Option Nat) :=
  unsafe evalConstCheck Nat ``Nat name

set_option backward.do.legacy false

/-- error: typeclass instance problem is stuck
  MonadOptions ?_ -/
#guard_msgs (substring := true) in
example (name : Name) : CoreM (Option Nat) := do
  try
    unsafe evalConstCheck Nat ``Nat name
  catch _ =>
    return none

/-- error: typeclass instance problem is stuck
  MonadOptions ?_ -/
#guard_msgs (substring := true) in
example (name : Name) : CoreM (Option Nat) := do
  unsafe evalConstCheck Nat ``Nat name

/-- error: typeclass instance problem is stuck
  MonadOptions ?_ -/
#guard_msgs (substring := true) in
example (name : Name) : CoreM (Option Nat) :=
  unsafe evalConstCheck Nat ``Nat name
