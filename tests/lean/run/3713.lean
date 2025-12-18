import Lean
open Lean  Elab Meta

def somethingBad : MetaM Nat := do
  IO.println "oh no"
  return 1

/-- error: invalid use of `(<- ...)`, must be nested inside a 'do' expression -/
#guard_msgs in
#eval show MetaM Unit from do
  let t := if false then ← somethingBad else 9

def foo : MetaM Bool :=
  return false

/-- error: invalid use of `(<- ...)`, must be nested inside a 'do' expression -/
#guard_msgs in
#eval show MetaM Unit from do
  let t := if (← foo) then ← somethingBad else 9

/--
info: 1
-/
#guard_msgs in
#eval show MetaM Nat from do
  let t := if (← foo) then 0 else 1
  return t
