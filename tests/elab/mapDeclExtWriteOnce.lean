import Lean

/-!
Declaration-keyed extension entries are write-once: `allowOverwrite` permits updating a
`MapDeclarationExtension` entry, as docstrings do, while any other overwrite panics and keeps the
existing entries. Registries kept in other extensions accept idempotent re-registration.
-/

open Lean

def foo := 1
def bar := 2
def baz := 3

/-- info: first, then second -/
#guard_msgs in
#eval show CoreM Unit from do
  modifyEnv fun env => docStringExt.insert env ``foo "first"
  let first := docStringExt.find? (← getEnv) ``foo
  modifyEnv fun env => docStringExt.insert env ``foo "second" (allowOverwrite := true)
  let second := docStringExt.find? (← getEnv) ``foo
  logInfo m!"{first.getD ""}, then {second.getD ""}"

#guard_panic in
#eval show CoreM Unit from do
  modifyEnv fun env => docStringExt.insert env ``bar "first"
  modifyEnv fun env => docStringExt.insert env ``bar "second"

/-- info: first -/
#guard_msgs in
#eval show CoreM Unit from do
  logInfo m!"{(docStringExt.find? (← getEnv) ``bar).getD ""}"

/-- info: 5 -/
#guard_msgs in
#eval show CoreM Unit from do
  modifyEnv (setDefHeightOverride · ``foo 5)
  modifyEnv (setDefHeightOverride · ``foo 5)
  logInfo m!"{getMaxHeight (← getEnv) (mkConst ``foo)}"

#guard_panic in
#eval show CoreM Unit from do
  modifyEnv (setDefHeightOverride · ``baz 3)
  modifyEnv (setDefHeightOverride · ``baz 4)

-- The panicking registration keeps the existing overrides, including the one for `foo`.
/-- info: 5, 3 -/
#guard_msgs in
#eval show CoreM Unit from do
  let env ← getEnv
  logInfo m!"{getMaxHeight env (mkConst ``foo)}, {getMaxHeight env (mkConst ``baz)}"
