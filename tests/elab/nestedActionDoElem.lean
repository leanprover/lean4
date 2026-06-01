/-!
Tests that the `nestedAction` parser (`← <action>`) accepts a `doElem` after `←`.

The legacy `do` elaborator only supports a `doExpr` (a `doElem` wrapping a term) after `←` and
rejects more general `doElem`s; the new elaborator (`backward.do.legacy false`) handles
arbitrary `doElem`s.
-/

/-! ## Backward compatibility: `← term` (parsed as `doExpr`) still works in both elaborators -/

namespace LegacyTerm
set_option backward.do.legacy true

/-- info: 5 -/
#guard_msgs in
#eval show IO Nat from do
  let x ← pure (← pure 5)
  return x

/-- info: 7 -/
#guard_msgs in
#eval show IO Nat from do
  let x ← pure ((← pure 3) + (← pure 4))
  return x

end LegacyTerm

namespace NewTerm
set_option backward.do.legacy false

/-- info: 5 -/
#guard_msgs in
#eval show IO Nat from do
  let x ← pure (← pure 5)
  return x

/-- info: 7 -/
#guard_msgs in
#eval show IO Nat from do
  let x ← pure ((← pure 3) + (← pure 4))
  return x

end NewTerm

/-! ## Legacy elaborator rejects more general `doElem`s after `←` -/

namespace LegacyRejects
set_option backward.do.legacy true

/--
error: the legacy `do` elaborator only supports a term after `←`; use `set_option backward.do.legacy false` to enable the new elaborator with full `doElem` support
-/
#guard_msgs in
example : IO Nat := do
  let x ← pure (← if true then pure 5 else pure 6)
  return x

/--
error: the legacy `do` elaborator only supports a term after `←`; use `set_option backward.do.legacy false` to enable the new elaborator with full `doElem` support
-/
#guard_msgs in
example : IO Nat := do
  let x ← pure (← return 5)
  return x

end LegacyRejects

/-! ## New elaborator accepts `← <doElem>` for `doIf`, `doReturn`, and `doIf` with
`doElem`-only branches. -/

namespace NewAcceptsDoElem
set_option backward.do.legacy false

/-- info: 5 -/
#guard_msgs in
#eval show IO Nat from do
  let x ← pure (← if true then pure 5 else pure 6)
  return x

/--
warning: This `do` element and its control-flow region are dead code. Consider removing it.
---
info: true
-/
#guard_msgs in
#eval show IO Bool from do
  let x ← pure (← return true)
  return x > 7

/-- info: 4 -/
#guard_msgs in
#eval show IO Nat from do
  let mut y := 1
  let x ← pure (← if true then
    y := y + 1
    pure y
  else
    pure 0)
  return x + y

end NewAcceptsDoElem
