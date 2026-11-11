/-! A `finally` block cannot reassign the `mut` variables in scope at the `try`. -/

/--
error: A `finally` block cannot reassign the `mut` variables `s`, `t`.
-/
#guard_msgs in
def reassignArrowAndLoop : IO Nat := do
  let mut s := 0
  let mut t := 0
  try
    s := 1
  catch _ =>
    s := 2
  finally
    t ← pure 3
    for i in [1, 2] do
      s := s + i
  return s + t

/--
error: A `finally` block does not support `break`, `continue` or `return`.
-/
#guard_msgs in
def breakInFinally : IO Unit := do
  for _ in [1, 2] do
    try
      pure ()
    finally
      break

/--
info: finally sees 0, local 10
---
info: 1
-/
#guard_msgs in
#eval show IO Nat from do
  let mut s := 0
  try
    s := 1
  finally
    let mut y := 0
    for i in [1, 2, 3, 4] do
      y := y + i
    IO.println s!"finally sees {s}, local {y}"
  return s

/-! The two errors below are reported at the `finally` keyword. -/

def reassign : IO Nat := do
  let mut s := 0
  try
    s := 1
  finally
    IO.println s!"finally sees {s}"
    s := s + 100
  return s

def noMonadFinally : Option Nat := do
  try
    pure 1
  finally
    pure ()
