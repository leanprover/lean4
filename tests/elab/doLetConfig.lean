-- Tests for letConfig support in do block let/have declarations

-- Basic let with (eq := h)
example : IO Unit := do
  let (eq := h) x := 42
  let _ : x = 42 := h
  return ()

-- Pattern let with (eq := h)
example : IO Unit := do
  let (eq := h) (a, b) := (1, 2)
  assert! a == 1
  assert! b == 2
  return ()

-- have with (eq := h)
example : IO Unit := do
  have (eq := h) x := 42
  let _ : x = 42 := h
  return ()

-- let +nondep
example : IO Unit := do
  let +nondep x := 42
  IO.println s!"{x}"

-- let +usedOnly (unused binding should be erased from body)
/--
trace: [Elab.definition.body] testUsedOnly : IO Unit :=
    pure ()
-/
#guard_msgs in
set_option trace.Elab.definition.body true in
def testUsedOnly : IO Unit := do
  let +usedOnly _x := 42
  return ()

-- let +zeta (binding should be inlined)
/--
trace: [Elab.definition.body] testZeta : IO Unit :=
    IO.println (toString 42)
-/
#guard_msgs in
set_option trace.Elab.definition.body true in
def testZeta : IO Unit := do
  let +zeta x := 42
  IO.println s!"{x}"

-- let else with (eq := h)
example (x? : Option Nat) : IO Unit := do
  let (eq := h) some x := x? | return ()
  IO.println s!"{x}"

-- Error: config options not allowed with let mut
/--
error: configuration options are not allowed with `let mut`
-/
#guard_msgs in
set_option backward.do.legacy false in
example : IO Unit := do
  let mut (eq := h) x := 42
  x := x + 1
  return ()

/--
error: configuration options are not allowed with `let mut`
-/
#guard_msgs in
set_option backward.do.legacy false in
example : IO Unit := do
  let mut +nondep x := 42
  x := x + 1
  return ()

-- Error: +postponeValue not supported in do blocks
/--
error: `+postponeValue` is not supported in `do` blocks
-/
#guard_msgs in
set_option backward.do.legacy false in
example : IO Unit := do
  let +postponeValue x := 42
  return ()

-- Error: +generalize not supported in do blocks
/--
error: `+generalize` is not supported in `do` blocks
-/
#guard_msgs in
set_option backward.do.legacy false in
example : IO Unit := do
  let +generalize x := 42
  return ()

-- Error: config options not supported with ←
/--
error: configuration options are not supported with `←`
-/
#guard_msgs in
set_option backward.do.legacy false in
example : IO Unit := do
  let (eq := h) x ← pure 42
  return ()

/--
error: configuration options are not supported with `←`
-/
#guard_msgs in
set_option backward.do.legacy false in
example : IO Unit := do
  let +nondep x ← pure 42
  return ()

-- Combining options
example : IO Unit := do
  let +nondep (eq := h) x := 42
  let _ : x = 42 := h
  return ()
