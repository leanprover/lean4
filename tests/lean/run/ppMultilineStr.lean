import Lean

/-! # Multiline string formatting tests

Verify that the formatter preserves newlines inside string literals without
re-indenting continuation lines. -/

elab "#pp " cmd:command : command => Lean.logInfo cmd

-- Multiline string in a definition
/--
info: def greeting :=
  "Hello
world"
-/
#guard_msgs in
#pp
def greeting := "Hello
world"

-- Interpolated multiline string
/--
info: def greeting (name : String) :=
  s! "Hello
{name}"
-/
#guard_msgs in
#pp
def greeting (name : String) := s!"Hello
{name}"

-- String with multiple newlines
/--
info: def lines :=
  "a
b
c"
-/
#guard_msgs in
#pp
def lines := "a
b
c"

-- Multiline string inside a let binding
/--
info: def foo :=
  let s := "Hello
world"
  s
-/
#guard_msgs in
#pp
def foo :=
  let s := "Hello
world"
  s

-- Multiline string in #eval
/--
info: #eval "Hello
world"
-/
#guard_msgs in
#pp
#eval "Hello
world"
