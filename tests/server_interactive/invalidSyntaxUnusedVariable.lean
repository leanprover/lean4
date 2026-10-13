/-!
Linter warnings are suppressed for commands with parse errors, so linters must not offer code actions
for them either. Here the unused variable linter would otherwise suggest `_n` and `_x` without
reporting a warning.
-/

def foo : Id Nat := do
  let mut n := 0
  for x in 0...5 do
    match x with
   --^ codeAction
  return n

/-! The code action is still offered for well-formed commands. -/

def bar : Nat :=
  let m := 0
    --^ codeAction
  1
