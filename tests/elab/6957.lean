set_option linter.unusedVariables false

example (x : Nat) : Option Nat := do
  let ⟨a, ha⟩ ← Option.attach (guard (x < 10))
  return 0

