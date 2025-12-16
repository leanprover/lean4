/-! Regression tests from working on PR 11695 -/

set_option linter.unusedVariables false

-- set_option trace.Meta.Match.match true

def dependent : (n : Nat) → (m : Fin n) → Nat
 | 0, i => Fin.elim0 i
 | .succ 0, 0 => 0
 | .succ (.succ n), 0 => 1
 | .succ (.succ n), ⟨.succ m, h⟩ => 2
