set_option linter.unusedVariables false

example : 2 + 3 = 5 := by cbv

example : (fun x => x + 1) 3 = 4 := by cbv

def foo : Nat := 42
example : foo = 42 := by cbv

-- Bare `cbv` on non-equation goals (new: reduces and replaces target)
-- `cbv` reduces ground equalities to True/False and uses mkOfEqTrue for True
example : id (1 = 1) := by cbv

example : Nat.succ 0 = 1 ∧ Nat.succ 1 = 2 := by cbv

/--
trace: x : Nat
⊢ x = 4
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : x = 2 + 2 := by
  cbv
  trace_state
  sorry
