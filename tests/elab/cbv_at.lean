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
trace: h : True
⊢ True
-/
#guard_msgs in
example (h : 2 + 3 = 5) : True := by
  cbv at h
  trace_state
  trivial

-- False equation in hypothesis: goal is closed automatically
example (h : 2 + 3 = 6) : 42 = 0 := by
  cbv at h

-- `cbv at h |-` — reduces both hypothesis and target
example (h : 2 + 3 = 5) : 1 + 1 = 2 := by
  cbv at h |-

/--
trace: h₁ h₂ : True
⊢ False
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (h₁ : 2 + 3 = 5) (h₂ : 1 + 1 = 2) : False := by
  cbv at *
  trace_state
  sorry

-- Reduces hypothesis but not target when only hypothesis is specified
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (h : (fun x => x + 1) 0 = 1) : 2 + 2 = 5 := by
  cbv at h
  sorry

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
