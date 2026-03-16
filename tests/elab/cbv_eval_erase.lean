import Std
set_option cbv.warning false
-- Use opaque constants so that cbv_eval is the ONLY way cbv can reduce them.
-- After erasure, cbv makes no progress and the goal must be closed manually.

opaque myConst : Nat
@[cbv_eval] theorem myConst_eq : myConst = 42 := sorry

-- Before erasure: cbv reduces myConst to 42 via cbv_eval
example : myConst = 42 := by cbv

-- Warning when erasing a theorem that doesn't have [cbv_eval]
theorem not_cbv (n : Nat) : n = n := rfl

/-- warning: `not_cbv` does not have the `[cbv_eval]` attribute -/
#guard_msgs in
attribute [-cbv_eval] not_cbv

-- Basic erasure (no section — permanent)
attribute [-cbv_eval] myConst_eq

-- After erasure: cbv can't reduce myConst, so the goal isn't closed
example : myConst = 42 := by
  cbv -- makes no progress
  exact myConst_eq

-- Scoping: erasure inside a section is reverted
opaque myConst2 : Nat
@[cbv_eval] theorem myConst2_eq : myConst2 = 100 := sorry

section
attribute [-cbv_eval] myConst2_eq

-- Inside section: cbv can't reduce
/--
trace: ⊢ myConst2 = 100
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : myConst2 = 100 := by
  cbv
  trace_state
  sorry
end

-- Outside section: cbv_eval is back
example : myConst2 = 100 := by cbv

-- Erasure of inverted theorem
opaque myConst3 : Nat
@[cbv_eval ←] theorem myConst3_eq : 7 = myConst3 := sorry

example : myConst3 = 7 := by cbv

section
attribute [-cbv_eval] myConst3_eq

/--
trace: ⊢ myConst3 = 7
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : myConst3 = 7 := by
  cbv
  trace_state
  sorry
end

-- Reverted after section
example : myConst3 = 7 := by cbv

-- Erasure with multiple cbv_eval rules: erase only one
opaque myFn : Nat → Nat
@[cbv_eval] theorem myFn_zero : myFn 0 = 1 := sorry
@[cbv_eval] theorem myFn_one  : myFn 1 = 0 := sorry

example : myFn 0 = 1 := by cbv
example : myFn 1 = 0 := by cbv

section
attribute [-cbv_eval] myFn_zero

-- myFn_zero is erased, so cbv can't reduce myFn 0

/--
trace: ⊢ myFn 0 = 1
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : myFn 0 = 1 := by
  cbv
  trace_state
  sorry

-- myFn_one is still active
example : myFn 1 = 0 := by cbv
end
