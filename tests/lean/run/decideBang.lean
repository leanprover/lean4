theorem foo1 : True := by decide

theorem foo2 : True := by decide!

/--
error: tactic 'decide' proved that the proposition
  False
is false
-/
#guard_msgs in
theorem foo3 : False := by decide

-- NB: Below we see error messages as they come from the kernel

/--
error: application type mismatch
  of_decide_eq_true (Eq.refl true)
argument has type
  true = true
but function has type
  decide False = true → False
-/
#guard_msgs in
theorem foo4 : False := by decide!

/--
error: application type mismatch
  Lean.ofReduceBool foo5._nativeDecide_1 true (Eq.refl true)
argument has type
  true = true
but function has type
  Lean.reduceBool foo5._nativeDecide_1 = true → foo5._nativeDecide_1 = true
-/
#guard_msgs in
theorem foo5 : False := by native_decide
