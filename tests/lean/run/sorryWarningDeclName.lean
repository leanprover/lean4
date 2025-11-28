/-!
# Sorry Warning Declaration Name Test

Tests that sorry warnings include the declaration name.
-/

-- Test: Warning includes declaration name
/--
warning: declaration `mySorryDef` uses `sorry`
-/
#guard_msgs in
def mySorryDef : Nat := sorry

-- Test: Theorem name shown
/--
warning: declaration `mySorryThm` uses `sorry`
-/
#guard_msgs in
theorem mySorryThm : True := sorry
