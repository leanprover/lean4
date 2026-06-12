/-!
# Theorems should be completely opaque

Theorems should not be delta-reducible.
-/

theorem simpleThm : True := trivial

-- The `delta` tactic should not unfold theorems
/--
error: Tactic `delta` failed: did not delta reduce [simpleThm]

⊢ True
-/
#guard_msgs in
example : True := by delta simpleThm; trivial
