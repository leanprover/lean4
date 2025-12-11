/-!
# Tests for the `have` tactic.
-/

/-!
If the body of a `have` fails to elaborate, the tactic completes with a `sorry` for the proof.
-/
/--
error: Type mismatch
  False.elim
has type
  False → ?m.2
but is expected to have type
  True
---
trace: h : True
⊢ True
-/
#guard_msgs in
example : True := by
  have h : True :=
    False.elim
  trace_state
  assumption
