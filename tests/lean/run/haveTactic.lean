/-!
# Tests for the `have` tactic.
-/

/-!
If the body of a `have` fails to elaborate, the tactic completes with a `sorry` for the proof.
-/
/--
error: type mismatch
  False.elim
has type
  False → ?m.6 : Sort ?u.5
but is expected to have type
  True : Prop
---
info: h : True
⊢ True
-/
#guard_msgs in
example : True := by
  have h : True :=
    False.elim
  trace_state
  assumption
