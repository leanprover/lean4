/--
error: failed to infer type of `foo`
note: all holes (e.g., `_`) in the header of a theorem are resolved before the proof is processed; information from the proof cannot be used to infer what these values should be
---
error: type of theorem 'foo' is not a proposition
  ?m.2
-/
#guard_msgs (error) in
theorem foo : _ :=
  sorry

/--
error: failed to infer type of example
note: when the resulting type of a declaration is explicitly provided, all holes (e.g., `_`) in the header are resolved before the declaration body is processed
-/
#guard_msgs (error) in
example : _ :=
  sorry

/--
error: failed to infer type of `boo`
note: when the resulting type of a declaration is explicitly provided, all holes (e.g., `_`) in the header are resolved before the declaration body is processed
-/
#guard_msgs (error) in
def boo : _ :=
  sorry

/--
error: failed to infer type of instance
note: when the resulting type of a declaration is explicitly provided, all holes (e.g., `_`) in the header are resolved before the declaration body is processed
-/
#guard_msgs (error) in
instance boo : _ :=
  sorry
