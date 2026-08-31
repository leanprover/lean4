/--
error: Tactic `apply` failed: could not unify the conclusion of `h`
  True
with the goal
  False

Note: The full type of `h` is
  1 = 1 → True

h : 1 = 1 → True
⊢ False
-/
#guard_msgs in
example (h : 1 = 1 → True) : False := by
  apply h

/--
error: Tactic `apply` failed: could not unify the type of `h`
  1 = 1 → True
with the goal
  2 = 2 → False

h : 1 = 1 → True
⊢ 2 = 2 → False
-/
#guard_msgs in
example (h : 1 = 1 → True) : 2 = 2 → False := by
  apply h

/--
error: Tactic `apply` failed: could not unify the conclusion of `h`
  1 = 1 → True
with the goal
  2 = 2 → False

Note: The full type of `h` is
  3 = 3 → 1 = 1 → True

h : 3 = 3 → 1 = 1 → True
⊢ 2 = 2 → False
-/
#guard_msgs in
example (h : 3 = 3 → 1 = 1 → True) : 2 = 2 → False := by
  apply h

/--
error: Tactic `apply` failed: could not unify the type of `h`
  True
with the goal
  False

h : True
⊢ False
-/
#guard_msgs in
example (h : True) : False := by
  apply h
