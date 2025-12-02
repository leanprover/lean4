/-!
# Tests for `exact? +grind` and `apply? +grind`

These tests verify that the `+grind` option is accepted syntactically and
enables `grind` as a fallback discharger for subgoals.
-/

/--
info: Try this:
  [apply] exact List.ne_nil_of_length_pos h
-/
#guard_msgs in
example (l : List Nat) (h : 0 < l.length) : l ≠ [] := by exact?

/--
info: Try this:
  [apply] exact List.ne_nil_of_length_pos (h trivial)
-/
#guard_msgs in
example (l : List Nat) (h : True → 0 < l.length) : l ≠ [] := by exact?

example (l : List Nat) (h : 1 < l.length) : l ≠ [] := by exact List.ne_nil_of_length_pos (by grind)

/--
info: Try this:
  [apply] exact List.ne_nil_of_length_pos (by grind)
-/
#guard_msgs in
example (l : List Nat) (h : 1 < l.length) : l ≠ [] := by
  exact? +grind

/--
info: Try this:
  [apply] exact List.ne_nil_of_length_pos (by grind)
-/
#guard_msgs in
example {P : Prop} (l : List Nat) (p : P) (h : P → 1 < l.length) : l ≠ [] := by
  exact? +grind

axiom foo (x : Nat) : x < 37 → 5 < x → x.log2 < 6

/--
info: Try this:
  [apply] exact foo x (by grind) (by grind)
-/
#guard_msgs in
example (x : Nat) (h₁ : x < 30) (h₂ : 8 < x) : x.log2 < 6 := by
  exact? +grind
