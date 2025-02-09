/-!
# Tests for `pp.coercions.types` option
-/

-- With the option off (default)
/--
info: n : Nat
h : n = 0
⊢ ↑n = 0
-/
#guard_msgs in
example (n : Nat) (h : n = 0) : (↑n : Int) = 0 := by
  trace_state
  simp [h]

-- With the option on
/--
info: n : Nat
h : n = 0
⊢ (↑n : Int) = 0
-/
#guard_msgs in
set_option pp.coercions.types true in
example (n : Nat) (h : n = 0) : (↑n : Int) = 0 := by
  trace_state
  simp [h]
