import Lean
/-!
Tests that `Sym.simp` produces a proper error message (instead of the internal
error `unexpected bound variable #3`) when a declaration or local hypothesis
that cannot be used as a simp theorem is provided as a parameter.
-/

/--
error: cannot use `HAdd.hAdd` as a simp theorem, it is a reducible definition or a projection, and `Sym.simp` does not support unfolding them
-/
#guard_msgs in
example : 1 + 1 = 2 := by
  sym =>
    simp [HAdd.hAdd]

/--
error: cannot use as a simp theorem, its type is not a proposition
  Nat
-/
#guard_msgs in
example (x : Nat) : x + 0 = x := by
  sym =>
    simp [x]

/--
error: cannot use `Nat` as a simp theorem, it is not a proposition nor a definition with equational theorems
-/
#guard_msgs in
example : 1 + 1 = 2 := by
  sym =>
    simp [Nat]
