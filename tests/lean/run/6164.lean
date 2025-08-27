/-!
  # `simp?` in conversion mode

  Tests that `simp?` and `dsimp?` work properly in `conv` mode: namely, that each displays the
  appropriate suggestion and applies the corresponding simplification to the focused expression.
-/

attribute [simp] Nat.two_mul

/--
info: Try this:
  simp only [Nat.two_mul]
-/
#guard_msgs in
example (n : Nat) : 123 + 2 * n = 123 + (n + n) := by
  conv =>
    enter [1, 2]
    simp?


@[simp] def foo (n : Nat) := n + 1

/--
info: Try this:
  dsimp only [foo]
-/
#guard_msgs in
example (n : Nat) : foo n = n + 1 := by
  conv =>
    lhs
    dsimp?
