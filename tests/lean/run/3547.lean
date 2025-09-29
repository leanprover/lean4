def foo : Nat → Nat
  | 0 => 0
  | n+1 => foo n
decreasing_by decreasing_tactic

/--
info: Try this:
  simp only [foo]
-/
#guard_msgs in
def foo2 : foo 2 = 0 := by
  simp? [foo]
