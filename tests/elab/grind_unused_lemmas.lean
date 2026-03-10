-- Test that grind.unusedLemmaThreshold reports activated but unused E-matching lemmas

def foo : Nat → Nat
  | 0 => 1
  | n + 1 => foo n + 1

@[grind =] theorem foo_zero : foo 0 = 1 := rfl
@[grind =] theorem foo_succ (n : Nat) : foo (n + 1) = foo n + 1 := rfl
@[grind =] theorem bar (n : Nat) : foo n + 0 = foo n := Nat.add_zero _

-- `bar` is activated but not used in the proof. With threshold=1, we get a warning.
/--
trace: [grind] grind: activated but unused E-matching lemmas
  [thm] bar ↦ 1
-/
#guard_msgs in
set_option grind.unusedLemmaThreshold 1 in
example (n : Nat) (h : n = 0) : foo n = 1 := by
  grind

-- Without the option (threshold=0), no warning.
#guard_msgs in
example (n : Nat) (h : n = 0) : foo n = 1 := by
  grind
