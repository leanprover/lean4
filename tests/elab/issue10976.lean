-- The variable names should be `a1` and `b1`

/--
error: Failed: `fail` tactic was invoked
a1 b1 : Nat
⊢ a1 + b1 < a1.succ + b1.succ
-/
#guard_msgs in
def f (a b : Nat) := match a with
| 0 => 0
| a1+1 => match b with
  | 0 => 0
  | b1+1 => f a1 b1
termination_by a+b
decreasing_by
  fail
