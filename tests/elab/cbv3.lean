def f (n : Nat) : Nat := match n with
| 0 => 0
| (n + 1) => (f n) + 1
termination_by n

example : f 1 = f 1 := by cbv

/--
trace: ⊢ False
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : f 1 = f 2 := by
  cbv
  trace_state
  sorry

example : "hello" ++ " " ++ "world" = "hello world" := by cbv
