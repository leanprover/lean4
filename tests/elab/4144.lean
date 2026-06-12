/--
error: Invalid projection: Type of
  x✝
is not known; cannot resolve projection `1`
---
error: unsolved goals
case refine'_1
⊢ Sort ?u.4

case refine'_2
⊢ Sort ?u.3

case refine'_3
⊢ ?refine'_1

case refine'_4
⊢ ?refine'_1

case refine'_5
⊢ ¬?m.10 ?refine'_3 = ?m.10 ?refine'_4
-/
#guard_msgs in
example : False := by
  refine' absurd (congrArg (·.1) sorry) _
