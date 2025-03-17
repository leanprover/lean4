/--
error: invalid field notation, type is not of the form (C ...) where C is a constant
  x✝
has type
  ?m.9
---
error: unsolved goals
case refine'_1
⊢ Sort ?u.8

case refine'_2
⊢ Sort ?u.7

case refine'_3
⊢ ?refine'_1

case refine'_4
⊢ ?refine'_1

case refine'_5
⊢ ¬(fun x => ?m.16) ?refine'_3 = (fun x => ?m.16) ?refine'_4
-/
#guard_msgs in
example : False := by
  refine' absurd (congrArg (·.1) sorry) _
