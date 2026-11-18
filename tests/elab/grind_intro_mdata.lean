/-!
`grind` must introduce the hypotheses of an implication even when the goal type is wrapped in
`Expr.mdata`, as `have` does (`noImplicitLambda`).
-/

/--
trace: [grind.assert] q
[grind.assert] p
[grind.assert] ¬q
-/
#guard_msgs in
set_option trace.grind.assert true in
example (p q : Prop) (hq : q) : p → q := by
  have : True := trivial
  grind
