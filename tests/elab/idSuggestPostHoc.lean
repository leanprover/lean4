-- test extending suggestions in a different module

/--
error: Invalid field `some`: The environment does not contain `String.some`, so it is not possible to project the field `some` from an expression
  x
of type `String`

Hint: Perhaps you meant `String.contains` in place of `String.some`:
  .s̵o̵m̵e̵c̲o̲n̲t̲a̲i̲n̲s̲
-/
#guard_msgs in example (x : String) := x.some fun _ => true

attribute [suggest_for String.some] String.any

/--
error: Invalid field `some`: The environment does not contain `String.some`, so it is not possible to project the field `some` from an expression
  x
of type `String`

Hint: Perhaps you meant one of these in place of `String.some`:
  [apply] `String.contains`
  [apply] `String.any`
-/
#guard_msgs in example (x : String) := x.some fun _ => true
