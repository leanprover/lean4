/-!
# Hints for invalid tuple projections

These tests assess hints for invalid projections that may be incorrectly attempting to project the
`n`th element from a tuple where `n > 2`.
-/

def p : Nat × Nat × Nat := (3, 4, 5)
/--
error: Invalid projection: Index `3` is invalid for this structure; it must be between 1 and 2

Note: The expression
  p
has type `Nat × Nat × Nat` which has only 2 fields

Hint: n-tuples in Lean are actually nested pairs. To access the third component of this tuple, use the projection `.2.2` instead:
  3̵2̲.̲2̲
-/
#guard_msgs in
#check p.3

/--
error: Invalid projection: Index `17` is invalid for this structure; it must be between 1 and 2

Note: The expression
  p
has type `Nat × Nat × Nat` which has only 2 fields

Hint: n-tuples in Lean are actually nested pairs. For example, to access the "third" component of `(a, b, c)`, write `(a, b, c).2.2` instead of `(a, b, c).3`.
-/
#guard_msgs in
#check p.17

/--
error: Invalid projection: Index `3` is invalid for this structure; it must be between 1 and 2

Note: The expression
  p
has type `Nat × Nat × Nat` which has only 2 fields

Hint: n-tuples in Lean are actually nested pairs. To access the third component of this tuple, use the projection `.2.2` instead:
  3̵2̲.̲2̲
-/
#guard_msgs in
#check p.3.succ

/-
In prior versions of Lean, the below would erroneously produce two error messages: "structure type
expected" on the first lval resolution iteration (prior to unfolding `MyProd`), then (correctly)
"invalid index" on the second, post-unfolding iteration
-/
abbrev MyProd := Nat × Nat × Nat × Nat × Nat
def mp : MyProd := (1, 2, 3, 4, 5)
/--
error: Invalid projection: Index `4` is invalid for this structure; it must be between 1 and 2

Note: The expression
  mp
has type `Nat × Nat × Nat × Nat × Nat` which has only 2 fields

Hint: n-tuples in Lean are actually nested pairs. To access the fourth component of this tuple, use the projection `.2.2.2.1` instead:
  4̵2̲.̲2̲.̲2̲.̲1̲
-/
#guard_msgs in
#eval mp.4

-- Ensure we don't produce hints for synthetic syntax
macro "illegally_project_from_a_tuple" : term => `((true, true, false).3)

/--
error: Invalid projection: Index `3` is invalid for this structure; it must be between 1 and 2

Note: The expression
  (true, true, false)
has type `Bool × Bool × Bool` which has only 2 fields

Hint: n-tuples in Lean are actually nested pairs. For example, to access the "third" component of `(a, b, c)`, write `(a, b, c).2.2` instead of `(a, b, c).3`.
-/
#guard_msgs in
#check illegally_project_from_a_tuple
