/-!
Tests the `suggest_for` annotations on `ite_eq_left`, `ite_eq_right`, `dite_eq_left`, and
`dite_eq_right`, which suggest these lemmas for plausible-but-nonexistent names like `ite_pos`.
-/

/--
error: Unknown identifier `ite_pos`

Hint: Perhaps you meant `ite_eq_left` in place of `ite_pos`:
  [apply] `ite_eq_left`
-/
#guard_msgs in
#check ite_pos

/--
error: Unknown identifier `ite_of_pos`

Hint: Perhaps you meant `ite_eq_left` in place of `ite_of_pos`:
  [apply] `ite_eq_left`
-/
#guard_msgs in
#check ite_of_pos

/--
error: Unknown identifier `ite_neg`

Hint: Perhaps you meant `ite_eq_right` in place of `ite_neg`:
  [apply] `ite_eq_right`
-/
#guard_msgs in
#check ite_neg

/--
error: Unknown identifier `ite_of_neg`

Hint: Perhaps you meant `ite_eq_right` in place of `ite_of_neg`:
  [apply] `ite_eq_right`
-/
#guard_msgs in
#check ite_of_neg

/--
error: Unknown identifier `dite_pos`

Hint: Perhaps you meant `dite_eq_left` in place of `dite_pos`:
  [apply] `dite_eq_left`
-/
#guard_msgs in
#check dite_pos

/--
error: Unknown identifier `dite_of_pos`

Hint: Perhaps you meant `dite_eq_left` in place of `dite_of_pos`:
  [apply] `dite_eq_left`
-/
#guard_msgs in
#check dite_of_pos

/--
error: Unknown identifier `dite_neg`

Hint: Perhaps you meant `dite_eq_right` in place of `dite_neg`:
  [apply] `dite_eq_right`
-/
#guard_msgs in
#check dite_neg

/--
error: Unknown identifier `dite_of_neg`

Hint: Perhaps you meant `dite_eq_right` in place of `dite_of_neg`:
  [apply] `dite_eq_right`
-/
#guard_msgs in
#check dite_of_neg
