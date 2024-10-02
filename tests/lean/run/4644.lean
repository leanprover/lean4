-- NB: well-founded recursion, so irreducible
def sorted_from_var [x: LE α] [DecidableRel x.le] (a: Array α) (i: Nat): Bool :=
  if h: i + 1 < a.size then
    have : i < a.size := Nat.lt_of_succ_lt h
    a[i] ≤ a[i+1] && sorted_from_var a (i + 1)
  else
    true
termination_by a.size - i

def check_sorted [x: LE α] [DecidableRel x.le] (a: Array α): Bool :=
  sorted_from_var a 0

/--
error: tactic 'rfl' failed, the left-hand side
  check_sorted #[0, 3, 3, 5, 8, 10, 10, 10]
is not definitionally equal to the right-hand side
  true
⊢ check_sorted #[0, 3, 3, 5, 8, 10, 10, 10] = true
-/
#guard_msgs in
example: check_sorted #[0, 3, 3, 5, 8, 10, 10, 10] = true := by
  rfl -- fails because `rfl` uses `.default` transparency, and `sorted_from_var` is marked as irreducible

/--
error: tactic 'decide' failed for proposition
  check_sorted #[0, 3, 3, 5, 8, 10, 10, 10] = true
since its 'Decidable' instance
  instDecidableEqBool (check_sorted #[0, 3, 3, 5, 8, 10, 10, 10]) true
did not reduce to 'isTrue' or 'isFalse'.

After unfolding the instances 'instDecidableEqBool' and 'Bool.decEq', reduction got stuck at the 'Decidable' instance
  match check_sorted #[0, 3, 3, 5, 8, 10, 10, 10], true with
  | false, false => isTrue ⋯
  | false, true => isFalse ⋯
  | true, false => isFalse ⋯
  | true, true => isTrue ⋯
-/
#guard_msgs in
example: check_sorted #[0, 3, 3, 5, 8, 10, 10, 10] := by
  decide -- fails because `decide` uses `.default` transparency, and `sorted_from_var` is marked as irreducible

unseal sorted_from_var in
example: check_sorted #[0, 3, 3, 5, 8, 10, 10, 10] := by
  decide -- works

example: check_sorted #[0, 3, 3, 5, 8, 10, 10, 10] := by
  with_unfolding_all decide -- should work
