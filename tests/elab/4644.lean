def sorted_to_var [x: LE α] [DecidableRel x.le] (a: Array α) (i: Nat) (h : i + 1 < a.size) : Bool :=
  match i with
  | 0 => true
  | i+1 =>
    have : i + 1 < a.size := Nat.lt_of_succ_lt h
    a[i] ≤ a[i+1] && sorted_to_var a i this
termination_by structural i

attribute [irreducible] sorted_to_var

def check_sorted [x: LE α] [DecidableRel x.le] (a: Array α): Bool :=
  if h : a.size ≤ 1
  then true
  else sorted_to_var a (a.size - 2) (by omega)

/--
error: Tactic `rfl` failed: The left-hand side
  check_sorted #[0, 3, 3, 5, 8, 10, 10, 10]
is not definitionally equal to the right-hand side
  true

⊢ check_sorted #[0, 3, 3, 5, 8, 10, 10, 10] = true
-/
#guard_msgs in
example: check_sorted #[0, 3, 3, 5, 8, 10, 10, 10] = true := by
  rfl -- fails because `rfl` uses `.default` transparency, and `sorted_from_var` is marked as irreducible

/--
error: Tactic `decide` failed for proposition
  check_sorted #[0, 3, 3, 5, 8, 10, 10, 10] = true
because its `Decidable` instance
  instDecidableEqBool (check_sorted #[0, 3, 3, 5, 8, 10, 10, 10]) true
did not reduce to `isTrue` or `isFalse`.

After unfolding the instances `instDecidableEqBool`, `Bool.decEq`, and `Nat.decLe`, reduction got stuck at
  sorted_to_var #[0, 3, 3, 5, 8, 10, 10, 10] (#[0, 3, 3, 5, 8, 10, 10, 10].size - 2) ⋯
-/
#guard_msgs in
example: check_sorted #[0, 3, 3, 5, 8, 10, 10, 10] := by
  decide -- fails because `decide` uses `.default` transparency, and `sorted_from_var` is marked as irreducible

unseal sorted_to_var in
example: check_sorted #[0, 3, 3, 5, 8, 10, 10, 10] := by
  decide -- works

example: check_sorted #[0, 3, 3, 5, 8, 10, 10, 10] := by
  with_unfolding_all decide -- should work
