def orderedInsert (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: l => if a < b then a :: b :: l else b :: orderedInsert a l

/-- error: Variable `x` cannot be generalized because the induction principle depends on it -/
#guard_msgs in
example : orderedInsert  x l = [] := by
  induction l using orderedInsert.induct_unfolding (a := x) generalizing x

/-- error: Variable `x` cannot be generalized because the induction principle depends on it -/
#guard_msgs in
example : orderedInsert  x l = [] := by
  fun_induction orderedInsert generalizing x

axiom foo_induct (n : Nat) {motive : Nat → Prop} (h : ∀ m, n = m): ∀ m, motive m

/-- error: Variable `n` cannot be generalized because the induction principle depends on it -/
#guard_msgs in
example (n m : Nat) : n = m := by
  induction m using foo_induct (n := n) generalizing n
