/-!
Tests that `fun_induction` allows naming all hypotheses of an alternative when the
combination of a `generalizing` clause, a `let` binding in the pattern, and structural
recursion previously caused a spurious "Too many variable names provided" error (#14472).
-/

def f (x : Nat) : Nat :=
  match x with
  | 0 => 0
  | n + 1 =>
    let i := 0
    f (n + i)

-- Naming all three fields (`n`, the `let`-bound `i`, and the induction hypothesis `ih`) is
-- accepted; each name refers to the expected hypothesis in the reported state.
/--
trace: case case2
n : Nat
i : Nat := 0
ih : ∀ {y : Nat}, f n = 0
y : Nat
⊢ f (n + i) = 0
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example {x y : Nat} : f x = 0 := by
  fun_induction f generalizing y with
  | case1 => simp
  | case2 n i ih => trace_state; sorry

-- Providing more names than there are fields is still rejected, now with the correct count.
/-- error: Too many variable names provided at alternative `case2`: 4 provided, but 3 expected -/
#guard_msgs in
example {x y : Nat} : f x = 0 := by
  fun_induction f generalizing y with
  | case1 => simp
  | case2 n i ih extra => sorry
