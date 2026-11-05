/-!
Regression test for #16285: a `Nat` offset term with offset `0` that still reduces to a constructor,
such as `0 + 0`, must be recognized as a constructor application.
-/

example (h : 0 + 0 = 1) : False := by contradiction
example (n : Nat) (h : 0 + 0 = n + 1) : False := by contradiction
example (n : Nat) (h : n + 1 = 0 + 0) : False := by contradiction
example (h : 0 + 0 + 0 = 1) : False := by contradiction
example (h : 3 + 0 = 0) : False := by contradiction
example (h : 1 + 0 = 0 + 0) : False := by contradiction
example (h : Nat.add 0 0 = 1) : False := by contradiction

-- These already worked and must keep working.
example (h : 2 + 2 = 3) : False := by contradiction
example (h : 0 + 1 = 0) : False := by contradiction

example (h : 0 + 0 = 1) : False := by injection h
example (n : Nat) (h : 0 + 0 = n + 1) : False := by injection h
example (a b : Nat) (h : (a + 1) + 0 = b + 1) : a = b := by injection h

example (n : Nat) (h : 0 + 0 = n + 1) : False := by simp only [reduceCtorEq] at h
example (n : Nat) (h : n + 1 = 0 + 0) : False := by simp only [reduceCtorEq] at h

-- `n + 0` reduces to the variable `n`, which is not a constructor application.
/--
error: Tactic `contradiction` failed

n : Nat
h : n + 0 = 1
⊢ False
-/
#guard_msgs in
example (n : Nat) (h : n + 0 = 1) : False := by contradiction
