/-!
Regression test for #16285: `contradiction` (and other users of `constructorApp'?`) must not
give up on `Nat` offset terms with offset `0`, such as `0 + 0`, which still reduce to constructors.
-/

example (h : 0 + 0 = 1) : False := by contradiction
example (n : Nat) (h : 0 + 0 = n + 1) : False := by contradiction
example (n : Nat) (h : n + 1 = 0 + 0) : False := by contradiction
example (h : (0 + 0) + 0 = 2) : False := by contradiction
example (h : 2 + 2 = 3) : False := by contradiction
example (h : 0 + 1 = 0) : False := by contradiction

example (h : 0 + 0 = 1) : False := by injection h
example (h : 0 + 0 = 1) : False := by simp at h
example (h : 0 + 0 = 1) : False := by cases h

/--
error: Tactic `contradiction` failed

n : Nat
h : n + 0 = 1
⊢ False
-/
#guard_msgs in
example (n : Nat) (h : n + 0 = 1) : False := by contradiction
