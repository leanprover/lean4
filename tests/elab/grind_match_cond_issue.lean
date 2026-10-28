/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example {n m a : Nat} (ih : ∀ {a : Nat}, a ^ 2 = 4 ^ m * n → False)
    (h : a ^ 2 = 4 ^ (m + 1) * n) : False := by
  grind -verbose

example {n m a : Nat} (ih : ∀ {a : Nat}, a ^ 2 = 4 ^ m * n → False)
    (h : a ^ 2 = 4 ^ m * n) : False := by
  grind

example {m a n : Nat} (ih : ∀ {a : Nat}, a ^ 2 = 4 ^ m * 4 * n → False)
    (h : a ^ 2 = 4 ^ (m + 1) * n) : False := by
  grind
