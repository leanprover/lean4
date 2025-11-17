/--
error: `grind` failed
case grind.2.2.1.1
n m a : Nat
ih : ∀ {a : Nat}, ¬a ^ 2 = 4 ^ m * n
h : a ^ 2 = 4 ^ (m + 1) * n
h_1 : ¬4 * 4 ^ m = 4 ^ m
h_2 : ¬4 * 4 ^ m = 4 ^ m
h_3 : n = 4 ^ m
h_4 : ↑a = 4
⊢ False
-/
#guard_msgs in
example {n m a : Nat} (ih : ∀ {a : Nat}, a ^ 2 = 4 ^ m * n → False)
    (h : a ^ 2 = 4 ^ (m + 1) * n) : False := by
  grind -verbose

example {n m a : Nat} (ih : ∀ {a : Nat}, a ^ 2 = 4 ^ m * n → False)
    (h : a ^ 2 = 4 ^ m * n) : False := by
  grind
