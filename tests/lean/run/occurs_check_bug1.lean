import logic data.nat data.prod

using nat prod
using decidable

variable modulo (x : ℕ) (y : ℕ) : ℕ
infixl `mod`:70 := modulo

variable gcd_aux : ℕ × ℕ → ℕ

definition gcd (x y : ℕ) : ℕ := gcd_aux (pair x y)

theorem gcd_def (x y : ℕ) : gcd x y = @ite (y = 0) (decidable_eq (pr2 (pair x y)) 0) nat x (gcd y (x mod y)) :=
sorry

theorem gcd_succ (m n : ℕ) : gcd m (succ n) = gcd (succ n) (m mod succ n) :=
trans (gcd_def _ _) (if_neg (succ_ne_zero n) _ _)
