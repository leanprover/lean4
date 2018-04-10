variables (A : Type) (f : A → ℕ → A) [has_mul A]
open nat

theorem thm' (a : A) : ∀ m n, f a m * f a n = f a n * f a m
| 0 n := sorry
| m 0 := sorry
| (succ m) (succ n) :=
 have h : f a m * f a n = f a n * f a m, from thm' _ _,
 sorry
