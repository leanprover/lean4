open nat

theorem succ_ne_self : ∀ (n : ℕ), succ n ≠ n
| 0 h := absurd h (nat.succ_ne_zero 0)
