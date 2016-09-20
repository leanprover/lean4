open nat

protected theorem one_le_bit0 (n : ℕ) : n ≠ 0 → 1 ≤ bit0 n :=
nat.cases_on n
  (λ h, absurd rfl h)
  (λ n h,
    suffices 1 ≤ succ (succ (bit0 n)), from
      eq.symm (nat.bit0_succ_eq n) ▸ this,
    succ_le_succ (zero_le (succ (bit0 n))))
