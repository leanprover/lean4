open nat

theorem ex1 (n : nat) : bit0 n ≠ 1 :=
nat.cases_on n
  (show 0 ≠ 1, from ne.symm nat.one_ne_zero)
  (λ m h1,
    have h2 : succ (succ (m + m)) = 1, from nat.succ_add m m ▸ h1,
    nat.no_confusion h2 (λ h3, absurd h3 (nat.succ_ne_zero (m + m))))

theorem ex2 (n : nat) : succ n ≠ 0 :=
λ h, nat.no_confusion h

theorem ex3 (n : nat) : succ (succ n) ≠ 1 :=
λ h, nat.no_confusion h (λ h, nat.no_confusion h)
