open nat

theorem bit0_succ_eq (n : ℕ) : bit0 (succ n) = succ (succ (bit0 n)) :=
show succ (succ n + n) = succ (succ (n + n)), from
succ_add n n ▸ rfl

theorem bit1_eq_succ_bit0 (n : ℕ) : bit1 n = succ (bit0 n) :=
rfl

theorem bit1_succ_eq (n : ℕ) : bit1 (succ n) = succ (succ (bit1 n)) :=
eq.trans (nat.bit1_eq_succ_bit0 (succ n)) (congr_arg succ (nat.bit0_succ_eq n))

theorem succ_ne_zero (n : ℕ) : succ n ≠ 0 :=
assume h, nat.no_confusion h

theorem succ_ne_self : ∀ (n : ℕ), succ n ≠ n
| 0     h := absurd h (nat.succ_ne_zero 0)
| (n+1) h := succ_ne_self n (nat.no_confusion h (λ h, h))

theorem bit0_ne_zero : ∀ (n : ℕ), n ≠ 0 → bit0 n ≠ 0
| 0     h := absurd rfl h
| (n+1) h := nat.succ_ne_zero _

theorem bit1_ne_one : ∀ (n : ℕ), n ≠ 0 → bit1 n ≠ 1
| 0     h h1 := absurd rfl h
| (n+1) h h1 := nat.no_confusion h1 (λ h2, absurd h2 (nat.succ_ne_zero _))

theorem add_self_ne_one : ∀ (n : ℕ), n + n ≠ 1
| 0     h := nat.no_confusion h
| (n+1) h :=
  have h1 : succ (succ (n + n)) = 1, from succ_add n n ▸ h,
  nat.no_confusion h1 (λ h2, absurd h2 (nat.succ_ne_zero (n + n)))

theorem bit1_ne_bit0 : ∀ (n m : ℕ), bit1 n ≠ bit0 m
| 0     m     h := absurd h (ne.symm (nat.add_self_ne_one m))
| (n+1) 0     h :=
  have h1 : succ (bit0 (succ n)) = 0, from h,
  absurd h1 (nat.succ_ne_zero _)
| (n+1) (m+1) h :=
  have h1 : succ (succ (bit1 n)) = succ (succ (bit0 m)), from
    nat.bit0_succ_eq m ▸ nat.bit1_succ_eq n ▸ h,
  have h2 : bit1 n = bit0 m, from
    nat.no_confusion h1 (λ h2', nat.no_confusion h2' (λ h2'', h2'')),
  absurd h2 (bit1_ne_bit0 n m)
