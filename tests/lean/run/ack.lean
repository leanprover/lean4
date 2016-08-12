open nat

definition iter (f : nat → nat) (n : nat) : nat :=
nat.rec_on n
  (f 1)
  (λ (n₁ : nat) (r : nat), f r)

definition ack (m : nat) : nat → nat :=
nat.rec_on m
  nat.succ
  (λ (m₁ : nat) (r : nat → nat), iter r)

theorem ack_0_n (n : nat) : ack 0 n = n + 1 :=
rfl

theorem ack_m_0 (m : nat) : ack (m + 1) 0 = ack m 1 :=
rfl

theorem ack_m_n (m n : nat) : ack (m + 1) (n + 1) = ack m (ack (m + 1) n) :=
rfl

example : ack 3 2 = 29 :=
rfl

example : ack 3 3 = 61 :=
rfl
