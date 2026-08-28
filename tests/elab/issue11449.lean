opaque double : Nat → Nat

inductive Parity : Nat -> Type
| even (n) : Parity (double n)
| odd  (n) : Parity (Nat.succ (double n))

example
  (motive : (x : Nat) → Parity x → Sort u_1)
  (h_2 : (j : Nat) → motive (double j) (Parity.even j))
  (j n : Nat)
  (heq_1 : double n = double j)
  (heq_2 : Parity.even n ≍ Parity.even j):
  h_2 n ≍ h_2 j := by
  grind

example
  (motive : (x : Nat) → Parity x → Sort u_1)
  (h_2 : (j : Nat) → motive (double j) (Parity.even j))
  (j n : Nat)
  (heq_1 : double n = double j)
  (heq_2 : Parity.even n ≍ Parity.even j):
  h_2 n ≍ h_2 j := by
  apply Parity.noConfusion heq_1 heq_2
  intro hnj
  subst hnj
  rfl
