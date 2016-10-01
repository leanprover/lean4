open tactic

constant f : nat → nat
constant foo : ∀ n, f n = n + 1
constant zadd : ∀ n, 0 + n = n

definition ex1 (n : nat) : 0 + f n = n + 1 :=
by do
  set_basic_attribute `simp `foo,
  set_basic_attribute `simp `zadd,
  simp
