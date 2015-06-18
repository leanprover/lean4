check nat
check nat.add_zero
check nat.zero_add
check finset

open nat
example (a b : nat) : a = 0 → b = 0 → a = b :=
begin
  intros, substvars
end
