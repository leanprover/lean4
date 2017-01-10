def f : nat → nat
| 0     := 1
| (n+1) := f n + 1

example (a : nat) : f a ≠ 0 :=
begin
  induction a,
  dsimp [f], intro x, contradiction,
  dsimp [f],
  change nat.succ (f a) ≠ 0,
  apply nat.succ_ne_zero
end

example (a : nat) : f a ≠ 0 :=
begin [smt]
  induction a,
  { ematch_using [f] },
  { repeat {ematch_using [f, nat.add_one_eq_succ, nat.succ_ne_zero]}}
end

example (a : nat) : f (a+1) = f a + 1 :=
begin [smt]
  dsimp [f]
end

example (a : nat) : f (a+1) = f a + 1 :=
begin [smt]
  simp [f]
end

example (a : nat) : f (a+1) = f a + 1 :=
begin [smt]
  ematch_using [f]
end

example (a : nat) : f 0 = 1 :=
begin [smt]
  ematch_using [f]
end
