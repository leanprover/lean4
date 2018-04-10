def f : nat → nat
| 0     := 1
| (n+1) := f n + 1

lemma ex(a : nat) : f a ≠ 0 :=
begin
  induction a,
  dsimp [f], intro x, contradiction,
  dsimp [f],
  change nat.succ (f a_n) ≠ 0,
  apply nat.succ_ne_zero
end

lemma ex2  (a : nat) : f a ≠ 0 :=
begin [smt]
  induction a,
  { intros, ematch_using [f] },
  { iterate { ematch_using [f, nat.add_one, nat.succ_ne_zero] }}
end

lemma ex3 (a : nat) : f (a+1) = f a + 1 :=
begin [smt]
  dsimp [f]
end

lemma ex4 (a : nat) : f (a+1) = f a + 1 :=
begin [smt]
  simp [f]
end

lemma ex5 (a : nat) : f (a+1) = f a + 1 :=
begin [smt]
  ematch_using [f]
end

lemma ex6 (a : nat) : f 0 = 1 :=
begin [smt]
  ematch_using [f]
end
