@[irreducible] def f : nat → nat
| 0     := 1
| (n+1) := 2 * f n

lemma ex1 (n : nat) : f (n+1) = 2 * f n :=
begin
  fail_if_success {refl},
  simp only [f]
end

lemma ex2 (n : nat) (h : f (n+1) = 0) : 2 * f n = 0 :=
begin
  fail_if_success {exact h},
  simp only [f] at h,
  exact h
end
