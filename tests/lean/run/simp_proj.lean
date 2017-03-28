def f (a : nat) := (a, 0)

example (a b : nat) (h : a = b) : (f a).1 = b :=
begin
  simp [f],
  guard_target a = b,
  exact h
end

example (a b : nat) (h : a = b) : (f a).1 = b :=
begin
  simp [f] {proj := ff},
  guard_target (a, 0)^.1 = b,
  exact h
end

def g (a : nat) := (λ x, x) a

example (a b : nat) (h : a = b) : g a = b :=
begin
  simp [g],
  guard_target a = b,
  exact h
end

example (a b : nat) (h : a = b) : g a = b :=
begin
  simp [g] {beta := ff},
  guard_target (λ x, x) a = b,
  exact h
end
