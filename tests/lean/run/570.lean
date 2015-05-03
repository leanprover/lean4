open nat
variables (P : ℕ → Prop)

example (H1 : ∃n, P n) : ∃n, P n :=
begin
  cases H1 with n p,
  apply (exists.intro n),
  assumption
end

example (H1 : ∃n, P n) : ∃n, P n :=
begin
  cases H1 with n p,
  existsi n,
  assumption
end
