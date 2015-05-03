open nat
variables (P : ℕ → Prop)

example (H : ∃n, P n) : ℕ :=
begin
  cases H with n p,
end
