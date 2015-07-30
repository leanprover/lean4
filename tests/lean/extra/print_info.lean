import data.int
open nat int

variables a b : nat
variables i j : int

definition foo := add a i
definition f₁ := a + i

example (n : nat) : n + n = 2 * n :=
begin
  unfold [nat.add,mul],
  apply sorry
end

example (n : nat) : n + n = n + n :=
rfl

example (a₁ a₂ a₃ : nat) : a₁ = 0 → a₂ = 0 → a₃ = 0 → a₁ + a₂ + a₃ = 0 :=
assume h₁ h₂ h₃, calc
a₁ + a₂ + a₃ = 0 + a₂ + a₃ : h₁
    ...      = 0 + 0 + a₃  : h₂
    ...      = 0 + 0 + 0   : h₃
