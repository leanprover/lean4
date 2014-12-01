import logic
open tactic

theorem foo (A : Type) (a b c : A) (Hab : a = b) (Hbc : b = c) : a = c :=
begin
  apply eq.trans,
  apply Hbc,
  apply Hbc,
end
