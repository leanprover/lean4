import logic
open tactic

theorem foo (A : Type) (a b c : A) : a = b → b = c → a = c ∧ c = a :=
begin
  intros [Hab, Hbc],
  apply and.intro,
  apply eq.trans,
  rotate 2,
  apply eq.trans,
  apply (eq.symm Hbc),
  apply (eq.symm Hab),
  apply Hab,
  apply Hbc,
end
