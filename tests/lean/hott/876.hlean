example : Σ(X : Type₀), X → unit :=
begin
  fapply sigma.mk,
  { exact unit},
  { intro x, induction x, exact unit.star }
end
