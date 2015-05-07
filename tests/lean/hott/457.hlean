import algebra.group

open eq algebra

definition foo {A : Type} (a b c : A) (H₁ : a = c) (H₂ : c = b)  : a = b :=
begin
  apply concat,
  rotate 1,
  apply H₂,
  apply H₁
end
