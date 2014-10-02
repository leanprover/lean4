import logic
open eq
section
  parameter {A : Type}
  theorem T {a b : A} (H : a = b) : b = a
  := symm H
  parameters x y : A
  hypothesis H : x = y
  check T H
  check T
end

section
  parameter {A : Type}
  theorem T2 ⦃a b : A⦄ (H : a = b) : b = a
  := symm H
  parameters x y : A
  hypothesis H : x = y
  check T2 H
  check T2
end
