import logic
open eq
section
  variable {A : Type}
  theorem T {a b : A} (H : a = b) : b = a
  := symm H
  variables x y : A
  variable H : x = y
  check T H
  check T
end

section
  variable {A : Type}
  theorem T2 ⦃a b : A⦄ (H : a = b) : b = a
  := symm H
  variables x y : A
  variable H : x = y
  check T2 H
  check T2
end
