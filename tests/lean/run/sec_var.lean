import logic

section
  parameter A : Type
  definition foo : ∀ ⦃ a b : A ⦄, a = b → a = b :=
  take a b H, H

  variable a : A
  set_option pp.implicit true
  check foo (eq.refl a)
  check foo
  check foo = (λ (a b : A) (H : a = b), H)
end

check foo = (λ (A : Type) (a b : A) (H : a = b), H)

section
  variable A : Type
  definition foo2 : ∀ ⦃ a b : A ⦄, a = b → a = b :=
  take a b H, H

  variable a : A
  set_option pp.implicit true
  check foo2 A (eq.refl a)
  check foo2
  check foo2 A = (λ (a b : A) (H : a = b), H)
end
