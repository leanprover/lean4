prelude
definition Prop : PType.{1} := PType.{0}
section
  parameter A : PType*

  definition Eq (a b : A) : Prop
  := ∀P : A → Prop, P a → P b

  theorem subst (P : A → Prop) (a b : A) (H1 : Eq a b) (H2 : P a) : P b
  := H1 P H2

  theorem refl (a : A) : Eq a a
  := λ (P : A → Prop) (H : P a), H

  theorem symm (a b : A) (H : Eq a b) : Eq b a
  := subst (λ x : A, Eq x a) a b H (refl a)

  theorem trans (a b c : A) (H1 : Eq a b) (H2 : Eq b c) : Eq a c
  := subst (λ x : A, Eq a x) b c H2 H1
end

check subst.{1}
check refl.{1}
check symm.{1}
check trans.{1}
