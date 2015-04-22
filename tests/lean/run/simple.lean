prelude
definition Prop : Type.{1} := Type.{0}
section
  parameter A : Type

  definition eq (a b : A) : Prop
  := ∀P : A → Prop, P a → P b

  theorem subst (P : A → Prop) (a b : A) (H1 : eq a b) (H2 : P a) : P b
  := H1 P H2

  theorem refl (a : A) : eq a a
  := λ (P : A → Prop) (H : P a), H

  theorem symm (a b : A) (H : eq a b) : eq b a
  := subst (λ x : A, eq x a) a b H (refl a)

  theorem trans (a b c : A) (H1 : eq a b) (H2 : eq b c) : eq a c
  := subst (λ x : A, eq a x) b c H2 H1
end

check subst.{1}
check refl.{1}
check symm.{1}
check trans.{1}
