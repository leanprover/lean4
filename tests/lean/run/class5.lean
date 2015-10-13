import logic
namespace experiment
namespace algebra
  inductive mul_struct [class] (A : Type) : Type :=
  mk : (A → A → A) → mul_struct A

  definition mul {A : Type} [s : mul_struct A] (a b : A)
  := mul_struct.rec (λ f, f) s a b

  infixl `*` := mul
end algebra

open algebra
namespace nat
  inductive nat : Type :=
  | zero : nat
  | succ : nat → nat

  constant mul : nat → nat → nat
  constant add : nat → nat → nat

  definition mul_struct [instance] : algebra.mul_struct nat
  := algebra.mul_struct.mk mul
end nat

section
  open algebra nat
  variables a b c : nat
  check a * b * c
  definition tst1 : nat := a * b * c
end

section
  open [notations] algebra
  open nat
  -- check mul_struct nat  << This is an error, we opened only the notation from algebra
  variables a b c : nat
  check a * b * c
  definition tst2 : nat := a * b * c
end

section
  open nat
  -- check mul_struct nat  << This is an error, we opened only the notation from algebra
  variables a b c : nat
  check a*b*c
  definition tst3 : nat := a*b*c
end

section
  open nat
  set_option pp.implicit true
  definition add_struct [instance] : algebra.mul_struct nat
  := algebra.mul_struct.mk add

  variables a b c : nat
  check #experiment.algebra a*b*c  -- << is open add instead of mul
  definition tst4 : nat := #experiment.algebra a*b*c
end
end experiment
