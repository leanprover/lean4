import logic

namespace algebra
  inductive mul_struct (A : Type) : Type :=
  mk : (A → A → A) → mul_struct A

  definition mul {A : Type} {s : mul_struct A} (a b : A)
  := mul_struct.rec (λ f, f) s a b

  infixl `*`:75 := mul
end algebra

namespace nat
  inductive nat : Type :=
  zero : nat,
  succ : nat → nat

  constant mul : nat → nat → nat
  constant add : nat → nat → nat

  definition mul_struct [instance] : algebra.mul_struct nat
  := algebra.mul_struct.mk mul
end nat

section
  open algebra nat
  parameters a b c : nat
  check a * b * c
  definition tst1 : nat := a * b * c
end

section
  open [notation] algebra
  open nat
  -- check mul_struct nat  << This is an error, we are open only the notation from algebra
  parameters a b c : nat
  check a * b * c
  definition tst2 : nat := a * b * c
end

section
  open nat
  -- check mul_struct nat  << This is an error, we are open only the notation from algebra
  parameters a b c : nat
  check #algebra a*b*c
  definition tst3 : nat := #algebra a*b*c
end

section
  open nat
  set_option pp.implicit true
  definition add_struct [instance] : algebra.mul_struct nat
  := algebra.mul_struct.mk add

  parameters a b c : nat
  check #algebra a*b*c  -- << is open add instead of mul
  definition tst4 : nat := #algebra a*b*c
end
