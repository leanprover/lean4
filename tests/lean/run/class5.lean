import standard

namespace algebra
  inductive mul_struct (A : Type) : Type :=
  | mk_mul_struct : (A → A → A) → mul_struct A

  class mul_struct

  definition mul [inline] {A : Type} {s : mul_struct A} (a b : A)
  := mul_struct_rec (λ f, f) s a b

  infixl `*`:75 := mul
end

namespace nat
  inductive nat : Type :=
  | zero : nat
  | succ : nat → nat

  variable mul : nat → nat → nat
  variable add : nat → nat → nat

  definition mul_struct [instance] : algebra.mul_struct nat
  := algebra.mk_mul_struct mul
end

section
  using algebra nat
  variables a b c : nat
  check a * b * c
end

section
  using [notation] algebra
  using nat
  -- check mul_struct nat  << This is an error, we are using only the notation from algebra
  variables a b c : nat
  check a * b * c
end

section
  using nat
  -- check mul_struct nat  << This is an error, we are using only the notation from algebra
  variables a b c : nat
  check #algebra a*b*c
end

section
  using nat

  definition add_struct [instance] : algebra.mul_struct nat
  := algebra.mk_mul_struct add

  variables a b c : nat
  check #algebra a*b*c  -- << is using add instead of mul
end

