import logic

namespace experiment
definition Type1 := Type.{1}

section
  variable {A  : Type}
  variable f   : A → A → A
  variable one : A
  variable inv : A → A
  local infixl `*`     := f
  local postfix `^-1`:100 := inv
  definition is_assoc := ∀ a b c, (a*b)*c = a*b*c
  definition is_id    := ∀ a, a*one = a
  definition is_inv   := ∀ a, a*a^-1 = one
end

namespace algebra
  inductive mul_struct [class] (A : Type) : Type :=
  mk : (A → A → A) → mul_struct A

  inductive add_struct [class] (A : Type) : Type :=
  mk : (A → A → A) → add_struct A

  definition mul  {A : Type} [s : mul_struct A] (a b : A)
  := mul_struct.rec (fun f, f) s a b

  infixl `*` := mul

  definition add  {A : Type} [s : add_struct A] (a b : A)
  := add_struct.rec (fun f, f) s a b

  infixl `+` := add
end algebra

open algebra
  inductive nat : Type :=
  | zero : nat
  | succ : nat → nat

namespace nat

  constant add : nat → nat → nat
  constant mul : nat → nat → nat

  definition is_mul_struct  [instance] : algebra.mul_struct nat
  := algebra.mul_struct.mk mul

  definition is_add_struct  [instance] : algebra.add_struct nat
  := algebra.add_struct.mk add

  definition to_nat (n : num) : nat
  := #experiment.algebra
    num.rec nat.zero (λ n, pos_num.rec (succ zero) (λ n r, r + r) (λ n r, r + r + succ zero) n) n
end nat

namespace algebra
namespace semigroup
  inductive semigroup_struct [class] (A : Type) : Type :=
  mk : Π (mul : A → A → A), is_assoc mul → semigroup_struct A

  definition mul  {A : Type} (s : semigroup_struct A) (a b : A)
  := semigroup_struct.rec (fun f h, f) s a b

  definition assoc  {A : Type} (s : semigroup_struct A) : is_assoc (mul s)
  := semigroup_struct.rec (fun f h, h) s

  definition is_mul_struct  [instance] (A : Type) [s : semigroup_struct A] : mul_struct A
  := mul_struct.mk (mul s)

  inductive semigroup : Type :=
  mk : Π (A : Type), semigroup_struct A → semigroup

  definition carrier  [coercion] (g : semigroup)
  := semigroup.rec (fun c s, c) g

  definition is_semigroup  [instance] [g : semigroup] : semigroup_struct (carrier g)
  := semigroup.rec (fun c s, s) g
end semigroup

namespace monoid
  check semigroup.mul

  inductive monoid_struct [class] (A : Type) : Type :=
  mk_monoid_struct : Π (mul : A → A → A) (id : A), is_assoc mul → is_id mul id → monoid_struct A

  definition mul  {A : Type} (s : monoid_struct A) (a b : A)
  := monoid_struct.rec (fun mul id a i, mul) s a b

  definition assoc  {A : Type} (s : monoid_struct A) : is_assoc (mul s)
  := monoid_struct.rec (fun mul id a i, a) s

  open semigroup
  definition is_semigroup_struct  [instance] (A : Type) [s : monoid_struct A] : semigroup_struct A
  := semigroup_struct.mk (mul s) (assoc s)

  inductive monoid : Type :=
  mk_monoid : Π (A : Type), monoid_struct A → monoid

  definition carrier  [coercion] (m : monoid)
  := monoid.rec (fun c s, c) m

  definition is_monoid  [instance] (m : monoid) : monoid_struct (carrier m)
  := monoid.rec (fun c s, s) m
end monoid
end algebra

section
  open algebra algebra.semigroup algebra.monoid
  variable M : monoid
  variables a b c : M
  check a*b*c*a*b*c*a*b*a*b*c*a
  check a*b
end
end experiment
