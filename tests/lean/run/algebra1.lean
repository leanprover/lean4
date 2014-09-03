import logic
open num

abbreviation Type1 := Type.{1}

section
  parameter {A  : Type}
  parameter f   : A → A → A
  parameter one : A
  parameter inv : A → A
  infixl `*`:75     := f
  postfix `^-1`:100 := inv
  definition is_assoc := ∀ a b c, (a*b)*c = a*b*c
  definition is_id    := ∀ a, a*one = a
  definition is_inv   := ∀ a, a*a^-1 = one
end

namespace algebra
  inductive mul_struct (A : Type) : Type :=
  mk_mul_struct : (A → A → A) → mul_struct A

  inductive add_struct (A : Type) : Type :=
  mk_add_struct : (A → A → A) → add_struct A

  definition mul [inline] {A : Type} {s : mul_struct A} (a b : A)
  := mul_struct_rec (fun f, f) s a b

  infixl `*`:75 := mul

  definition add [inline] {A : Type} {s : add_struct A} (a b : A)
  := add_struct_rec (fun f, f) s a b

  infixl `+`:65 := add
end algebra

namespace nat
  inductive nat : Type :=
  zero : nat,
  succ : nat → nat

  variable add : nat → nat → nat
  variable mul : nat → nat → nat

  definition is_mul_struct [inline] [instance] : algebra.mul_struct nat
  := algebra.mk_mul_struct mul

  definition is_add_struct [inline] [instance] : algebra.add_struct nat
  := algebra.mk_add_struct add

  definition to_nat (n : num) : nat
  := #algebra
    num_rec zero (λ n, pos_num_rec (succ zero) (λ n r, r + r) (λ n r, r + r + succ zero) n) n
end nat

namespace algebra
namespace semigroup
  inductive semigroup_struct (A : Type) : Type :=
  mk_semigroup_struct : Π (mul : A → A → A), is_assoc mul → semigroup_struct A

  definition mul [inline] {A : Type} (s : semigroup_struct A) (a b : A)
  := semigroup_struct_rec (fun f h, f) s a b

  definition assoc [inline] {A : Type} (s : semigroup_struct A) : is_assoc (mul s)
  := semigroup_struct_rec (fun f h, h) s

  definition is_mul_struct [inline] [instance] (A : Type) (s : semigroup_struct A) : mul_struct A
  := mk_mul_struct (mul s)

  inductive semigroup : Type :=
  mk_semigroup : Π (A : Type), semigroup_struct A → semigroup

  definition carrier [inline] [coercion] (g : semigroup)
  := semigroup_rec (fun c s, c) g

  definition is_semigroup [inline] [instance] (g : semigroup) : semigroup_struct (carrier g)
  := semigroup_rec (fun c s, s) g
end semigroup

namespace monoid
  check semigroup.mul

  inductive monoid_struct (A : Type) : Type :=
  mk_monoid_struct : Π (mul : A → A → A) (id : A), is_assoc mul → is_id mul id → monoid_struct A

  definition mul [inline] {A : Type} (s : monoid_struct A) (a b : A)
  := monoid_struct_rec (fun mul id a i, mul) s a b

  definition assoc [inline] {A : Type} (s : monoid_struct A) : is_assoc (mul s)
  := monoid_struct_rec (fun mul id a i, a) s

  open semigroup
  definition is_semigroup_struct [inline] [instance] (A : Type) (s : monoid_struct A) : semigroup_struct A
  := mk_semigroup_struct (mul s) (assoc s)

  inductive monoid : Type :=
  mk_monoid : Π (A : Type), monoid_struct A → monoid

  definition carrier [inline] [coercion] (m : monoid)
  := monoid_rec (fun c s, c) m

  definition is_monoid [inline] [instance] (m : monoid) : monoid_struct (carrier m)
  := monoid_rec (fun c s, s) m
end monoid
end algebra

section
  open algebra algebra.semigroup algebra.monoid
  variable M : monoid
  variables a b c : M
  check a*b*c*a*b*c*a*b*a*b*c*a
  check a*b
end
