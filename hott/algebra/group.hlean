/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.group
Authors: Jeremy Avigad, Leonardo de Moura

Various multiplicative and additive structures. Partially modeled on Isabelle's library.
-/

import algebra.binary

open eq truncation binary  -- note: ⁻¹ will be overloaded

namespace path_algebra

variable {A : Type}

/- overloaded symbols -/
structure has_mul [class] (A : Type) :=
(mul : A → A → A)

structure has_add [class] (A : Type) :=
(add : A → A → A)

structure has_one [class] (A : Type) :=
(one : A)

structure has_zero [class] (A : Type) :=
(zero : A)

structure has_inv [class] (A : Type) :=
(inv : A → A)

structure has_neg [class] (A : Type) :=
(neg : A → A)

infixl `*`   := has_mul.mul
infixl `+`   := has_add.add
postfix `⁻¹` := has_inv.inv
prefix `-`   := has_neg.neg
notation 1   := !has_one.one
notation 0   := !has_zero.zero


/- semigroup -/

structure semigroup [class] (A : Type) extends has_mul A :=
(carrier_hset : is_hset A)
(mul_assoc : ∀a b c, mul (mul a b) c = mul a (mul b c))

theorem mul_assoc [s : semigroup A] (a b c : A) : a * b * c = a * (b * c) :=
!semigroup.mul_assoc

structure comm_semigroup [class] (A : Type) extends semigroup A :=
(mul_comm : ∀a b, mul a b = mul b a)

theorem mul_comm [s : comm_semigroup A] (a b : A) : a * b = b * a :=
!comm_semigroup.mul_comm

theorem mul_left_comm [s : comm_semigroup A] (a b c : A) : a * (b * c) = b * (a * c) :=
binary.left_comm (@mul_comm A s) (@mul_assoc A s) a b c

theorem mul_right_comm [s : comm_semigroup A] (a b c : A) : (a * b) * c = (a * c) * b :=
binary.right_comm (@mul_comm A s) (@mul_assoc A s) a b c

structure left_cancel_semigroup [class] (A : Type) extends semigroup A :=
(mul_left_cancel : ∀a b c, mul a b = mul a c → b = c)

theorem mul_left_cancel [s : left_cancel_semigroup A] {a b c : A} :
  a * b = a * c → b = c :=
!left_cancel_semigroup.mul_left_cancel

structure right_cancel_semigroup [class] (A : Type) extends semigroup A :=
(mul_right_cancel : ∀a b c, mul a b = mul c b → a = c)

theorem mul_right_cancel [s : right_cancel_semigroup A] {a b c : A} :
  a * b = c * b → a = c :=
!right_cancel_semigroup.mul_right_cancel


/- additive semigroup -/

structure add_semigroup [class] (A : Type) extends has_add A :=
(add_assoc : ∀a b c, add (add a b) c = add a (add b c))

theorem add_assoc [s : add_semigroup A] (a b c : A) : a + b + c = a + (b + c) :=
!add_semigroup.add_assoc

structure add_comm_semigroup [class] (A : Type) extends add_semigroup A :=
(add_comm : ∀a b, add a b = add b a)

theorem add_comm [s : add_comm_semigroup A] (a b : A) : a + b = b + a :=
!add_comm_semigroup.add_comm

theorem add_left_comm [s : add_comm_semigroup A] (a b c : A) :
  a + (b + c) = b + (a + c) :=
binary.left_comm (@add_comm A s) (@add_assoc A s) a b c

theorem add_right_comm [s : add_comm_semigroup A] (a b c : A) : (a + b) + c = (a + c) + b :=
binary.right_comm (@add_comm A s) (@add_assoc A s) a b c

structure add_left_cancel_semigroup [class] (A : Type) extends add_semigroup A :=
(add_left_cancel : ∀a b c, add a b = add a c → b = c)

theorem add_left_cancel [s : add_left_cancel_semigroup A] {a b c : A} :
  a + b = a + c → b = c :=
!add_left_cancel_semigroup.add_left_cancel

structure add_right_cancel_semigroup [class] (A : Type) extends add_semigroup A :=
(add_right_cancel : ∀a b c, add a b = add c b → a = c)

theorem add_right_cancel [s : add_right_cancel_semigroup A] {a b c : A} :
  a + b = c + b → a = c :=
!add_right_cancel_semigroup.add_right_cancel

/- monoid -/

structure monoid [class] (A : Type) extends semigroup A, has_one A :=
(mul_left_id : ∀a, mul one a = a) (mul_right_id : ∀a, mul a one = a)

theorem mul_left_id [s : monoid A] (a : A) : 1 * a = a := !monoid.mul_left_id

theorem mul_right_id [s : monoid A] (a : A) : a * 1 = a := !monoid.mul_right_id

structure comm_monoid [class] (A : Type) extends monoid A, comm_semigroup A


/- additive monoid -/

structure add_monoid [class] (A : Type) extends add_semigroup A, has_zero A :=
(add_left_id : ∀a, add zero a = a) (add_right_id : ∀a, add a zero = a)

theorem add_left_id [s : add_monoid A] (a : A) : 0 + a = a := !add_monoid.add_left_id

theorem add_right_id [s : add_monoid A] (a : A) : a + 0 = a := !add_monoid.add_right_id

structure add_comm_monoid [class] (A : Type) extends add_monoid A, add_comm_semigroup A



/- group -/

structure group [class] (A : Type) extends monoid A, has_inv A :=
(mul_left_inv : ∀a, mul (inv a) a = one)

-- Note: with more work, we could derive the axiom mul_left_id

section group

  variable [s : group A]
  include s

  theorem mul_left_inv (a : A) : a⁻¹ * a = 1 := !group.mul_left_inv

  theorem inv_mul_cancel_left (a b : A) : a⁻¹ * (a * b) = b :=
  calc
    a⁻¹ * (a * b) = a⁻¹ * a * b : mul_assoc
      ... = 1 * b : mul_left_inv
      ... = b : mul_left_id

  theorem inv_mul_cancel_right (a b : A) : a * b⁻¹ * b = a :=
  calc
    a * b⁻¹ * b = a * (b⁻¹ * b) : mul_assoc
      ... = a * 1 : mul_left_inv
    ... = a : mul_right_id

  theorem inv_unique {a b : A} (H : a * b = 1) : a⁻¹ = b :=
  calc
    a⁻¹ = a⁻¹ * 1 : mul_right_id
      ... = a⁻¹ * (a * b) : H
      ... = b : inv_mul_cancel_left

  theorem inv_one : 1⁻¹ = 1 := inv_unique (mul_left_id 1)

  theorem inv_inv (a : A) : (a⁻¹)⁻¹ = a := inv_unique (mul_left_inv a)

  theorem inv_inj {a b : A} (H : a⁻¹ = b⁻¹) : a = b :=
  calc
    a = (a⁻¹)⁻¹ : inv_inv
      ... = b : inv_unique (H⁻¹ ▹ (mul_left_inv _))

  --theorem inv_eq_inv_iff_eq (a b : A) : a⁻¹ = b⁻¹ ↔ a = b :=
  --iff.intro (assume H, inv_inj H) (assume H, congr_arg _ H)

  --theorem inv_eq_one_iff_eq_one (a b : A) : a⁻¹ = 1 ↔ a = 1 :=
  --inv_one ▹ !inv_eq_inv_iff_eq

  theorem eq_inv_imp_eq_inv {a b : A} (H : a = b⁻¹) : b = a⁻¹ :=
  H⁻¹ ▹ (inv_inv b)⁻¹

  --theorem eq_inv_iff_eq_inv (a b : A) : a = b⁻¹ ↔ b = a⁻¹ :=
  --iff.intro !eq_inv_imp_eq_inv !eq_inv_imp_eq_inv

  theorem mul_right_inv (a : A) : a * a⁻¹ = 1 :=
  calc
    a * a⁻¹ = (a⁻¹)⁻¹ * a⁻¹ : inv_inv
      ... = 1 : mul_left_inv

  theorem mul_inv_cancel_left (a b : A) : a * (a⁻¹ * b) = b :=
  calc
    a * (a⁻¹ * b) = a * a⁻¹ * b : mul_assoc
      ... = 1 * b : mul_right_inv
      ... = b : mul_left_id

  theorem mul_inv_cancel_right (a b : A) : a * b * b⁻¹ = a :=
  calc
    a * b * b⁻¹ = a * (b * b⁻¹) : mul_assoc
      ... = a * 1 : mul_right_inv
      ... = a : mul_right_id

  theorem inv_mul (a b : A) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  inv_unique
    (calc
      a * b * (b⁻¹ * a⁻¹) = a * (b * (b⁻¹ * a⁻¹)) : mul_assoc
        ... = a * a⁻¹ : mul_inv_cancel_left
        ... = 1 : mul_right_inv)

  theorem mul_inv_eq_one_imp_eq {a b : A} (H : a * b⁻¹ = 1) : a = b :=
  calc
    a = a * b⁻¹ * b : inv_mul_cancel_right
      ... = 1 * b : H
      ... = b : mul_left_id

  -- TODO: better names for the next eight theorems? (Also for additive ones.)
  theorem mul_eq_imp_eq_mul_inv {a b c : A} (H : a * b = c) : a = c * b⁻¹ :=
  H ▹ !mul_inv_cancel_right⁻¹

  theorem mul_eq_imp_eq_inv_mul {a b c : A} (H : a * b = c) : b = a⁻¹ * c :=
  H ▹ !inv_mul_cancel_left⁻¹

  theorem eq_mul_imp_inv_mul_eq {a b c : A} (H : a = b * c) : b⁻¹ * a = c :=
  H⁻¹ ▹ !inv_mul_cancel_left

  theorem eq_mul_imp_mul_inv_eq {a b c : A} (H : a = b * c) : a * c⁻¹ = b :=
  H⁻¹ ▹ !mul_inv_cancel_right

  theorem mul_inv_eq_imp_eq_mul {a b c : A} (H : a * b⁻¹ = c) : a = c * b :=
  !inv_inv ▹ (mul_eq_imp_eq_mul_inv H)

  theorem inv_mul_eq_imp_eq_mul {a b c : A} (H : a⁻¹ * b = c) : b = a * c :=
  !inv_inv ▹ (mul_eq_imp_eq_inv_mul H)

  theorem eq_inv_mul_imp_mul_eq {a b c : A} (H : a = b⁻¹ * c) : b * a = c :=
  !inv_inv ▹ (eq_mul_imp_inv_mul_eq H)

  theorem eq_mul_inv_imp_mul_eq {a b c : A} (H : a = b * c⁻¹) : a * c = b :=
  !inv_inv ▹ (eq_mul_imp_mul_inv_eq H)

  --theorem mul_eq_iff_eq_inv_mul (a b c : A) : a * b = c ↔ b = a⁻¹ * c :=
  --iff.intro mul_eq_imp_eq_inv_mul eq_inv_mul_imp_mul_eq

  --theorem mul_eq_iff_eq_mul_inv (a b c : A) : a * b = c ↔ a = c * b⁻¹ :=
  --iff.intro mul_eq_imp_eq_mul_inv eq_mul_inv_imp_mul_eq

  definition group.to_left_cancel_semigroup [instance] : left_cancel_semigroup A :=
  left_cancel_semigroup.mk (@group.mul A s) (@group.carrier_hset A s) (@group.mul_assoc A s)
    (take a b c,
      assume H : a * b = a * c,
      calc
        b = a⁻¹ * (a * b) : inv_mul_cancel_left
          ... = a⁻¹ * (a * c) : H
          ... = c : inv_mul_cancel_left)

  definition group.to_right_cancel_semigroup [instance] : right_cancel_semigroup A :=
  right_cancel_semigroup.mk (@group.mul A s) (@group.carrier_hset A s) (@group.mul_assoc A s)
    (take a b c,
      assume H : a * b = c * b,
      calc
        a = (a * b) * b⁻¹ : mul_inv_cancel_right
          ... = (c * b) * b⁻¹ : H
          ... = c : mul_inv_cancel_right)

end group

structure comm_group [class] (A : Type) extends group A, comm_monoid A


/- additive group -/

structure add_group [class] (A : Type) extends add_monoid A, has_neg A :=
(add_left_inv : ∀a, add (neg a) a = zero)

section add_group

  variables [s : add_group A]
  include s

  theorem add_left_inv (a : A) : -a + a = 0 := !add_group.add_left_inv

  theorem neg_add_cancel_left (a b : A) : -a + (a + b) = b :=
  calc
    -a + (a + b) = -a + a + b : add_assoc
      ... = 0 + b : add_left_inv
      ... = b : add_left_id

  theorem neg_add_cancel_right (a b : A) : a + -b + b = a :=
  calc
    a + -b + b = a + (-b + b) : add_assoc
      ... = a + 0 : add_left_inv
      ... = a : add_right_id

  theorem neg_unique {a b : A} (H : a + b = 0) : -a = b :=
  calc
    -a = -a + 0 : add_right_id
      ... = -a + (a + b) : H
      ... = b : neg_add_cancel_left

  theorem neg_zero : -0 = 0 := neg_unique (add_left_id 0)

  theorem neg_neg (a : A) : -(-a) = a := neg_unique (add_left_inv a)

  theorem neg_inj {a b : A} (H : -a = -b) : a = b :=
  calc
    a = -(-a) : neg_neg
      ... = b : neg_unique (H⁻¹ ▹ (add_left_inv _))

  --theorem neg_eq_neg_iff_eq (a b : A) : -a = -b ↔ a = b :=
  --iff.intro (assume H, neg_inj H) (assume H, congr_arg _ H)

  --theorem neg_eq_zero_iff_eq_zero (a b : A) : -a = 0 ↔ a = 0 :=
  --neg_zero ▹ !neg_eq_neg_iff_eq

  theorem eq_neg_imp_eq_neg {a b : A} (H : a = -b) : b = -a :=
  H⁻¹ ▹ (neg_neg b)⁻¹

  --theorem eq_neg_iff_eq_neg (a b : A) : a = -b ↔ b = -a :=
  --iff.intro !eq_neg_imp_eq_neg !eq_neg_imp_eq_neg

  theorem add_right_inv (a : A) : a + -a = 0 :=
  calc
    a + -a = -(-a) + -a : neg_neg
      ... = 0 : add_left_inv

  theorem add_neg_cancel_left (a b : A) : a + (-a + b) = b :=
  calc
    a + (-a + b) = a + -a + b : add_assoc
      ... = 0 + b : add_right_inv
      ... = b : add_left_id

  theorem add_neg_cancel_right (a b : A) : a + b + -b = a :=
  calc
    a + b + -b = a + (b + -b) : add_assoc
      ... = a + 0 : add_right_inv
      ... = a : add_right_id

  theorem neg_add (a b : A) : -(a + b) = -b + -a :=
  neg_unique
    (calc
      a + b + (-b + -a) = a + (b + (-b + -a)) : add_assoc
        ... = a + -a : add_neg_cancel_left
        ... = 0 : add_right_inv)

  theorem add_eq_imp_eq_add_neg {a b c : A} (H : a + b = c) : a = c + -b :=
  H ▹ !add_neg_cancel_right⁻¹

  theorem add_eq_imp_eq_neg_add {a b c : A} (H : a + b = c) : b = -a + c :=
  H ▹ !neg_add_cancel_left⁻¹

  theorem eq_add_imp_neg_add_eq {a b c : A} (H : a = b + c) : -b + a = c :=
  H⁻¹ ▹ !neg_add_cancel_left

  theorem eq_add_imp_add_neg_eq {a b c : A} (H : a = b + c) : a + -c = b :=
  H⁻¹ ▹ !add_neg_cancel_right

  theorem add_neg_eq_imp_eq_add {a b c : A} (H : a + -b = c) : a = c + b :=
  !neg_neg ▹ (add_eq_imp_eq_add_neg H)

  theorem neg_add_eq_imp_eq_add {a b c : A} (H : -a + b = c) : b = a + c :=
  !neg_neg ▹ (add_eq_imp_eq_neg_add H)

  theorem eq_neg_add_imp_add_eq {a b c : A} (H : a = -b + c) : b + a = c :=
  !neg_neg ▹ (eq_add_imp_neg_add_eq H)

  theorem eq_add_neg_imp_add_eq {a b c : A} (H : a = b + -c) : a + c = b :=
  !neg_neg ▹ (eq_add_imp_add_neg_eq H)

  --theorem add_eq_iff_eq_neg_add (a b c : A) : a + b = c ↔ b = -a + c :=
  --iff.intro add_eq_imp_eq_neg_add eq_neg_add_imp_add_eq

  --theorem add_eq_iff_eq_add_neg (a b c : A) : a + b = c ↔ a = c + -b :=
  --iff.intro add_eq_imp_eq_add_neg eq_add_neg_imp_add_eq

  definition add_group.to_left_cancel_semigroup [instance] :
    add_left_cancel_semigroup A :=
  add_left_cancel_semigroup.mk (@add_group.add A s) (@add_group.add_assoc A s)
    (take a b c,
      assume H : a + b = a + c,
      calc
        b = -a + (a + b) : neg_add_cancel_left
          ... = -a + (a + c) : H
          ... = c : neg_add_cancel_left)

  definition add_group.to_add_right_cancel_semigroup [instance] :
    add_right_cancel_semigroup A :=
  add_right_cancel_semigroup.mk (@add_group.add A s) (@add_group.add_assoc A s)
    (take a b c,
      assume H : a + b = c + b,
      calc
        a = (a + b) + -b : add_neg_cancel_right
          ... = (c + b) + -b : H
          ... = c : add_neg_cancel_right)

  /- minus -/

  -- TODO: derive corresponding facts for div in a field
  definition minus (a b : A) : A := a + -b

  infix `-` := minus

  theorem minus_self (a : A) : a - a = 0 := !add_right_inv

  theorem minus_add_cancel (a b : A) : a - b + b = a := !neg_add_cancel_right

  theorem add_minus_cancel (a b : A) : a + b - b = a := !add_neg_cancel_right

  theorem minus_eq_zero_imp_eq {a b : A} (H : a - b = 0) : a = b :=
  calc
    a = (a - b) + b : minus_add_cancel
      ... = 0 + b : H
      ... = b : add_left_id

  --theorem eq_iff_minus_eq_zero (a b : A) : a = b ↔ a - b = 0 :=
  --iff.intro (assume H, H ▹ !minus_self) (assume H, minus_eq_zero_imp_eq H)

  theorem zero_minus (a : A) : 0 - a = -a := !add_left_id

  theorem minus_zero (a : A) : a - 0 = a := (neg_zero⁻¹) ▹ !add_right_id

  theorem minus_neg_eq_add (a b : A) : a - (-b) = a + b := !neg_neg⁻¹ ▹ idp

  theorem neg_minus_eq (a b : A) : -(a - b) = b - a :=
  neg_unique
    (calc
      a - b + (b - a) = a - b + b - a : add_assoc
        ... = a - a : minus_add_cancel
        ... = 0 : minus_self)

  theorem add_minus_eq (a b c : A) : a + (b - c) = a + b - c := !add_assoc⁻¹

  theorem minus_add_eq_minus_swap (a b c : A) : a - (b + c) = a - c - b :=
  calc
    a - (b + c) = a + (-c - b) : neg_add
      ... = a - c - b : add_assoc

  --theorem minus_eq_iff_eq_add (a b c : A) : a - b = c ↔ a = c + b :=
  --iff.intro (assume H, add_neg_eq_imp_eq_add H) (assume H, eq_add_imp_add_neg_eq H)

  --theorem eq_minus_iff_add_eq (a b c : A) : a = b - c ↔ a + c = b :=
  --iff.intro (assume H, eq_add_neg_imp_add_eq H) (assume H, add_eq_imp_eq_add_neg H)

  --theorem minus_eq_minus_iff {a b c d : A} (H : a - b = c - d) : a = b ↔ c = d :=
  --calc
  --  a = b ↔ a - b = 0 : eq_iff_minus_eq_zero
  --    ... ↔ c - d = 0 : H ▹ !iff.refl
  --    ... ↔ c = d : iff.symm (eq_iff_minus_eq_zero c d)

end add_group

structure add_comm_group [class] (A : Type) extends add_group A, add_comm_monoid A

section add_comm_group

variable [s : add_comm_group A]
include s

  theorem minus_add_eq (a b c : A) : a - (b + c) = a - b - c :=
  !add_comm ▹ !minus_add_eq_minus_swap

  theorem neg_add_eq_minus (a b : A) : -a + b = b - a := !add_comm

  theorem neg_add_distrib (a b : A) : -(a + b) = -a + -b := !add_comm ▹ !neg_add

  theorem minus_add_right_comm (a b c : A) : a - b + c = a + c - b := !add_right_comm

  theorem minus_minus_eq (a b c : A) : a - b - c = a - (b + c) :=
  calc
    a - b - c = a + (-b + -c) : add_assoc
      ... = a + -(b + c) : neg_add_distrib
      ... = a - (b + c) : idp

  theorem add_minus_cancel_left (a b c : A) : (c + a) - (c + b) = a - b :=
  calc
    (c + a) - (c + b) = c + a - c - b : minus_add_eq
      ... = a + c - c - b : add_comm a c
      ... = a - b : add_minus_cancel


end add_comm_group


/- bundled structures -/

structure Semigroup :=
(carrier : Type) (struct : semigroup carrier)

coercion Semigroup.carrier
instance Semigroup.struct

structure CommSemigroup :=
(carrier : Type) (struct : comm_semigroup carrier)

coercion CommSemigroup.carrier
instance CommSemigroup.struct

structure Monoid :=
(carrier : Type) (struct : monoid carrier)

coercion Monoid.carrier
instance Monoid.struct

structure CommMonoid :=
(carrier : Type) (struct : comm_monoid carrier)

coercion CommMonoid.carrier
instance CommMonoid.struct

structure Group :=
(carrier : Type) (struct : group carrier)

coercion Group.carrier
instance Group.struct

structure CommGroup :=
(carrier : Type) (struct : comm_group carrier)

coercion CommGroup.carrier
instance CommGroup.struct

structure AddSemigroup :=
(carrier : Type) (struct : add_semigroup carrier)

coercion AddSemigroup.carrier
instance AddSemigroup.struct

structure AddCommSemigroup :=
(carrier : Type) (struct : add_comm_semigroup carrier)

coercion AddCommSemigroup.carrier
instance AddCommSemigroup.struct

structure AddMonoid :=
(carrier : Type) (struct : add_monoid carrier)

coercion AddMonoid.carrier
instance AddMonoid.struct

structure AddCommMonoid :=
(carrier : Type) (struct : add_comm_monoid carrier)

coercion AddCommMonoid.carrier
instance AddCommMonoid.struct

structure AddGroup :=
(carrier : Type) (struct : add_group carrier)

coercion AddGroup.carrier
instance AddGroup.struct

structure AddCommGroup :=
(carrier : Type) (struct : add_comm_group carrier)

coercion AddCommGroup.carrier
instance AddCommGroup.struct

end path_algebra
