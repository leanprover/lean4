/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.group
Authors: Jeremy Avigad, Leonardo de Moura

Various multiplicative and additive structures. Partially modeled on Isabelle's library.
-/

import algebra.binary

open eq is_trunc binary  -- note: ⁻¹ will be overloaded

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

--a second notation for the inverse, which is not overloaded
postfix [parsing-only] `⁻¹ᵍ`:std.prec.max_plus := has_inv.inv


/- semigroup -/

structure semigroup [class] (A : Type) extends has_mul A :=
(carrier_hset : is_hset A)
(mul_assoc : ∀a b c, mul (mul a b) c = mul a (mul b c))

attribute semigroup.carrier_hset [instance]

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
(one_mul : ∀a, mul one a = a) (mul_one : ∀a, mul a one = a)

theorem one_mul [s : monoid A] (a : A) : 1 * a = a := !monoid.one_mul

theorem mul_one [s : monoid A] (a : A) : a * 1 = a := !monoid.mul_one

structure comm_monoid [class] (A : Type) extends monoid A, comm_semigroup A


/- additive monoid -/

structure add_monoid [class] (A : Type) extends add_semigroup A, has_zero A :=
(zero_add : ∀a, add zero a = a) (add_zero : ∀a, add a zero = a)

theorem zero_add [s : add_monoid A] (a : A) : 0 + a = a := !add_monoid.zero_add

theorem add_zero [s : add_monoid A] (a : A) : a + 0 = a := !add_monoid.add_zero

structure add_comm_monoid [class] (A : Type) extends add_monoid A, add_comm_semigroup A



/- group -/

structure group [class] (A : Type) extends monoid A, has_inv A :=
(mul_left_inv : ∀a, mul (inv a) a = one)

-- Note: with more work, we could derive the axiom one_mul

section group

  variable [s : group A]
  include s

  theorem mul_left_inv (a : A) : a⁻¹ * a = 1 := !group.mul_left_inv

  theorem inv_mul_cancel_left (a b : A) : a⁻¹ * (a * b) = b :=
  calc
    a⁻¹ * (a * b) = a⁻¹ * a * b : mul_assoc
      ... = 1 * b : mul_left_inv
      ... = b : one_mul

  theorem inv_mul_cancel_right (a b : A) : a * b⁻¹ * b = a :=
  calc
    a * b⁻¹ * b = a * (b⁻¹ * b) : mul_assoc
      ... = a * 1 : mul_left_inv
    ... = a : mul_one

  theorem inv_eq_of_mul_eq_one {a b : A} (H : a * b = 1) : a⁻¹ = b :=
  calc
    a⁻¹ = a⁻¹ * 1 : mul_one
      ... = a⁻¹ * (a * b) : H
      ... = b : inv_mul_cancel_left

  theorem inv_one : 1⁻¹ = 1 := inv_eq_of_mul_eq_one (one_mul 1)

  theorem inv_inv (a : A) : (a⁻¹)⁻¹ = a := inv_eq_of_mul_eq_one (mul_left_inv a)

  theorem inv_inj {a b : A} (H : a⁻¹ = b⁻¹) : a = b :=
  calc
    a = (a⁻¹)⁻¹ : inv_inv
      ... = b : inv_eq_of_mul_eq_one (H⁻¹ ▹ (mul_left_inv _))

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
      ... = b : one_mul

  theorem mul_inv_cancel_right (a b : A) : a * b * b⁻¹ = a :=
  calc
    a * b * b⁻¹ = a * (b * b⁻¹) : mul_assoc
      ... = a * 1 : mul_right_inv
      ... = a : mul_one

  theorem inv_mul (a b : A) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  inv_eq_of_mul_eq_one
    (calc
      a * b * (b⁻¹ * a⁻¹) = a * (b * (b⁻¹ * a⁻¹)) : mul_assoc
        ... = a * a⁻¹ : mul_inv_cancel_left
        ... = 1 : mul_right_inv)

  theorem eq_of_mul_inv_eq_one {a b : A} (H : a * b⁻¹ = 1) : a = b :=
  calc
    a = a * b⁻¹ * b : inv_mul_cancel_right
      ... = 1 * b : H
      ... = b : one_mul

  -- TODO: better names for the next eight theorems? (Also for additive ones.)
  theorem eq_mul_inv_of_mul_eq {a b c : A} (H : a * b = c) : a = c * b⁻¹ :=
  H ▹ !mul_inv_cancel_right⁻¹

  theorem eq_inv_mul_of_mul_eq {a b c : A} (H : a * b = c) : b = a⁻¹ * c :=
  H ▹ !inv_mul_cancel_left⁻¹

  theorem inv_mul_eq_of_eq_mul {a b c : A} (H : a = b * c) : b⁻¹ * a = c :=
  H⁻¹ ▹ !inv_mul_cancel_left

  theorem mul_inv_eq_of_eq_mul {a b c : A} (H : a = b * c) : a * c⁻¹ = b :=
  H⁻¹ ▹ !mul_inv_cancel_right

  theorem eq_mul_of_mul_inv_eq {a b c : A} (H : a * b⁻¹ = c) : a = c * b :=
  !inv_inv ▹ (eq_mul_inv_of_mul_eq H)

  theorem eq_mul_of_inv_mul_eq {a b c : A} (H : a⁻¹ * b = c) : b = a * c :=
  !inv_inv ▹ (eq_inv_mul_of_mul_eq H)

  theorem mul_eq_of_eq_inv_mul {a b c : A} (H : a = b⁻¹ * c) : b * a = c :=
  !inv_inv ▹ (inv_mul_eq_of_eq_mul H)

  theorem mul_eq_of_eq_mul_inv {a b c : A} (H : a = b * c⁻¹) : a * c = b :=
  !inv_inv ▹ (mul_inv_eq_of_eq_mul H)

  --theorem mul_eq_iff_eq_inv_mul (a b c : A) : a * b = c ↔ b = a⁻¹ * c :=
  --iff.intro eq_inv_mul_of_mul_eq mul_eq_of_eq_inv_mul

  --theorem mul_eq_iff_eq_mul_inv (a b c : A) : a * b = c ↔ a = c * b⁻¹ :=
  --iff.intro eq_mul_inv_of_mul_eq mul_eq_of_eq_mul_inv

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
      ... = b : zero_add

  theorem neg_add_cancel_right (a b : A) : a + -b + b = a :=
  calc
    a + -b + b = a + (-b + b) : add_assoc
      ... = a + 0 : add_left_inv
      ... = a : add_zero

  theorem neq_eq_of_add_eq_zero {a b : A} (H : a + b = 0) : -a = b :=
  calc
    -a = -a + 0 : add_zero
      ... = -a + (a + b) : H
      ... = b : neg_add_cancel_left

  theorem neg_zero : -0 = 0 := neq_eq_of_add_eq_zero (zero_add 0)

  theorem neg_neg (a : A) : -(-a) = a := neq_eq_of_add_eq_zero (add_left_inv a)

  theorem neg_inj {a b : A} (H : -a = -b) : a = b :=
  calc
    a = -(-a) : neg_neg
      ... = b : neq_eq_of_add_eq_zero (H⁻¹ ▹ (add_left_inv _))

  --theorem neg_eq_neg_iff_eq (a b : A) : -a = -b ↔ a = b :=
  --iff.intro (assume H, neg_inj H) (assume H, congr_arg _ H)

  --theorem neg_eq_zero_iff_eq_zero (a b : A) : -a = 0 ↔ a = 0 :=
  --neg_zero ▹ !neg_eq_neg_iff_eq

  theorem eq_neq_of_eq_neg {a b : A} (H : a = -b) : b = -a :=
  H⁻¹ ▹ (neg_neg b)⁻¹

  --theorem eq_neg_iff_eq_neg (a b : A) : a = -b ↔ b = -a :=
  --iff.intro !eq_neq_of_eq_neg !eq_neq_of_eq_neg

  theorem add_right_inv (a : A) : a + -a = 0 :=
  calc
    a + -a = -(-a) + -a : neg_neg
      ... = 0 : add_left_inv

  theorem add_neg_cancel_left (a b : A) : a + (-a + b) = b :=
  calc
    a + (-a + b) = a + -a + b : add_assoc
      ... = 0 + b : add_right_inv
      ... = b : zero_add

  theorem add_neg_cancel_right (a b : A) : a + b + -b = a :=
  calc
    a + b + -b = a + (b + -b) : add_assoc
      ... = a + 0 : add_right_inv
      ... = a : add_zero

  theorem neq_add_rev (a b : A) : -(a + b) = -b + -a :=
  neq_eq_of_add_eq_zero
    (calc
      a + b + (-b + -a) = a + (b + (-b + -a)) : add_assoc
        ... = a + -a : add_neg_cancel_left
        ... = 0 : add_right_inv)

  theorem eq_add_neq_of_add_eq {a b c : A} (H : a + b = c) : a = c + -b :=
  H ▹ !add_neg_cancel_right⁻¹

  theorem eq_neg_add_of_add_eq {a b c : A} (H : a + b = c) : b = -a + c :=
  H ▹ !neg_add_cancel_left⁻¹

  theorem neg_add_eq_of_eq_add {a b c : A} (H : a = b + c) : -b + a = c :=
  H⁻¹ ▹ !neg_add_cancel_left

  theorem add_neg_eq_of_eq_add {a b c : A} (H : a = b + c) : a + -c = b :=
  H⁻¹ ▹ !add_neg_cancel_right

  theorem eq_add_of_add_neg_eq {a b c : A} (H : a + -b = c) : a = c + b :=
  !neg_neg ▹ (eq_add_neq_of_add_eq H)

  theorem eq_add_of_neg_add_eq {a b c : A} (H : -a + b = c) : b = a + c :=
  !neg_neg ▹ (eq_neg_add_of_add_eq H)

  theorem add_eq_of_eq_neg_add {a b c : A} (H : a = -b + c) : b + a = c :=
  !neg_neg ▹ (neg_add_eq_of_eq_add H)

  theorem add_eq_of_eq_add_neg {a b c : A} (H : a = b + -c) : a + c = b :=
  !neg_neg ▹ (add_neg_eq_of_eq_add H)

  --theorem add_eq_iff_eq_neg_add (a b c : A) : a + b = c ↔ b = -a + c :=
  --iff.intro eq_neg_add_of_add_eq add_eq_of_eq_neg_add

  --theorem add_eq_iff_eq_add_neg (a b c : A) : a + b = c ↔ a = c + -b :=
  --iff.intro eq_add_neq_of_add_eq add_eq_of_eq_add_neg

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

  /- sub -/

  -- TODO: derive corresponding facts for div in a field
  definition sub [reducible] (a b : A) : A := a + -b

  infix `-` := sub

  theorem sub_self (a : A) : a - a = 0 := !add_right_inv

  theorem sub_add_cancel (a b : A) : a - b + b = a := !neg_add_cancel_right

  theorem add_sub_cancel (a b : A) : a + b - b = a := !add_neg_cancel_right

  theorem eq_of_sub_eq_zero {a b : A} (H : a - b = 0) : a = b :=
  calc
    a = (a - b) + b : sub_add_cancel
      ... = 0 + b : H
      ... = b : zero_add

  --theorem eq_iff_minus_eq_zero (a b : A) : a = b ↔ a - b = 0 :=
  --iff.intro (assume H, H ▹ !sub_self) (assume H, eq_of_sub_eq_zero H)

  theorem zero_sub (a : A) : 0 - a = -a := !zero_add

  theorem sub_zero (a : A) : a - 0 = a := neg_zero⁻¹ ▹ !add_zero

  theorem sub_neg_eq_add (a b : A) : a - (-b) = a + b := !neg_neg ▹ idp

  theorem neg_sub (a b : A) : -(a - b) = b - a :=
  neq_eq_of_add_eq_zero
    (calc
      a - b + (b - a) = a - b + b - a : add_assoc
        ... = a - a : sub_add_cancel
        ... = 0 : sub_self)

  theorem add_sub (a b c : A) : a + (b - c) = a + b - c := !add_assoc⁻¹

  theorem sub_add_eq_sub_sub_swap (a b c : A) : a - (b + c) = a - c - b :=
  calc
    a - (b + c) = a + (-c - b) : neq_add_rev
      ... = a - c - b : add_assoc

  --theorem minus_eq_iff_eq_add (a b c : A) : a - b = c ↔ a = c + b :=
  --iff.intro (assume H, eq_add_of_add_neg_eq H) (assume H, add_neg_eq_of_eq_add H)

  --theorem eq_minus_iff_add_eq (a b c : A) : a = b - c ↔ a + c = b :=
  --iff.intro (assume H, add_eq_of_eq_add_neg H) (assume H, eq_add_neq_of_add_eq H)

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

  theorem sub_add_eq_sub_sub (a b c : A) : a - (b + c) = a - b - c :=
  !add_comm ▹ !sub_add_eq_sub_sub_swap

  theorem neq_add_eq_sub (a b : A) : -a + b = b - a := !add_comm

  theorem neg_add_distrib (a b : A) : -(a + b) = -a + -b := !add_comm ▹ !neq_add_rev

  theorem sub_add_eq_add_sub (a b c : A) : a - b + c = a + c - b := !add_right_comm

  theorem sub_sub (a b c : A) : a - b - c = a - (b + c) :=
  calc
    a - b - c = a + (-b + -c) : add_assoc
      ... = a + -(b + c) : neg_add_distrib
      ... = a - (b + c) : idp

  theorem add_sub_add_left_eq_sub (a b c : A) : (c + a) - (c + b) = a - b :=
  calc
    (c + a) - (c + b) = c + a - c - b : sub_add_eq_sub_sub
      ... = a + c - c - b : add_comm a c
      ... = a - b : add_sub_cancel


end add_comm_group


/- bundled structures -/
structure Semigroup :=
(carrier : Type) (struct : semigroup carrier)

attribute Semigroup.carrier [coercion]
attribute Semigroup.struct [instance]

structure CommSemigroup :=
(carrier : Type) (struct : comm_semigroup carrier)

attribute CommSemigroup.carrier [coercion]
attribute CommSemigroup.struct [instance]

structure Monoid :=
(carrier : Type) (struct : monoid carrier)

attribute Monoid.carrier [coercion]
attribute Monoid.struct [instance]

structure CommMonoid :=
(carrier : Type) (struct : comm_monoid carrier)

attribute CommMonoid.carrier [coercion]
attribute CommMonoid.struct [instance]

structure Group :=
(carrier : Type) (struct : group carrier)

attribute Group.carrier [coercion]
attribute Group.struct [instance]

structure CommGroup :=
(carrier : Type) (struct : comm_group carrier)

attribute CommGroup.carrier [coercion]
attribute CommGroup.struct [instance]

structure AddSemigroup :=
(carrier : Type) (struct : add_semigroup carrier)

attribute AddSemigroup.carrier [coercion]
attribute AddSemigroup.struct [instance]

structure AddCommSemigroup :=
(carrier : Type) (struct : add_comm_semigroup carrier)

attribute AddCommSemigroup.carrier [coercion]
attribute AddCommSemigroup.struct [instance]

structure AddMonoid :=
(carrier : Type) (struct : add_monoid carrier)

attribute AddMonoid.carrier [coercion]
attribute AddMonoid.struct [instance]

structure AddCommMonoid :=
(carrier : Type) (struct : add_comm_monoid carrier)

attribute AddCommMonoid.carrier [coercion]
attribute AddCommMonoid.struct [instance]

structure AddGroup :=
(carrier : Type) (struct : add_group carrier)

attribute AddGroup.carrier [coercion]
attribute AddGroup.struct [instance]

structure AddCommGroup :=
(carrier : Type) (struct : add_comm_group carrier)

attribute AddCommGroup.carrier [coercion]
attribute AddCommGroup.struct [instance]

end path_algebra
