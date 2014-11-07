/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.group
Authors: Jeremy Avigad, Leonardo de Moura

Various  multiplicative and additive structures.
-/

import logic.eq logic.connectives
import data.unit data.sigma data.prod
import algebra.function algebra.binary

open eq

namespace algebra

variables {A : Type}


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
notation 1   := has_one.one
notation 0   := has_zero.zero


/- semigroup -/

structure semigroup [class] (A : Type) extends has_mul A :=
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
(comm : ∀a b, add a b = add b a)

theorem add_comm [s : add_comm_semigroup A] {a b : A} : a + b = b + a := 
!add_comm_semigroup.comm

theorem add_left_comm [s : add_comm_semigroup A] {a b c : A} : 
  a + (b + c) = b + (a + c) :=
binary.left_comm (@add_comm A s) (@add_assoc A s) a b c

theorem add_right_comm [s : add_comm_semigroup A] {a b c : A} : (a + b) + c = (a + c) + b :=
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
(mul_right_id : ∀a, mul a one = a) (mul_left_id : ∀a, mul one a = a)

theorem mul_right_id [s : monoid A] (a : A) : a * 1 = a := !monoid.mul_right_id

theorem mul_left_id [s : monoid A] (a : A) : 1 * a = a := !monoid.mul_left_id

structure comm_monoid [class] (A : Type) extends monoid A, comm_semigroup A


/- additive monoid -/

structure add_monoid [class] (A : Type) extends add_semigroup A, has_zero A :=
(add_right_id : ∀a, add a zero = a) (add_left_id : ∀a, add zero a = a)

theorem add_right_id [s : add_monoid A] (a : A) : a + 0 = a := !add_monoid.add_right_id

theorem add_left_id [s : add_monoid A] (a : A) : 0 + a = a := !add_monoid.add_left_id

structure add_comm_monoid [class] (A : Type) extends add_monoid A, add_comm_semigroup A


/- group -/

structure group [class] (A : Type) extends monoid A, has_inv A :=
(mul_left_inv : ∀a, mul (inv a) a = one) (mul_right_inv : ∀a, mul a (inv a) = one)

theorem mul_left_inv [s : group A] (a : A) : a⁻¹ * a = 1 := !group.mul_left_inv

theorem mul_right_inv [s : group A] (a : A) : a * a⁻¹ = 1 := !group.mul_right_inv

theorem mul_inv_cancel_right [s : group A] (a b : A) : a * b * b⁻¹ = a :=
calc
  a * b * b⁻¹ = a * (b * b⁻¹) : mul_assoc
    ... = a * 1 : mul_right_inv
    ... = a : mul_right_id

theorem mul_cancel_inv_right [s : group A] (a b : A) : a * b⁻¹ * b = a :=
calc
  a * b⁻¹ * b = a * (b⁻¹ * b) : mul_assoc
    ... = a * 1 : mul_left_inv
    ... = a : mul_right_id

theorem mul_inv_cancel_left [s : group A] (a b : A) : a * (a⁻¹ * b) = b :=
calc
  a * (a⁻¹ * b) = a * a⁻¹ * b : mul_assoc
    ... = 1 * b : mul_right_inv
    ... = b : mul_left_id

theorem mul_cancel_inv_left [s : group A] (a b : A) : a⁻¹ * (a * b) = b :=
calc
  a⁻¹ * (a * b) = a⁻¹ * a * b : mul_assoc
    ... = 1 * b : mul_left_inv
    ... = b : mul_left_id

theorem group.to_left_cancel_semigroup [instance] [s : group A] : left_cancel_semigroup A :=
left_cancel_semigroup.mk (@group.mul A s) (@group.mul_assoc A s)
  (take a b c,
    assume H : a * b = a * c,
    calc
      b = a⁻¹ * (a * b) : mul_cancel_inv_left
        ... = a⁻¹ * (a * c) : H
        ... = c : mul_cancel_inv_left)

theorem group.to_right_cancel_semigroup [instance] [s : group A] : right_cancel_semigroup A :=
right_cancel_semigroup.mk (@group.mul A s) (@group.mul_assoc A s)
  (take a b c,
    assume H : a * b = c * b,
    calc
      a = (a * b) * b⁻¹ : mul_inv_cancel_right
        ... = (c * b) * b⁻¹ : H
        ... = c : mul_inv_cancel_right)

structure comm_group [class] (A : Type) extends group A, comm_monoid A


/- additive group -/

structure add_group [class] (A : Type) extends add_monoid A, has_neg A :=
(add_left_inv : ∀a, add (neg a) a = zero) (add_right_inv : ∀a, add a (neg a) = zero)

theorem add_left_inv [s : add_group A] (a : A) : -a + a = 0 := !add_group.add_left_inv

theorem add_right_inv [s : add_group A] (a : A) : a + -a = 0 := !add_group.add_right_inv

theorem add_inv_cancel_right [s : add_group A] (a b : A) : a + b + -b = a :=
calc
  a + b + -b = a + (b + -b) : add_assoc
    ... = a + 0 : add_right_inv
    ... = a : add_right_id

theorem add_cancel_inv_right [s : add_group A] (a b : A) : a + -b + b = a :=
calc
  a + -b + b = a + (-b + b) : add_assoc
    ... = a + 0 : add_left_inv
    ... = a : add_right_id

theorem add_inv_cancel_left [s : add_group A] (a b : A) : a + (-a + b) = b :=
calc
  a + (-a + b) = a + -a + b : add_assoc
    ... = 0 + b : add_right_inv
    ... = b : add_left_id

theorem add_cancel_inv_left [s : add_group A] (a b : A) : -a + (a + b) = b :=
calc
  -a + (a + b) = -a + a + b : add_assoc
    ... = 0 + b : add_left_inv
    ... = b : add_left_id

theorem add_group.to_left_cancel_semigroup [instance] [s : add_group A] : 
  add_left_cancel_semigroup A :=
add_left_cancel_semigroup.mk (@add_group.add A s) (@add_group.add_assoc A s)
  (take a b c,
    assume H : a + b = a + c,
    calc
      b = -a + (a + b) : add_cancel_inv_left
        ... = -a + (a + c) : H
        ... = c : add_cancel_inv_left)

theorem add_group.to_add_right_cancel_semigroup [instance] [s : add_group A] : 
  add_right_cancel_semigroup A :=
add_right_cancel_semigroup.mk (@add_group.add A s) (@add_group.add_assoc A s)
  (take a b c,
    assume H : a + b = c + b,
    calc
      a = (a + b) + -b : add_inv_cancel_right
        ... = (c + b) + -b : H
        ... = c : add_inv_cancel_right)

structure add_comm_group [class] (A : Type) extends add_group A, add_comm_monoid A


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

end algebra

