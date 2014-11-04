-- Copyright (c) 2014 Jeremy Avigad. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Jeremy Avigad, Leonardo de Moura

-- algebra.group
-- =============

-- Various structures with 1, *, inv, including groups.

import logic.eq logic.connectives
import data.unit data.sigma data.prod
import algebra.function algebra.binary

open eq

namespace algebra

structure has_mul [class] (A : Type) :=
mk :: (mul : A → A → A)

structure has_one [class] (A : Type) :=
mk :: (one : A)

structure has_inv [class] (A : Type) :=
mk :: (inv : A → A)

infixl `*`   := has_mul.mul
postfix `⁻¹` := has_inv.inv
notation 1   := has_one.one

structure semigroup [class] (A : Type) extends has_mul A :=
mk :: (assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c))

set_option pp.notation false
-- set_option pp.implicit true
-- set_option pp.coercions true
print instances has_mul

section
  variables {A : Type} [s : semigroup A]
  include s
  variables a b : A

  example : a * b = semigroup.mul a b :=
  rfl

  theorem mul_assoc (a b c : A) : a * b * c = a * (b * c) :=
    semigroup.assoc a b c
end

structure comm_semigroup [class] (A : Type) extends semigroup A :=
mk :: (comm : ∀a b, mul a b = mul b a)

namespace comm_semigroup
  variables {A : Type} [s : comm_semigroup A]
  include s
  variables a b c : A
  theorem mul_comm : a * b = b * a := !comm_semigroup.comm

  theorem mul_left_comm : a * (b * c) = b * (a * c) :=
    binary.left_comm mul_comm mul_assoc a b c
end comm_semigroup

structure monoid [class] (A : Type) extends semigroup A, has_one A:=
mk :: (right_id : ∀a, mul a one = a) (left_id : ∀a, mul one a = a)

section
  variables {A : Type} [s : monoid A]
  variable a : A
  include s

  theorem mul_right_id : a * 1 = a := !monoid.right_id
  theorem mul_left_id  : 1 * a = a := !monoid.left_id
end

exit
structure comm_monoid [class] (A : Type) extends monoid A, comm_semigroup A :=
mk ::

exit

namespace comm_monoid
  section
  variables {A : Type} [s : comm_monoid A]
  variables a b c : A
  definition mul := comm_monoid.rec (λmul one assoc right_id left_id comm, mul) s a b
  definition one := comm_monoid.rec (λmul one assoc right_id left_id comm, one) s
  definition assoc : mul (mul a b) c = mul a (mul b c) :=
    comm_monoid.rec (λmul one assoc right_id left_id comm, assoc) s a b c
  definition right_id : mul a one = a :=
    comm_monoid.rec (λmul one assoc right_id left_id comm, right_id) s a
  definition left_id : mul one a = a :=
    comm_monoid.rec (λmul one assoc right_id left_id comm, left_id) s a
  definition comm : mul a b = mul b a :=
    comm_monoid.rec (λmul one assoc right_id left_id comm, comm) s a b
  end
end comm_monoid

section
  variables {A : Type} [s : comm_monoid A]
  include s
  definition comm_monoid_monoid [instance] : monoid A :=
    monoid.mk comm_monoid.mul comm_monoid.one comm_monoid.assoc
              comm_monoid.right_id comm_monoid.left_id
  definition comm_monoid_comm_semigroup [instance] : comm_semigroup A :=
    comm_semigroup.mk comm_monoid.mul comm_monoid.assoc comm_monoid.comm
end

-- bundled structures
-- ------------------

inductive Semigroup [class] : Type := mk : Π carrier : Type, semigroup carrier → Semigroup
section
  variable S : Semigroup
  definition Semigroup.carrier [coercion] : Type := Semigroup.rec (λc s, c) S
  definition Semigroup.struc   [instance] : semigroup S := Semigroup.rec (λc s, s) S
end

inductive CommSemigroup [class] : Type :=
  mk : Π carrier : Type, comm_semigroup carrier → CommSemigroup
section
  variable S : CommSemigroup
  definition CommSemigroup.carrier [coercion] : Type := CommSemigroup.rec (λc s, c) S
  definition CommSemigroup.struc [instance] : comm_semigroup S := CommSemigroup.rec (λc s, s) S
end

inductive Monoid [class] : Type := mk : Π carrier : Type, monoid carrier → Monoid
section
  variable S : Monoid
  definition Monoid.carrier [coercion] : Type := Monoid.rec (λc s, c) S
  definition Monoid.struc [instance] : monoid S := Monoid.rec (λc s, s) S
end

inductive CommMonoid : Type := mk : Π carrier : Type, comm_monoid carrier → CommMonoid
section
  variable S : CommMonoid
  definition CommMonoid.carrier [coercion] : Type := CommMonoid.rec (λc s, c) S
  definition CommMonoid.struc [instance] : comm_monoid S := CommMonoid.rec (λc s, s) S
end
end algebra

open algebra

section examples

theorem test1 {S : Semigroup} (a b c d : S) : a * (b * c) * d = a * b * (c * d) :=
calc
  a * (b * c) * d = a * b * c * d   : {symm !mul_assoc}
              ... = a * b * (c * d) : !mul_assoc

theorem test2 {M : CommSemigroup} (a b : M) : a * b = a * b := rfl

theorem test3 {M : Monoid} (a b c d : M) : a * (b * c) * d = a * b * (c * d) :=
calc
  a * (b * c) * d = a * b * c * d   : {symm !mul_assoc}
              ... = a * b * (c * d) : !mul_assoc

-- for test4b to work, we need instances at the level of the bundled structures as well
definition Monoid_Semigroup [instance] (M : Monoid) : Semigroup :=
Semigroup.mk (Monoid.carrier M) _

theorem test4 {M : Monoid} (a b c d : M) : a * (b * c) * d = a * b * (c * d) :=
test1 a b c d

theorem test5 {M : Monoid} (a b c : M) : a * 1 * b * c = a * (b * c) :=
calc
  a * 1 * b * c = a * b * c   : {!mul_right_id}
            ... = a * (b * c) : !mul_assoc

theorem test5a {M : Monoid} (a b c : M) : a * 1 * b * c = a * (b * c) :=
calc
  a * 1 * b * c = a * b * c   : {!mul_right_id}
            ... = a * (b * c) : !mul_assoc

theorem test5b {A : Type} {M : monoid A} (a b c : A) : a * 1 * b * c = a * (b * c) :=
calc
  a * 1 * b * c = a * b * c   : {!mul_right_id}
            ... = a * (b * c) : !mul_assoc

theorem test6 {M : CommMonoid} (a b c : M) : a * 1 * b * c = a * (b * c) :=
calc
  a * 1 * b * c = a * b * c   : {!mul_right_id}
            ... = a * (b * c) : !mul_assoc
end examples
