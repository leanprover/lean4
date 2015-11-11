-- Copyright (c) 2014 Jeremy Avigad. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Jeremy Avigad, Leonardo de Moura

-- algebra.group
-- =============

-- Various structures with 1, *, inv, including groups.

import logic.eq
import data.unit data.sigma data.prod
import algebra.binary

open eq

namespace algebra

structure has_mul [class] (A : Type) :=
(mul : A → A → A)

structure has_one [class] (A : Type) :=
(one : A)

structure has_inv [class] (A : Type) :=
(inv : A → A)

infixl `*`   := has_mul.mul
postfix `⁻¹` := has_inv.inv
notation 1   := !has_one.one

structure semigroup [class] (A : Type) extends has_mul A :=
(assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c))

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
(comm : ∀a b, mul a b = mul b a)

namespace comm_semigroup
  variables {A : Type} [s : comm_semigroup A]
  include s
  variables a b c : A
  theorem mul_comm : a * b = b * a := !comm_semigroup.comm

  theorem mul_left_comm : a * (b * c) = b * (a * c) :=
    binary.left_comm mul_comm mul_assoc a b c
end comm_semigroup

structure monoid [class] (A : Type) extends semigroup A, has_one A :=
(right_id : ∀a, mul a one = a) (left_id : ∀a, mul one a = a)

section
  variables {A : Type} [s : monoid A]
  variable a : A
  include s

  theorem mul_right_id : a * 1 = a := !monoid.right_id
  theorem mul_left_id  : 1 * a = a := !monoid.left_id
end

structure comm_monoid [class] (A : Type) extends monoid A, comm_semigroup A

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
definition Monoid_Semigroup [coercion] [reducible] (M : Monoid) : Semigroup :=
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

end examples
