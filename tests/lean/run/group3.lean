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

-- classes for notation
-- --------------------

inductive has_mul [class] (A : Type) : Type := mk : (A → A → A) → has_mul A
inductive has_one [class] (A : Type) : Type := mk : A → has_one A
inductive has_inv [class] (A : Type) : Type := mk : (A → A) → has_inv A

definition mul {A : Type} [s : has_mul A] (a b : A) : A := has_mul.rec (λf, f) s a b
definition one {A : Type} [s : has_one A] : A := has_one.rec (λo, o) s
definition inv {A : Type} [s : has_inv A] (a : A) : A := has_inv.rec (λi, i) s a

infix `*`    := mul
postfix `⁻¹` := inv
notation 1   := one

-- semigroup
-- ---------

inductive semigroup [class] (A : Type) : Type :=
mk : Π mul: A → A → A,
  (∀a b c : A, (mul (mul a b) c = mul a (mul b c))) →
    semigroup A

namespace semigroup
section
  variables {A : Type} [s : semigroup A]
  variables a b c : A
  definition mul := semigroup.rec (λmul assoc, mul) s a b
  section
    infixl `*` := mul
    definition assoc : (a * b) * c = a * (b * c) :=
      semigroup.rec (λmul assoc, assoc) s a b c
  end
end
end semigroup

section
  variables {A : Type} [s : semigroup A]
  include s
  definition semigroup_has_mul [instance] : has_mul A := has_mul.mk semigroup.mul

  theorem mul_assoc (a b c : A) : a * b * c = a * (b * c) :=
    !semigroup.assoc
end

-- comm_semigroup
-- --------------

inductive comm_semigroup [class] (A : Type) : Type :=
mk : Π (mul: A → A → A)
       (infixl `*` := mul),
       (∀a b c, (a * b) * c = a * (b * c)) →
       (∀a b,   a * b = b * a) →
    comm_semigroup A

namespace comm_semigroup
section
  variables {A : Type} [s : comm_semigroup A]
  variables a b c : A
  definition mul (a b : A) : A := comm_semigroup.rec (λmul assoc comm, mul) s a b
  definition assoc : mul (mul a b) c = mul a (mul b c) :=
    comm_semigroup.rec (λmul assoc comm, assoc) s a b c
  definition comm : mul a b = mul b a :=
    comm_semigroup.rec (λmul assoc comm, comm) s a b
end
end comm_semigroup

section
  variables {A : Type} [s : comm_semigroup A]
  variables a b c : A
  include s
  definition comm_semigroup_semigroup [instance] : semigroup A :=
    semigroup.mk comm_semigroup.mul comm_semigroup.assoc

  theorem mul_comm : a * b = b * a := !comm_semigroup.comm

  theorem mul_left_comm : a * (b * c) = b * (a * c) :=
    binary.left_comm mul_comm mul_assoc a b c
end

-- monoid
-- ------

inductive monoid [class] (A : Type) : Type :=
mk : Π (mul: A → A → A) (one : A)
       (infixl `*` := mul) (notation 1 := one),
       (∀a b c, (a * b) * c = a * (b * c)) →
       (∀a, a * 1 = a) →
       (∀a, 1 * a = a) →
    monoid A

namespace monoid
  section
  variables {A : Type} [s : monoid A]
  variables a b c : A
  include s
  section
  definition mul := monoid.rec (λmul one assoc right_id left_id, mul) s a b
  definition one := monoid.rec (λmul one assoc right_id left_id, one) s
  infixl `*` := mul
  notation 1 := one
  definition assoc : (a * b) * c = a * (b * c) :=
    monoid.rec (λmul one assoc right_id left_id, assoc) s a b c
  definition right_id : a * 1 = a :=
    monoid.rec (λmul one assoc right_id left_id, right_id) s a
  definition left_id : 1 * a = a :=
    monoid.rec (λmul one assoc right_id left_id, left_id) s a
  end
  end
end monoid

section
  variables {A : Type} [s : monoid A]
  variable a : A
  include s
  definition monoid_has_one [instance] : has_one A := has_one.mk (monoid.one)
  definition monoid_semigroup [instance] : semigroup A :=
    semigroup.mk monoid.mul monoid.assoc

  theorem mul_right_id : a * 1 = a := !monoid.right_id
  theorem mul_left_id  : 1 * a = a := !monoid.left_id
end


-- comm_monoid
-- -----------

inductive comm_monoid [class] (A : Type) : Type :=
mk : Π (mul: A → A → A) (one : A)
       (infixl `*` := mul) (notation 1 := one),
       (∀a b c, (a * b) * c = a * (b * c)) →
       (∀a, a * 1 = a) →
       (∀a, 1 * a = a) →
       (∀a b, a * b = b * a) →
 comm_monoid A

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
