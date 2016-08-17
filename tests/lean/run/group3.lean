-- Copyright (c) 2014 Jeremy Avigad. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Jeremy Avigad, Leonardo de Moura

-- algebra.group
-- =============

-- Various structures with 1, *, inv, including groups.

open eq

namespace algebra

-- classes for notation
-- --------------------

inductive [class] has_mul (A : Type) : Type | mk : (A → A → A) → has_mul
inductive [class] has_one (A : Type) : Type | mk : A → has_one
inductive [class] has_inv (A : Type) : Type | mk : (A → A) → has_inv

definition mul {A : Type} [s : has_mul A] (a b : A) : A := has_mul.rec (λf, f) s a b
definition one {A : Type} [s : has_one A] : A := has_one.rec (λo, o) s
definition inv {A : Type} [s : has_inv A] (a : A) : A := has_inv.rec (λi, i) s a

infix `*`    := mul
postfix `⁻¹` := inv
notation 1   := one

-- semigroup
-- ---------

inductive [class] semigroup (A : Type) : Type
| mk : Π mul: A → A → A,
      (∀a b c : A, (mul (mul a b) c = mul a (mul b c))) →
      semigroup

namespace semigroup
section
  variables {A : Type} [s : semigroup A]
  variables a b c : A
  definition mul := semigroup.rec (λmul assoc, mul) s a b
  section
    infixl `*` := mul
  end
end
end semigroup

section
  variables {A : Type} [s : semigroup A]
  include s
  attribute [instance]
  definition semigroup_has_mul : has_mul A := has_mul.mk semigroup.mul

end

-- comm_semigroup
-- --------------

inductive [class] comm_semigroup (A : Type) : Type
| mk : Π (mul: A → A → A)
       (infixl `*` := mul),
       (∀a b c, (a * b) * c = a * (b * c)) →
       (∀a b,   a * b = b * a) →
    comm_semigroup

namespace comm_semigroup
section
  variables {A : Type} [s : comm_semigroup A]
  variables a b c : A
  definition mul (a b : A) : A := comm_semigroup.rec (λmul assoc comm, mul) s a b
end
end comm_semigroup


-- monoid
-- ------

inductive [class] monoid (A : Type) : Type
| mk : Π (mul: A → A → A) (one : A)
       (infixl `*` := mul) (notation 1 := one),
       (∀a b c, (a * b) * c = a * (b * c)) →
       (∀a, a * 1 = a) →
       (∀a, 1 * a = a) →
    monoid

end algebra
