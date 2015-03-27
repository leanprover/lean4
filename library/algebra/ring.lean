/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.ring
Authors: Jeremy Avigad, Leonardo de Moura

Structures with multiplicative and additive components, including semirings, rings, and fields.
The development is modeled after Isabelle's library.
-/

import logic.eq logic.connectives data.unit data.sigma data.prod
import algebra.function algebra.binary algebra.group
open eq eq.ops

namespace algebra

variable {A : Type}

/- auxiliary classes -/

structure distrib [class] (A : Type) extends has_mul A, has_add A :=
(left_distrib : ∀a b c, mul a (add b c) = add (mul a b) (mul a c))
(right_distrib : ∀a b c, mul (add a b) c = add (mul a c) (mul b c))

theorem left_distrib [s : distrib A] (a b c : A) : a * (b + c) = a * b + a * c :=
!distrib.left_distrib

theorem right_distrib [s: distrib A] (a b c : A) : (a + b) * c = a * c + b * c :=
!distrib.right_distrib

structure mul_zero_class [class] (A : Type) extends has_mul A, has_zero A :=
(zero_mul : ∀a, mul zero a = zero)
(mul_zero : ∀a, mul a zero = zero)

theorem zero_mul [s : mul_zero_class A] (a : A) : 0 * a = 0 := !mul_zero_class.zero_mul
theorem mul_zero [s : mul_zero_class A] (a : A) : a * 0 = 0 := !mul_zero_class.mul_zero

structure zero_ne_one_class [class] (A : Type) extends has_zero A, has_one A :=
(zero_ne_one : zero ≠ one)

theorem zero_ne_one [s: zero_ne_one_class A] : 0 ≠ 1 := @zero_ne_one_class.zero_ne_one A s

/- semiring -/

structure semiring [class] (A : Type) extends add_comm_monoid A, monoid A, distrib A,
    mul_zero_class A

section semiring
  variables [s : semiring A] (a b c : A)
  include s

  theorem ne_zero_of_mul_ne_zero_right {a b : A} (H : a * b ≠ 0) : a ≠ 0 :=
  assume H1 : a = 0,
  have H2 : a * b = 0, from H1⁻¹ ▸ zero_mul b,
  H H2

  theorem ne_zero_of_mul_ne_zero_left {a b : A} (H : a * b ≠ 0) : b ≠ 0 :=
  assume H1 : b = 0,
  have H2 : a * b = 0, from H1⁻¹ ▸ mul_zero a,
  H H2
end semiring

/- comm semiring -/

structure comm_semiring [class] (A : Type) extends semiring A, comm_semigroup A
-- TODO: we could also define a cancelative comm_semiring, i.e. satisfying
-- c ≠ 0 → c * a = c * b → a = b.

section comm_semiring
  variables [s : comm_semiring A] (a b c : A)
  include s

  definition dvd (a b : A) : Prop := ∃c, b = a * c
  notation ( a | b ) := dvd a b

  theorem dvd.intro {a b c : A} (H : a * c = b) : (a | b) :=
  exists.intro _ H⁻¹

  theorem dvd.intro_left {a b c : A} (H : c * a = b) : (a | b) :=
  dvd.intro (!mul.comm ▸ H)

  theorem exists_eq_mul_right_of_dvd {a b : A} (H : (a | b)) : ∃c, b = a * c := H

  theorem dvd.elim {P : Prop} {a b : A} (H₁ : (a | b)) (H₂ : ∀c, b = a * c → P) : P :=
  exists.elim H₁ H₂

  theorem exists_eq_mul_left_of_dvd {a b : A} (H : (a | b)) : ∃c, b = c * a :=
  dvd.elim H (take c, assume H1 : b = a * c, exists.intro c (H1 ⬝ !mul.comm))

  theorem dvd.elim_left {P : Prop} {a b : A} (H₁ : (a | b)) (H₂ : ∀c, b = c * a → P) : P :=
  exists.elim (exists_eq_mul_left_of_dvd H₁) (take c, assume H₃ : b = c * a, H₂ c H₃)

  theorem dvd.refl : (a | a) := dvd.intro !mul_one

  theorem dvd.trans {a b c : A} (H₁ : (a | b)) (H₂ : (b | c)) : (a | c) :=
  dvd.elim H₁
    (take d, assume H₃ : b = a * d,
      dvd.elim H₂
        (take e, assume H₄ : c = b * e,
          dvd.intro
            (show a * (d * e) = c, by rewrite ⟨-mul.assoc, -H₃, H₄⟩)))

  theorem eq_zero_of_zero_dvd {a : A} (H : (0 | a)) : a = 0 :=
    dvd.elim H (take c, assume H' : a = 0 * c, H' ⬝ !zero_mul)

  theorem dvd_zero : (a | 0) := dvd.intro !mul_zero

  theorem one_dvd : (1 | a) := dvd.intro !one_mul

  theorem dvd_mul_right : (a | a * b) := dvd.intro rfl

  theorem dvd_mul_left : (a | b * a) := mul.comm a b ▸ dvd_mul_right a b

  theorem dvd_mul_of_dvd_left {a b : A} (H : (a | b)) (c : A) : (a | b * c) :=
  dvd.elim H
    (take d,
      assume H₁ : b = a * d,
      dvd.intro
        (show a * (d * c) = b * c, from by rewrite ⟨-mul.assoc, H₁⟩))

  theorem dvd_mul_of_dvd_right {a b : A} (H : (a | b)) (c : A) : (a | c * b) :=
  !mul.comm ▸ (dvd_mul_of_dvd_left H _)

  theorem mul_dvd_mul {a b c d : A} (dvd_ab : (a | b)) (dvd_cd : (c | d)) : (a * c | b * d) :=
  dvd.elim dvd_ab
    (take e, assume Haeb : b = a * e,
      dvd.elim dvd_cd
        (take f, assume Hcfd : d = c * f,
          dvd.intro
            (show a * c * (e * f) = b * d,
             by rewrite [mul.assoc, {c*_}mul.left_comm, -mul.assoc, Haeb, Hcfd])))

  theorem dvd_of_mul_right_dvd {a b c : A} (H : (a * b | c)) : (a | c) :=
  dvd.elim H (take d, assume Habdc : c = a * b * d, dvd.intro (!mul.assoc⁻¹ ⬝ Habdc⁻¹))

  theorem dvd_of_mul_left_dvd {a b c : A} (H : (a * b | c)) : (b | c) :=
  dvd_of_mul_right_dvd (mul.comm a b ▸ H)

  theorem dvd_add {a b c : A} (Hab : (a | b)) (Hac : (a | c)) : (a | b + c) :=
  dvd.elim Hab
    (take d, assume Hadb : b = a * d,
      dvd.elim Hac
        (take e, assume Haec : c = a * e,
          dvd.intro (show a * (d + e) = b + c,
                     by rewrite [left_distrib, -Hadb, -Haec])))
end comm_semiring

/- ring -/

structure ring [class] (A : Type) extends add_comm_group A, monoid A, distrib A

theorem ring.mul_zero [s : ring A] (a : A) : a * 0 = 0 :=
have H : a * 0 + 0 = a * 0 + a * 0, from calc
  a * 0 + 0 = a * 0         : by rewrite add_zero
        ... = a * (0 + 0)   : by rewrite add_zero
        ... = a * 0 + a * 0 : by rewrite {a*_}ring.left_distrib,
show a * 0 = 0, from (add.left_cancel H)⁻¹

theorem ring.zero_mul [s : ring A] (a : A) : 0 * a = 0 :=
have H : 0 * a + 0 = 0 * a + 0 * a, from calc
  0 * a + 0 = 0 * a         : by rewrite add_zero
        ... = (0 + 0) * a   : by rewrite add_zero
        ... = 0 * a + 0 * a : by rewrite {_*a}ring.right_distrib,
show 0 * a = 0, from  (add.left_cancel H)⁻¹

definition ring.to_semiring [instance] [coercion] [reducible] [s : ring A] : semiring A :=
⦃ semiring, s,
  mul_zero := ring.mul_zero,
  zero_mul := ring.zero_mul ⦄

section
  variables [s : ring A] (a b c d e : A)
  include s

  theorem neg_mul_eq_neg_mul : -(a * b) = -a * b :=
  neg_eq_of_add_eq_zero
    begin
      rewrite [-right_distrib, add.right_inv, zero_mul]
    end

  theorem neg_mul_eq_mul_neg : -(a * b) = a * -b :=
   neg_eq_of_add_eq_zero
     begin
       rewrite [-left_distrib, add.right_inv, mul_zero]
     end

  theorem neg_mul_neg : -a * -b = a * b :=
  calc
     -a * -b = -(a * -b) : by rewrite -neg_mul_eq_neg_mul
       ... = - -(a * b)  : by rewrite -neg_mul_eq_mul_neg
       ... = a * b       : by rewrite neg_neg

  theorem neg_mul_comm : -a * b = a * -b := !neg_mul_eq_neg_mul⁻¹ ⬝ !neg_mul_eq_mul_neg

  theorem neg_eq_neg_one_mul : -a = -1 * a :=
  calc
    -a = -(1 * a)  : by rewrite one_mul
      ... = -1 * a : by rewrite neg_mul_eq_neg_mul

  theorem mul_sub_left_distrib : a * (b - c) = a * b - a * c :=
  calc
    a * (b - c) = a * b + a * -c : left_distrib
      ... = a * b + - (a * c)    : by rewrite -neg_mul_eq_mul_neg
      ... = a * b - a * c        : rfl

  theorem mul_sub_right_distrib : (a - b) * c = a * c - b * c :=
  calc
    (a - b) * c = a * c  + -b * c : right_distrib
      ... = a * c + - (b * c)     : by rewrite neg_mul_eq_neg_mul
      ... = a * c - b * c         : rfl

  -- TODO: can calc mode be improved to make this easier?
  -- TODO: there is also the other direction. It will be easier when we
  -- have the simplifier.

  theorem mul_add_eq_mul_add_iff_sub_mul_add_eq : a * e + c = b * e + d ↔ (a - b) * e + c = d :=
  calc
    a * e + c = b * e + d ↔ a * e + c = d + b * e : by rewrite {b*e+_}add.comm
      ... ↔ a * e + c - b * e = d : iff.symm !sub_eq_iff_eq_add
      ... ↔ a * e - b * e + c = d : by rewrite sub_add_eq_add_sub
      ... ↔ (a - b) * e + c = d   : by rewrite mul_sub_right_distrib

  theorem mul_neg_one_eq_neg : a * (-1) = -a :=
    have H : a + a * -1 = 0, from calc
      a + a * -1 = a * 1 + a * -1 : mul_one
             ... = a * (1 + -1)   : left_distrib
             ... = a * 0          : add.right_inv
             ... = 0              : mul_zero,
    symm (neg_eq_of_add_eq_zero H)

  theorem mul_ne_zero_imp_ne_zero {a b} (H : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
    have Ha : a ≠ 0, from
      (assume Ha1 : a = 0,
        have H1 : a * b = 0, by rewrite [Ha1, zero_mul],
        absurd H1 H),
    have Hb : b ≠ 0, from
      (assume Hb1 : b = 0,
        have H1 : a * b = 0, by rewrite [Hb1, mul_zero],
        absurd H1 H),
    and.intro Ha Hb
end

structure comm_ring [class] (A : Type) extends ring A, comm_semigroup A

definition comm_ring.to_comm_semiring [instance] [coercion] [reducible] [s : comm_ring A] : comm_semiring A :=
⦃ comm_semiring, s,
  mul_zero := mul_zero,
  zero_mul := zero_mul ⦄

section
  variables [s : comm_ring A] (a b c d e : A)
  include s

  -- TODO: wait for the simplifier
  theorem mul_self_sub_mul_self_eq : a * a - b * b = (a + b) * (a - b) := sorry

  theorem mul_self_sub_one_eq : a * a - 1 = (a + 1) * (a - 1) :=
  mul_one 1 ▸ mul_self_sub_mul_self_eq a 1

  theorem dvd_neg_iff_dvd : (a | -b) ↔ (a | b) :=
  iff.intro
    (assume H : (a | -b),
      dvd.elim H
        (take c, assume H' : -b = a * c,
          dvd.intro
            (show a * -c = b,
             by rewrite [-neg_mul_eq_mul_neg, -H', neg_neg])))
    (assume H : (a | b),
      dvd.elim H
        (take c, assume H' : b = a * c,
          dvd.intro
            (show a * -c = -b,
             by rewrite [-neg_mul_eq_mul_neg, -H'])))

  theorem neg_dvd_iff_dvd : (-a | b) ↔ (a | b) :=
  iff.intro
    (assume H : (-a | b),
      dvd.elim H
        (take c, assume H' : b = -a * c,
          dvd.intro
            (show a * -c = b, by rewrite [-neg_mul_comm, H'])))
    (assume H : (a | b),
      dvd.elim H
        (take c, assume H' : b = a * c,
          dvd.intro
            (show -a * -c = b, by rewrite [neg_mul_neg, H'])))

  theorem dvd_sub (H₁ : (a | b)) (H₂ : (a | c)) : (a | b - c) :=
  dvd_add H₁ (iff.elim_right !dvd_neg_iff_dvd H₂)
end

/- integral domains -/

structure no_zero_divisors [class] (A : Type) extends has_mul A, has_zero A :=
(eq_zero_or_eq_zero_of_mul_eq_zero : ∀a b, mul a b = zero → a = zero ∨ b = zero)

theorem eq_zero_or_eq_zero_of_mul_eq_zero {A : Type} [s : no_zero_divisors A] {a b : A}
    (H : a * b = 0) :
  a = 0 ∨ b = 0 := !no_zero_divisors.eq_zero_or_eq_zero_of_mul_eq_zero H

structure integral_domain [class] (A : Type) extends comm_ring A, no_zero_divisors A

section

  variables [s : integral_domain A] (a b c d e : A)
  include s

  theorem mul_ne_zero {a b : A} (H1 : a ≠ 0) (H2 : b ≠ 0) : a * b ≠ 0 :=
  assume H : a * b = 0,
    or.elim (eq_zero_or_eq_zero_of_mul_eq_zero H) (assume H3, H1 H3) (assume H4, H2 H4)

  theorem mul.cancel_right {a b c : A} (Ha : a ≠ 0) (H : b * a = c * a) : b = c :=
  have H1  : b * a - c * a = 0, from iff.mp !eq_iff_sub_eq_zero H,
  have H2 : (b - c) * a = 0, using H1, by rewrite [mul_sub_right_distrib, H1],
  have H3 : b - c = 0, from or_resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero H2) Ha,
  iff.elim_right !eq_iff_sub_eq_zero H3

  theorem mul.cancel_left {a b c : A} (Ha : a ≠ 0) (H : a * b = a * c) : b = c :=
  have H1 : a * b - a * c = 0, from iff.mp !eq_iff_sub_eq_zero H,
  have H2 : a * (b - c) = 0, using H1, by rewrite [mul_sub_left_distrib, H1],
  have H3 : b - c = 0, from or_resolve_right (eq_zero_or_eq_zero_of_mul_eq_zero H2) Ha,
  iff.elim_right !eq_iff_sub_eq_zero H3

  -- TODO: do we want the iff versions?

  -- TODO: wait for simplifier
  theorem mul_self_eq_mul_self_iff (a b : A) : a * a = b * b ↔ a = b ∨ a = -b := sorry

  theorem mul_self_eq_one_iff (a : A) : a * a = 1 ↔ a = 1 ∨ a = -1 := sorry

  -- TODO: c - b * c → c = 0 ∨ b = 1 and variants

  theorem dvd_of_mul_dvd_mul_left {a b c : A} (Ha : a ≠ 0) (Hdvd : (a * b | a * c)) : (b | c) :=
  dvd.elim Hdvd
    (take d,
      assume H : a * c = a * b * d,
      have H1 : b * d = c, from mul.cancel_left Ha (mul.assoc a b d ▸ H⁻¹),
      dvd.intro H1)

  theorem dvd_of_mul_dvd_mul_right {a b c : A} (Ha : a ≠ 0) (Hdvd : (b * a | c * a)) : (b | c) :=
  dvd.elim Hdvd
    (take d,
      assume H : c * a = b * a * d,
      have H1 : b * d * a = c * a, from by rewrite [mul.right_comm, -H],
      have H2 : b * d = c, from mul.cancel_right Ha H1,
      dvd.intro H2)
end

end algebra
