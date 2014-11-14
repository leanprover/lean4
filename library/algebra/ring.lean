/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.ring
Authors: Jeremy Avigad, Leonardo de Moura

Structures with multiplicative and additive components, including semirings, rings, and fields.
The development is modeled after Isabelle's library.
-/

import logic.eq logic.connectives
import data.unit data.sigma data.prod
import algebra.function algebra.binary algebra.group

open eq eq.ops

namespace algebra

variable {A : Type}

/- auxiliary classes -/

structure distrib [class] (A : Type) extends has_mul A, has_add A :=
(distrib_left : ∀a b c, mul a (add b c) = add (mul a b) (mul a c))
(distrib_right : ∀a b c, mul (add a b) c = add (mul a c) (mul b c))

theorem distrib_left [s : distrib A] (a b c : A) : a * (b + c) = a * b + a * c := !distrib.distrib_left
theorem distrib_right [s: distrib A] (a b c : A) : (a + b) * c = a * c + b * c := !distrib.distrib_right

structure mul_zero [class] (A : Type) extends has_mul A, has_zero A :=
(mul_zero_left : ∀a, mul zero a = zero)
(mul_zero_right : ∀a, mul a zero = zero)

theorem mul_zero_left [s : mul_zero A] (a : A) : 0 * a = 0 := !mul_zero.mul_zero_left
theorem mul_zero_right [s : mul_zero A] (a : A) : a * 0 = 0 := !mul_zero.mul_zero_right

structure zero_ne_one_class [class] (A : Type) extends has_zero A, has_one A :=
(zero_ne_one : zero ≠ one)

theorem zero_ne_one [s: zero_ne_one_class A] : 0 ≠ 1 := zero_ne_one_class.zero_ne_one


/- semiring -/
structure semiring [class] (A : Type) extends add_comm_monoid A, monoid A, distrib A, mul_zero A,
    zero_ne_one_class A

section

  variable [s : semiring A]
  include s

  /- -/
end

structure comm_semiring [class] (A : Type) extends semiring A, comm_semigroup A


/- abstract divisibility -/

structure has_dvd [class] (A : Type) extends has_mul A :=
(dvd : A → A → Prop)
(dvd_intro : ∀a b c, mul a b = c → dvd a c)
(dvd_imp_exists : ∀ a b, dvd a b → ∃c, mul a c = b)

definition dvd [s : has_dvd A] (a b : A) : Prop := has_dvd.dvd a b
infix `|` := dvd

theorem dvd_intro [s : has_dvd A] {a b c : A} : a * b = c → a | c := !has_dvd.dvd_intro

theorem dvd_imp_exists [s : has_dvd A] {a b : A} : a | b → ∃c, a * c = b := !has_dvd.dvd_imp_exists

theorem dvd_elim [s : has_dvd A] {P : Prop} {a b : A} (H₁ : a | b) (H₂ : ∀c, a * c = b → P) : P :=
exists_elim (dvd_imp_exists H₁) H₂

structure comm_semiring_dvd [class] (A : Type) extends comm_semiring A, has_dvd A

section comm_semiring_dvd

  variables [s : comm_semiring_dvd A] (a b c : A)
  include s

  theorem dvd_refl : a | a := dvd_intro (!mul_right_id)

  theorem dvd_trans {a b c : A} (H₁ : a | b) (H₂ : b | c) : a | c :=
  dvd_elim H₁
    (take d, assume H₃ : a * d = b,
      dvd_elim H₂
        (take e, assume H₄ : b * e = c,
          @dvd_intro _ _ _ (d * e) _
            (calc
              a * (d * e) = (a * d) * e : mul_assoc
                ... = b * e : H₃
                ... = c : H₄)))

  theorem zero_dvd {H : 0 | a} : a = 0 :=
    dvd_elim H (take c, assume H' : 0 * c = a, (H')⁻¹ ⬝ !mul_zero_left)

  theorem dvd_zero : a | 0 := dvd_intro !mul_zero_right

  theorem one_dvd : 1 | a := dvd_intro !mul_left_id

  theorem dvd_mul_right : a | a * b := dvd_intro rfl

  theorem dvd_mul_left : a | b * a := !mul_comm ▸ !dvd_mul_right

  theorem dvd_imp_dvd_mul_right {a b : A} (H : a | b) (c : A) : a | b * c :=
  dvd_elim H
    (take d,
      assume H₁ : a * d = b,
      dvd_intro
        (calc
          a * (d * c) = a * d * c : mul_assoc
             ... = b * c : H₁))

  theorem dvd_imp_dvd_mul_left {a b : A} (H : a | b) (c : A) : a | c * b :=
  !mul_comm ▸ (dvd_imp_dvd_mul_right H _)

  theorem mul_dvd_mono {a b c d : A} (dvd_ab : a | b) (dvd_cd : c | d) : a * c | b * d :=
  dvd_elim dvd_ab
    (take e, assume Haeb : a * e = b,
      dvd_elim dvd_cd
        (take f, assume Hcfd : c * f = d,
          dvd_intro
            (calc
              a * c * (e * f) = a * (c * (e * f)) : mul_assoc
                ... = a * (e * (c * f)) : mul_left_comm
                ... = a * e * (c * f) : mul_assoc
                ... = b * (c * f) : Haeb
                ... = b * d : Hcfd)))

  theorem mul_dvd_imp_dvd_left {a b c : A} (H : a * b | c) : a | c :=
  dvd_elim H (take d, assume Habdc : a * b * d = c, dvd_intro (!mul_assoc⁻¹ ⬝ Habdc))

  theorem mul_dvd_imp_dvd_right {a b c : A} (H : a * b | c) : b | c :=
  mul_dvd_imp_dvd_left (!mul_comm ▸ H)

  theorem dvd_add {a b c : A} (Hab : a | b) (Hac : a | c) : a | b + c :=
  dvd_elim Hab
    (take d, assume Hadb : a * d = b,
      dvd_elim Hac
        (take e, assume Haec : a * e = c,
          dvd_intro (show a * (d + e) = b + c, from Hadb ▸ Haec ▸ !distrib_left)))

end comm_semiring_dvd


/- ring -/

structure ring [class] (A : Type) extends add_comm_group A, monoid A, distrib A, zero_ne_one_class A

definition ring.to_semiring [instance] [s : ring A] : semiring A :=
semiring.mk ring.add ring.add_assoc ring.zero ring.add_left_id
  add_right_id   -- note: we've shown that add_right_id follows from add_left_id in add_comm_group
  ring.add_comm ring.mul ring.mul_assoc ring.one ring.mul_left_id ring.mul_right_id
  ring.distrib_left ring.distrib_right
  (take a,
    have H : 0 * a  + 0 = 0 * a + 0 * a, from
      calc
        0 * a + 0 = 0 * a : add_right_id
          ... = (0 + 0) * a : add_right_id
          ... = 0 * a + 0 * a : ring.distrib_right,
    show 0 * a = 0, from  (add_left_cancel H)⁻¹)
  (take a,
    have H : a * 0 + 0 = a * 0 + a * 0, from
      calc
        a * 0 + 0 = a * 0 : add_right_id
          ... = a * (0 + 0) : add_right_id
          ... = a * 0 + a * 0 : ring.distrib_left,
    show a * 0 = 0, from  (add_left_cancel H)⁻¹)
  ring.zero_ne_one

section

  variables [s : ring A] (a b c : A)
  include s

  theorem neg_mul_left : -(a * b) = (-a) * b :=
  neg_unique
    (calc
      a * b + (-a) * b = (a + -a) * b : distrib_right
        ... = 0 * b : add_right_inv
        ... = 0 : mul_zero_left)

  theorem neg_mul_right : -(a * b) = a * (-b) :=
  neg_unique
    (calc
      a * b + a * (-b) = a * (b + -b) : distrib_left
        ... = a * 0 : add_right_inv
        ... = 0 : mul_zero_right)

  theorem neg_mul_neg : (-a) * (-b) = a * b :=
  calc
     (-a) * (-b) = -(a * -b) : neg_mul_left
       ... = - -(a * b) : neg_mul_right
       ... = a * b : neg_neg

end

structure comm_ring [class] (A : Type) extends ring A, comm_semigroup A

/- TODO: show a comm_ring is a comm-semiring -/

structure comm_ring_dvd [class] (A : Type) extends comm_ring A, has_dvd A

definition comm_ring_dvd.to_comm_semiring_dvd [instance] [s : comm_ring_dvd A] : comm_semiring_dvd A :=
comm_semiring_dvd.mk has_add.add add_assoc has_zero.zero add_left_id add_right_id add_comm
  has_mul.mul mul_assoc has_one.one mul_left_id mul_right_id distrib_left distrib_right
  mul_zero_left mul_zero_right zero_ne_one mul_comm dvd (@dvd_intro A s) (@dvd_imp_exists A s)

end algebra
