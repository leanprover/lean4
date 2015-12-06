/-
Copyright (c) 2015 Jacob Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Gross, Jeremy Avigad

The complex numbers.
-/
import data.real
open real eq.ops

record complex : Type :=
(re : ℝ) (im : ℝ)

notation `ℂ` := complex

namespace complex

variables (u w z : ℂ)
variable n : ℕ

protected proposition eq {z w : ℂ} (H1 : complex.re z = complex.re w)
(H2 : complex.im z = complex.im w) : z = w :=
begin
  induction z,
  induction w,
  rewrite [H1, H2]
end

protected proposition eta (z : ℂ) : complex.mk (complex.re z) (complex.im z) = z :=
by cases z; exact rfl

definition of_real [coercion] (x : ℝ) : ℂ := complex.mk x 0
definition of_rat [coercion] (q : ℚ) : ℂ := rat.to.complex q
definition of_int [coercion] (i : ℤ) : ℂ := int.to.complex i
definition of_nat [coercion] (n : ℕ) : ℂ := nat.to.complex n
definition of_num [coercion] [reducible] (n : num) : ℂ := num.to.complex n

protected definition prio : num := num.pred real.prio

definition complex_has_zero [reducible] [instance] [priority complex.prio] : has_zero ℂ :=
has_zero.mk (of_nat 0)

definition complex_has_one [reducible] [instance] [priority complex.prio] : has_one ℂ :=
has_one.mk (of_nat 1)

theorem re_of_real (x : ℝ) : re (of_real x) = x := rfl

theorem im_of_real (x : ℝ) : im (of_real x) = 0 := rfl

protected definition add (z w : ℂ) : ℂ :=
complex.mk (complex.re z + complex.re w) (complex.im z + complex.im w)

protected definition neg (z : ℂ) : ℂ :=
complex.mk (-(re z)) (-(im z))

protected definition mul (z w : ℂ) : ℂ :=
complex.mk
  (complex.re w * complex.re z - complex.im w * complex.im z)
  (complex.re w * complex.im z + complex.im w * complex.re z)

/- notation -/

definition complex_has_add [reducible] [instance] [priority complex.prio] : has_add complex :=
has_add.mk complex.add

definition complex_has_neg [reducible] [instance] [priority complex.prio] : has_neg complex :=
has_neg.mk complex.neg

definition complex_has_mul [reducible] [instance] [priority complex.prio] : has_mul complex :=
has_mul.mk complex.mul

protected theorem add_def (z w : ℂ) :
  z + w = complex.mk (complex.re z + complex.re w) (complex.im z + complex.im w) := rfl

protected theorem neg_def (z : ℂ) : -z = complex.mk (-(re z)) (-(im z)) := rfl

protected theorem mul_def (z w : ℂ) :
  z * w = complex.mk
    (complex.re w * complex.re z - complex.im w * complex.im z)
    (complex.re w * complex.im z + complex.im w * complex.re z) := rfl

-- TODO: what notation should we use for i?

definition ii := complex.mk 0 1

theorem i_mul_i : ii * ii = -1 := rfl

/- basic properties -/

protected theorem add_comm (w z : ℂ) : w + z = z + w :=
complex.eq !add.comm !add.comm

protected theorem add_assoc (w z u : ℂ) : (w + z) + u = w + (z + u) :=
complex.eq !add.assoc !add.assoc

protected theorem add_zero (z : ℂ) : z + 0 = z :=
complex.eq !add_zero !add_zero

protected theorem zero_add (z : ℂ) : 0 + z = z := !complex.add_comm ▸ !complex.add_zero

definition smul (x : ℝ) (z : ℂ) : ℂ :=
complex.mk (x*re z) (x*im z)

protected theorem add_right_inv : z + - z = 0 :=
complex.eq !add.right_inv !add.right_inv

protected theorem add_left_inv : - z + z = 0 :=
!complex.add_comm ▸ !complex.add_right_inv

protected theorem mul_comm : w * z = z * w :=
by rewrite [*complex.mul_def, *mul.comm (re w), *mul.comm (im w), add.comm]

protected theorem one_mul :  1 * z = z :=
by krewrite [complex.mul_def, *mul_one, *mul_zero, sub_zero, zero_add, complex.eta]

protected theorem mul_one :  z * 1 = z := !complex.mul_comm ▸ !complex.one_mul

protected theorem left_distrib  : u * (w + z) = u * w + u * z :=
begin
  rewrite [*complex.mul_def, *complex.add_def, ▸*, *right_distrib, -sub_sub, *sub_eq_add_neg],
  rewrite [*add.assoc, add.left_comm (re z * im u), add.left_comm (-_)]
end

protected theorem right_distrib : (u + w) * z = u * z + w * z :=
by rewrite [*complex.mul_comm _ z, complex.left_distrib]

protected theorem mul_assoc : (u * w) * z = u * (w * z) :=
begin
  rewrite [*complex.mul_def, ▸*, *sub_eq_add_neg, *left_distrib, *right_distrib, *neg_add],
  rewrite [-*neg_mul_eq_neg_mul, -*neg_mul_eq_mul_neg, *add.assoc, *mul.assoc],
  rewrite [add.comm (-(im z * (im w * _))), add.comm (-(im z * (im w * _))), *add.assoc]
end

theorem re_add (z w : ℂ) : re (z + w) = re z + re w := rfl

theorem im_add (z w : ℂ) : im (z + w) = im z + im w := rfl

/- coercions -/

theorem of_real_add (a b : ℝ) : of_real (a + b) = of_real a + of_real b := rfl

theorem of_real_mul (a b : ℝ) : of_real (a * b) = (of_real a) * (of_real b) :=
by rewrite [complex.mul_def, *re_of_real, *im_of_real, *mul_zero, *zero_mul, sub_zero, add_zero,
           mul.comm]

theorem of_real_neg (a : ℝ) : of_real (-a) = -(of_real a) := rfl

theorem of_real.inj {a b : ℝ} (H : of_real a = of_real b) : a = b :=
show re (of_real a) = re (of_real b), from congr_arg re H

theorem eq_of_of_real_eq_of_real {a b : ℝ} (H : of_real a = of_real b) : a = b :=
of_real.inj H

theorem of_real_eq_of_real_iff (a b : ℝ) : of_real a = of_real b ↔ a = b :=
iff.intro eq_of_of_real_eq_of_real !congr_arg

/- make complex an instance of ring -/

protected definition comm_ring [reducible] : comm_ring complex :=
  begin
    fapply comm_ring.mk,
    exact complex.add,
    exact complex.add_assoc,
    exact 0,
    exact complex.zero_add,
    exact complex.add_zero,
    exact complex.neg,
    exact complex.add_left_inv,
    exact complex.add_comm,
    exact complex.mul,
    exact complex.mul_assoc,
    exact 1,
    apply complex.one_mul,
    apply complex.mul_one,
    apply complex.left_distrib,
    apply complex.right_distrib,
    apply complex.mul_comm
  end

local attribute complex.comm_ring [instance]

definition complex_has_sub [reducible] [instance] [priority complex.prio] : has_sub complex :=
has_sub.mk has_sub.sub

theorem of_real_sub (x y : ℝ) : of_real (x - y) = of_real x - of_real y :=
rfl

-- TODO: move these
private lemma eq_zero_of_mul_self_eq_zero {x : ℝ} (H : x * x = 0) : x = 0 :=
 iff.mp !or_self (!eq_zero_or_eq_zero_of_mul_eq_zero H)

private lemma eq_zero_of_sum_square_eq_zero {x y : ℝ} (H : x * x + y * y = 0) : x = 0 :=
have x * x ≤ (0 : ℝ), from calc
  x * x ≤ x * x + y * y : le_add_of_nonneg_right (mul_self_nonneg y)
    ... = 0             : H,
eq_zero_of_mul_self_eq_zero (le.antisymm this (mul_self_nonneg x))

/- complex modulus and conjugate-/

definition cmod (z : ℂ) : ℝ :=
(complex.re z) * (complex.re z) + (complex.im z) * (complex.im z)

theorem cmod_zero : cmod 0 = 0 := rfl

theorem cmod_of_real (x : ℝ) : cmod x = x * x :=
by rewrite [↑cmod, re_of_real, im_of_real, mul_zero, add_zero]

theorem eq_zero_of_cmod_eq_zero {z : ℂ} (H : cmod z = 0) : z = 0 :=
have H1 : (complex.re z) * (complex.re z) + (complex.im z) * (complex.im z) = 0,
  from H,
have H2 : complex.re z = 0, from eq_zero_of_sum_square_eq_zero H1,
have H3 : complex.im z = 0, from eq_zero_of_sum_square_eq_zero (!add.comm ▸ H1),
show z = 0, from complex.eq H2 H3

definition conj (z : ℂ) : ℂ := complex.mk (complex.re z) (-(complex.im z))

theorem conj_of_real {x : ℝ} : conj (of_real x) = of_real x := rfl

theorem conj_add (z w : ℂ) : conj (z + w) = conj z + conj w :=
by rewrite [↑conj, *complex.add_def, ▸*, neg_add]

theorem conj_mul (z w : ℂ) : conj (z * w) = conj z * conj w :=
by rewrite [↑conj, *complex.mul_def, ▸*, neg_mul_neg, neg_add,
            -neg_mul_eq_mul_neg, -neg_mul_eq_neg_mul]

theorem conj_conj (z : ℂ) : conj (conj z) = z :=
by rewrite [↑conj, neg_neg, complex.eta]

theorem mul_conj_eq_of_real_cmod (z : ℂ) : z * conj z = of_real (cmod z) :=
by rewrite [↑conj, ↑cmod, ↑of_real, complex.mul_def, ▸*, -*neg_mul_eq_neg_mul,
            sub_neg_eq_add, mul.comm (re z) (im z), add.right_inv]

theorem cmod_conj (z : ℂ) : cmod (conj z) = cmod z :=
begin
  apply eq_of_of_real_eq_of_real,
  rewrite [-*mul_conj_eq_of_real_cmod, conj_conj, mul.comm]
end

theorem cmod_mul (z w : ℂ) : cmod (z * w) = cmod z * cmod w :=
begin
  apply eq_of_of_real_eq_of_real,
  rewrite [of_real_mul, -*mul_conj_eq_of_real_cmod, conj_mul, *mul.assoc, mul.left_comm w]
end

protected noncomputable definition inv (z : ℂ) : complex := conj z * of_real (cmod z)⁻¹

protected noncomputable definition complex_has_inv [reducible] [instance] [priority complex.prio] :
  has_inv complex := has_inv.mk complex.inv

protected theorem inv_def (z : ℂ) : z⁻¹ = conj z * of_real (cmod z)⁻¹ := rfl

protected theorem inv_zero : 0⁻¹ = (0 : ℂ) :=
by krewrite [complex.inv_def, conj_of_real, zero_mul]

theorem of_real_inv (x : ℝ) : of_real x⁻¹ = (of_real x)⁻¹ :=
classical.by_cases
  (assume H : x = 0,
    by krewrite [H, inv_zero, complex.inv_zero])
  (assume H : x ≠ 0,
    by rewrite [complex.inv_def, cmod_of_real, conj_of_real, mul_inv_eq H H, -of_real_mul,
               -mul.assoc, mul_inv_cancel H, one_mul])

noncomputable protected definition div (z w : ℂ) : ℂ := z * w⁻¹

noncomputable definition complex_has_div [instance] [reducible] [priority complex.prio] :
    has_div complex :=
  has_div.mk complex.div

protected theorem div_def (z w : ℂ) : z / w = z * w⁻¹ := rfl

theorem of_real_div (x y : ℝ) : of_real (x / y) = of_real x / of_real y :=
have H : x / y = x * y⁻¹, from rfl,
by+ rewrite [H, complex.div_def, of_real_mul, of_real_inv]

theorem conj_inv (z : ℂ) : (conj z)⁻¹ = conj (z⁻¹) :=
by rewrite [*complex.inv_def, conj_mul, *conj_conj, conj_of_real, cmod_conj]

protected theorem mul_inv_cancel {z : ℂ} (H : z ≠ 0) : z * z⁻¹ = 1 :=
by rewrite [complex.inv_def, -mul.assoc, mul_conj_eq_of_real_cmod, -of_real_mul,
            mul_inv_cancel (assume H', H (eq_zero_of_cmod_eq_zero H'))]

protected theorem inv_mul_cancel {z : ℂ} (H : z ≠ 0) : z⁻¹ * z = 1 :=
!mul.comm ▸ complex.mul_inv_cancel H

protected noncomputable definition has_decidable_eq : decidable_eq ℂ :=
take z w, classical.prop_decidable (z = w)

protected theorem zero_ne_one : (0 : ℂ) ≠ 1 :=
assume H, zero_ne_one (eq_of_of_real_eq_of_real H)

protected noncomputable definition discrete_field [reducible][trans_instance] :
  discrete_field ℂ :=
⦃ discrete_field, complex.comm_ring,
  mul_inv_cancel   := @complex.mul_inv_cancel,
  inv_mul_cancel   := @complex.inv_mul_cancel,
  zero_ne_one      := complex.zero_ne_one,
  inv_zero         := complex.inv_zero,
  has_decidable_eq := complex.has_decidable_eq
⦄

-- TODO : we still need the whole family of coercion properties, for nat, int, rat

-- coercions

theorem of_rat_eq (a : ℚ) : of_rat a = of_real (real.of_rat a) := rfl

theorem of_int_eq (a : ℤ) : of_int a = of_real (real.of_int a) := rfl

theorem of_nat_eq (a : ℕ) : of_nat a = of_real (real.of_nat a) := rfl

theorem of_rat.inj {x y : ℚ} (H : of_rat x = of_rat y) : x = y :=
real.of_rat.inj (of_real.inj H)

theorem eq_of_of_rat_eq_of_rat {x y : ℚ} (H : of_rat x = of_rat y) : x = y :=
of_rat.inj H

theorem of_rat_eq_of_rat_iff (x y : ℚ) : of_rat x = of_rat y ↔ x = y :=
iff.intro eq_of_of_rat_eq_of_rat !congr_arg

theorem of_int.inj {a b : ℤ} (H : of_int a = of_int b) : a = b :=
rat.of_int.inj (of_rat.inj H)

theorem eq_of_of_int_eq_of_int {a b : ℤ} (H : of_int a = of_int b) : a = b :=
of_int.inj H

theorem of_int_eq_of_int_iff (a b : ℤ) : of_int a = of_int b ↔ a = b :=
iff.intro of_int.inj !congr_arg

theorem of_nat.inj {a b : ℕ} (H : of_nat a = of_nat b) : a = b :=
int.of_nat.inj (of_int.inj H)

theorem eq_of_of_nat_eq_of_nat {a b : ℕ} (H : of_nat a = of_nat b) : a = b :=
of_nat.inj H

theorem of_nat_eq_of_nat_iff (a b : ℕ) : of_nat a = of_nat b ↔ a = b :=
iff.intro of_nat.inj !congr_arg

open rat

theorem of_rat_add (a b : ℚ) : of_rat (a + b) = of_rat a + of_rat b :=
by rewrite [of_rat_eq]

theorem of_rat_neg (a : ℚ) : of_rat (-a) = -of_rat a :=
by rewrite [of_rat_eq]

-- these show why we have to use krewrite in the next theorem: there are
-- two different instances of "has_mul".

-- set_option pp.notation false
-- set_option pp.coercions true
-- set_option pp.implicit true

theorem of_rat_mul (a b : ℚ) : of_rat (a * b) = of_rat a * of_rat b :=
by krewrite [of_rat_eq, real.of_rat_mul, of_real_mul]

open int

theorem of_int_add (a b : ℤ) : of_int (a + b) = of_int a + of_int b :=
  by krewrite [of_int_eq, real.of_int_add, of_real_add]

theorem of_int_neg (a : ℤ) : of_int (-a) = -of_int a :=
  by krewrite [of_int_eq, real.of_int_neg, of_real_neg]

theorem of_int_mul (a b : ℤ) : of_int (a * b) = of_int a * of_int b :=
  by krewrite [of_int_eq, real.of_int_mul, of_real_mul]

open nat

theorem of_nat_add (a b : ℕ) : of_nat (a + b) = of_nat a + of_nat b :=
  by krewrite [of_nat_eq, real.of_nat_add, of_real_add]

theorem of_nat_mul (a b : ℕ) : of_nat (a * b) = of_nat a * of_nat b :=
  by krewrite [of_nat_eq, real.of_nat_mul, of_real_mul]

end complex
