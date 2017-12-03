/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura

Structures with multiplicative and additive components, including division rings and fields.
The development is modeled after Isabelle's library.
-/
prelude
import init.algebra.ring
universe u

/- Make sure instances defined in this file have lower priority than the ones
   defined for concrete structures -/
set_option default_priority 100

set_option old_structure_cmd true

class division_ring (α : Type u) extends ring α, has_inv α, zero_ne_one_class α :=
(mul_inv_cancel : ∀ {a : α}, a ≠ 0 → a * a⁻¹ = 1)
(inv_mul_cancel : ∀ {a : α}, a ≠ 0 → a⁻¹ * a = 1)

variable {α : Type u}

section division_ring
variables [division_ring α]

protected definition algebra.div (a b : α) : α :=
a * b⁻¹

instance division_ring_has_div [division_ring α] : has_div α :=
⟨algebra.div⟩

lemma division_def (a b : α) : a / b = a * b⁻¹ :=
rfl

@[simp]
lemma mul_inv_cancel {a : α} (h : a ≠ 0) : a * a⁻¹ = 1 :=
division_ring.mul_inv_cancel h

@[simp]
lemma inv_mul_cancel {a : α} (h : a ≠ 0) : a⁻¹ * a = 1 :=
division_ring.inv_mul_cancel h

@[simp]
lemma one_div_eq_inv (a : α) : 1 / a = a⁻¹ :=
one_mul a⁻¹

lemma inv_eq_one_div (a : α) : a⁻¹ = 1 / a :=
by simp

local attribute [simp]
division_def mul_comm mul_assoc
mul_left_comm mul_inv_cancel inv_mul_cancel

lemma div_eq_mul_one_div (a b : α) : a / b = a * (1 / b) :=
by simp

lemma mul_one_div_cancel {a : α} (h : a ≠ 0) : a * (1 / a) = 1 :=
by simp [h]

lemma one_div_mul_cancel {a : α} (h : a ≠ 0) : (1 / a) * a = 1 :=
by simp [h]

lemma div_self {a : α} (h : a ≠ 0) : a / a = 1 :=
by simp [h]

lemma one_div_one : 1 / 1 = (1:α) :=
div_self (ne.symm zero_ne_one)

lemma mul_div_assoc (a b c : α) : (a * b) / c = a * (b / c) :=
by simp

lemma one_div_ne_zero {a : α} (h : a ≠ 0) : 1 / a ≠ 0 :=
assume : 1 / a = 0,
have 0 = (1:α), from eq.symm (by rw [← mul_one_div_cancel h, this, mul_zero]),
absurd this zero_ne_one

lemma inv_ne_zero {a : α} (h : a ≠ 0) : a⁻¹ ≠ 0 :=
by rw inv_eq_one_div; exact one_div_ne_zero h

lemma one_inv_eq : 1⁻¹ = (1:α) :=
calc 1⁻¹ = 1 * 1⁻¹ : by rw [one_mul]
     ... = (1:α)   : by simp

local attribute [simp] one_inv_eq

lemma div_one (a : α) : a / 1 = a :=
by simp

lemma zero_div (a : α) : 0 / a = 0 :=
by simp

-- note: integral domain has a "mul_ne_zero". α commutative division ring is an integral
-- domain, but let's not define that class for now.
lemma division_ring.mul_ne_zero {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
assume : a * b = 0,
have   a * 1 = 0, by rw [← mul_one_div_cancel hb, ← mul_assoc, this, zero_mul],
have   a = 0, by rwa mul_one at this,
absurd this ha

lemma mul_ne_zero_comm {a b : α} (h : a * b ≠ 0) : b * a ≠ 0 :=
have h₁ : a ≠ 0, from ne_zero_of_mul_ne_zero_right h,
have h₂ : b ≠ 0, from ne_zero_of_mul_ne_zero_left h,
division_ring.mul_ne_zero h₂ h₁

lemma eq_one_div_of_mul_eq_one {a b : α} (h : a * b = 1) : b = 1 / a :=
have a ≠ 0, from
   assume : a = 0,
   have 0 = (1:α), by rwa [this, zero_mul] at h,
      absurd this zero_ne_one,
have b = (1 / a) * a * b, by rw [one_div_mul_cancel this, one_mul],
show b = 1 / a, by rwa [mul_assoc, h, mul_one] at this

lemma eq_one_div_of_mul_eq_one_left {a b : α} (h : b * a = 1) : b = 1 / a :=
have a ≠ 0, from
  assume : a = 0,
  have 0 = (1:α), by rwa [this, mul_zero] at h,
    absurd this zero_ne_one,
by rw [← h, mul_div_assoc, div_self this, mul_one]

lemma division_ring.one_div_mul_one_div {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) : (1 / a) * (1 / b) = 1 / (b * a) :=
have (b * a) * ((1 / a) * (1 / b)) = 1,
  by rw [mul_assoc, ← mul_assoc a, mul_one_div_cancel ha, one_mul, mul_one_div_cancel hb],
eq_one_div_of_mul_eq_one this

lemma one_div_neg_one_eq_neg_one : (1:α) / (-1) = -1 :=
have (-1) * (-1) = (1:α), by rw [neg_mul_neg, one_mul],
eq.symm (eq_one_div_of_mul_eq_one this)

lemma division_ring.one_div_neg_eq_neg_one_div {a : α} (h : a ≠ 0) : 1 / (- a) = - (1 / a) :=
have -1 ≠ (0:α), from
  (assume : -1 = 0, absurd (eq.symm (calc
            1 = -(-1)  : (neg_neg (1:α)).symm
          ... = -0     : by rw this
          ... = (0:α)  : neg_zero)) zero_ne_one),
calc
  1 / (- a) = 1 / ((-1) * a)        : by rw neg_eq_neg_one_mul
        ... = (1 / a) * (1 / (- 1)) : by rw (division_ring.one_div_mul_one_div h this)
        ... = (1 / a) * (-1)        : by rw one_div_neg_one_eq_neg_one
        ... = - (1 / a)             : by rw [mul_neg_eq_neg_mul_symm, mul_one]

lemma div_neg_eq_neg_div {a : α} (b : α) (ha : a ≠ 0) : b / (- a) = - (b / a) :=
calc
  b / (- a) = b * (1 / (- a)) : by rw [← inv_eq_one_div, division_def]
        ... = b * -(1 / a)    : by rw (division_ring.one_div_neg_eq_neg_one_div ha)
        ... = -(b * (1 / a))  : by rw neg_mul_eq_mul_neg
        ... = - (b * a⁻¹)     : by rw inv_eq_one_div

lemma neg_div (a b : α) : (-b) / a = - (b / a) :=
by rw [neg_eq_neg_one_mul, mul_div_assoc, ← neg_eq_neg_one_mul]

lemma division_ring.neg_div_neg_eq (a : α) {b : α} (hb : b ≠ 0) : (-a) / (-b) = a / b :=
by rw [(div_neg_eq_neg_div _ hb), neg_div, neg_neg]

lemma division_ring.one_div_one_div {a : α} (h : a ≠ 0) : 1 / (1 / a) = a :=
eq.symm (eq_one_div_of_mul_eq_one_left (mul_one_div_cancel h))

lemma division_ring.inv_inv {a : α} (h : a ≠ 0) : a⁻¹⁻¹ = a :=
by rw [inv_eq_one_div, inv_eq_one_div, division_ring.one_div_one_div h]

lemma division_ring.eq_of_one_div_eq_one_div {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) (h : 1 / a = 1 / b) : a = b :=
by rw [← division_ring.one_div_one_div ha, h, (division_ring.one_div_one_div hb)]

lemma mul_inv_eq {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) : (b * a)⁻¹ = a⁻¹ * b⁻¹ :=
eq.symm $ calc
  a⁻¹ * b⁻¹ = (1 / a) * (1 / b) : by simp
        ... = (1 / (b * a))     : division_ring.one_div_mul_one_div ha hb
        ... = (b * a)⁻¹         : by simp

lemma division_ring.one_div_div {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) : 1 / (a / b) = b / a :=
by rw [one_div_eq_inv, division_def, mul_inv_eq (inv_ne_zero hb) ha,
       division_ring.inv_inv hb, division_def]

lemma mul_div_cancel (a : α) {b : α} (hb : b ≠ 0) : a * b / b = a :=
by simp [hb]

lemma div_mul_cancel (a : α) {b : α} (hb : b ≠ 0) : a / b * b = a :=
by simp [hb]

lemma div_add_div_same (a b c : α) : a / c + b / c = (a + b) / c :=
eq.symm $ right_distrib a b (c⁻¹)

lemma div_sub_div_same (a b c : α) : (a / c) - (b / c) = (a - b) / c :=
by rw [sub_eq_add_neg, ← neg_div, div_add_div_same, sub_eq_add_neg]

lemma one_div_mul_add_mul_one_div_eq_one_div_add_one_div {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) :
          (1 / a) * (a + b) * (1 / b) = 1 / a + 1 / b :=
by rw [(left_distrib (1 / a)), (one_div_mul_cancel ha), right_distrib, one_mul,
       mul_assoc, (mul_one_div_cancel hb), mul_one, add_comm]

lemma one_div_mul_sub_mul_one_div_eq_one_div_add_one_div {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) :
          (1 / a) * (b - a) * (1 / b) = 1 / a - 1 / b :=
by rw [(mul_sub_left_distrib (1 / a)), (one_div_mul_cancel ha), mul_sub_right_distrib,
       one_mul, mul_assoc, (mul_one_div_cancel hb), mul_one]

lemma div_eq_one_iff_eq (a : α) {b : α} (hb : b ≠ 0) : a / b = 1 ↔ a = b :=
iff.intro
 (assume : a / b = 1, calc
      a   = a / b * b : by simp [hb]
      ... = 1 * b     : by rw this
      ... = b         : by simp)
 (assume : a = b, by simp [this, hb])

lemma eq_of_div_eq_one (a : α) {b : α} (Hb : b ≠ 0) : a / b = 1 → a = b :=
iff.mp $ div_eq_one_iff_eq a Hb

lemma eq_div_iff_mul_eq (a b : α) {c : α} (hc : c ≠ 0) : a = b / c ↔ a * c = b :=
iff.intro
  (assume : a = b / c, by rw [this, (div_mul_cancel _ hc)])
  (assume : a * c = b, by rw [← this, mul_div_cancel _ hc])

lemma eq_div_of_mul_eq (a b : α) {c : α} (hc : c ≠ 0) : a * c = b → a = b / c :=
iff.mpr $ eq_div_iff_mul_eq a b hc

lemma mul_eq_of_eq_div (a b: α) {c : α} (hc : c ≠ 0) : a = b / c → a * c = b :=
iff.mp $ eq_div_iff_mul_eq a b hc

lemma add_div_eq_mul_add_div (a b : α) {c : α} (hc : c ≠ 0) : a + b / c = (a * c + b) / c :=
have (a + b / c) * c = a * c + b, by rw [right_distrib, (div_mul_cancel _ hc)],
  (iff.mpr (eq_div_iff_mul_eq _ _ hc)) this

lemma mul_mul_div (a : α) {c : α} (hc : c ≠ 0) : a = a * c * (1 / c) :=
by simp [hc]

end division_ring

class field (α : Type u) extends division_ring α, comm_ring α

section field

variable [field α]

lemma field.one_div_mul_one_div {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) : (1 / a) * (1 / b) =  1 / (a * b) :=
by rw [(division_ring.one_div_mul_one_div ha hb), mul_comm b]

lemma field.div_mul_right {a b : α} (hb : b ≠ 0) (h : a * b ≠ 0) : a / (a * b) = 1 / b :=
have a ≠ 0, from ne_zero_of_mul_ne_zero_right h,
  eq.symm (calc
      1 / b = a * ((1 / a) * (1 / b)) : by rw [← mul_assoc, mul_one_div_cancel this, one_mul]
        ... = a * (1 / (b * a))       : by rw (division_ring.one_div_mul_one_div this hb)
        ... = a * (a * b)⁻¹           : by rw [inv_eq_one_div, mul_comm a b])

lemma field.div_mul_left {a b : α} (ha : a ≠ 0) (h : a * b ≠ 0) : b / (a * b) = 1 / a :=
have b * a ≠ 0, from mul_ne_zero_comm h,
by rw [mul_comm a, (field.div_mul_right ha this)]

lemma mul_div_cancel_left {a : α} (b : α) (ha : a ≠ 0) : a * b / a = b :=
by rw [mul_comm a, (mul_div_cancel _ ha)]

lemma mul_div_cancel' (a : α) {b : α} (hb : b ≠ 0) : b * (a / b) = a :=
by rw [mul_comm, (div_mul_cancel _ hb)]

lemma one_div_add_one_div {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) : 1 / a + 1 / b = (a + b) / (a * b) :=
have a * b ≠ 0, from (division_ring.mul_ne_zero ha hb),
by rw [add_comm, ← field.div_mul_left ha this, ← field.div_mul_right hb this,
       division_def, division_def, division_def, ← right_distrib]

local attribute [simp] mul_assoc mul_comm mul_left_comm

lemma field.div_mul_div (a : α) {b : α} (c : α) {d : α} (hb : b ≠ 0) (hd : d ≠ 0) :
      (a / b) * (c / d) = (a * c) / (b * d) :=
begin simp [division_def], rw [mul_inv_eq hd hb, mul_comm d⁻¹] end

lemma mul_div_mul_left (a : α) {b c : α} (hb : b ≠ 0) (hc : c ≠ 0) :
      (c * a) / (c * b) = a / b :=
by rw [← field.div_mul_div _ _ hc hb, div_self hc, one_mul]

lemma mul_div_mul_right (a : α) {b c : α} (hb : b ≠ 0) (hc : c ≠ 0) :
      (a * c) / (b * c) = a / b :=
by rw [mul_comm a, mul_comm b, mul_div_mul_left _ hb hc]

lemma div_mul_eq_mul_div (a b c : α) : (b / c) * a = (b * a) / c :=
by simp [division_def]

lemma field.div_mul_eq_mul_div_comm (a b : α) {c : α} (hc : c ≠ 0) :
      (b / c) * a = b * (a / c) :=
by rw [div_mul_eq_mul_div, ← one_mul c, ← field.div_mul_div _ _ (ne.symm zero_ne_one) hc,
       div_one, one_mul]

lemma div_add_div (a : α) {b : α} (c : α) {d : α} (hb : b ≠ 0) (hd : d ≠ 0) :
      (a / b) + (c / d) = ((a * d) + (b * c)) / (b * d) :=
by rw [← mul_div_mul_right _ hb hd, ← mul_div_mul_left _ hd hb, div_add_div_same]

lemma div_sub_div (a : α) {b : α} (c : α) {d : α} (hb : b ≠ 0) (hd : d ≠ 0) :
      (a / b) - (c / d) = ((a * d) - (b * c)) / (b * d) :=
begin
  simp [sub_eq_add_neg],
  rw [neg_eq_neg_one_mul, ← mul_div_assoc, div_add_div _ _ hb hd,
      ← mul_assoc, mul_comm b, mul_assoc, ← neg_eq_neg_one_mul]
end

lemma mul_eq_mul_of_div_eq_div (a : α) {b : α} (c : α) {d : α} (hb : b ≠ 0)
      (hd : d ≠ 0) (h : a / b = c / d) : a * d = c * b :=
by rw [← mul_one (a*d), mul_assoc, mul_comm d, ← mul_assoc, ← div_self hb,
       ← field.div_mul_eq_mul_div_comm _ _ hb, h, div_mul_eq_mul_div, div_mul_cancel _ hd]

lemma field.div_div_eq_mul_div (a : α) {b c : α} (hb : b ≠ 0) (hc : c ≠ 0) :
      a / (b / c) = (a * c) / b :=
by rw [div_eq_mul_one_div, division_ring.one_div_div hb hc, ← mul_div_assoc]

lemma field.div_div_eq_div_mul (a : α) {b c : α} (hb : b ≠ 0) (hc : c ≠ 0) :
      (a / b) / c = a / (b * c) :=
by rw [div_eq_mul_one_div, field.div_mul_div _ _ hb hc, mul_one]

lemma field.div_div_div_div_eq (a : α) {b c d : α} (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
      (a / b) / (c / d) = (a * d) / (b * c) :=
by rw [field.div_div_eq_mul_div _ hc hd, div_mul_eq_mul_div,
       field.div_div_eq_div_mul _ hb hc]

lemma field.div_mul_eq_div_mul_one_div (a : α) {b c : α} (hb : b ≠ 0) (hc : c ≠ 0) :
      a / (b * c) = (a / b) * (1 / c) :=
by rw [← field.div_div_eq_div_mul _ hb hc, ← div_eq_mul_one_div]

lemma eq_of_mul_eq_mul_of_nonzero_left {a b c : α} (h : a ≠ 0) (h₂ : a * b = a * c) : b = c :=
by rw [← one_mul b, ← div_self h, div_mul_eq_mul_div, h₂, mul_div_cancel_left _ h]

lemma eq_of_mul_eq_mul_of_nonzero_right {a b c : α} (h : c ≠ 0) (h2 : a * c = b * c) : a = b :=
by rw [← mul_one a, ← div_self h, ← mul_div_assoc, h2, mul_div_cancel _ h]

end field

class discrete_field (α : Type u) extends field α :=
(has_decidable_eq : decidable_eq α)
(inv_zero : inv zero = zero)

attribute [instance] discrete_field.has_decidable_eq

section discrete_field
variable [discrete_field α]

-- many of the lemmas in discrete_field are the same as lemmas in field or division ring,
-- but with fewer hypotheses since 0⁻¹ = 0 and equality is decidable.

lemma discrete_field.eq_zero_or_eq_zero_of_mul_eq_zero
    (a b : α) (h : a * b = 0) : a = 0 ∨ b = 0 :=
decidable.by_cases
  (assume : a = 0, or.inl this)
  (assume : a ≠ 0,
     or.inr (by rw [← one_mul b, ← inv_mul_cancel this, mul_assoc, h, mul_zero]))

instance discrete_field.to_integral_domain [s : discrete_field α] : integral_domain α :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := discrete_field.eq_zero_or_eq_zero_of_mul_eq_zero,
  ..s }

lemma inv_zero : 0⁻¹ = (0:α) :=
discrete_field.inv_zero α

lemma one_div_zero : 1 / 0 = (0:α) :=
calc
  1 / 0 = (1:α) * 0⁻¹ : by rw division_def
    ... = 1 * 0       : by rw inv_zero
    ... = (0:α)       : by rw mul_zero

lemma div_zero (a : α) : a / 0 = 0 :=
by rw [div_eq_mul_one_div, one_div_zero, mul_zero]

lemma ne_zero_of_one_div_ne_zero {a : α} (h : 1 / a ≠ 0) : a ≠ 0 :=
assume ha : a = 0, begin rw [ha, one_div_zero] at h, contradiction end

lemma eq_zero_of_one_div_eq_zero {a : α} (h : 1 / a = 0) : a = 0 :=
decidable.by_cases
  (assume ha, ha)
  (assume ha, false.elim ((one_div_ne_zero ha) h))

lemma one_div_mul_one_div' (a b : α) : (1 / a) * (1 / b) = 1 / (b * a) :=
decidable.by_cases
 (assume : a = 0,
   by rw [this, div_zero, zero_mul, mul_zero, div_zero])
 (assume ha : a ≠ 0,
   decidable.by_cases
     (assume : b = 0,
       by rw [this, div_zero, mul_zero, zero_mul, div_zero])
     (assume : b ≠ 0, division_ring.one_div_mul_one_div ha this))

lemma one_div_neg_eq_neg_one_div (a : α) : 1 / (- a) = - (1 / a) :=
decidable.by_cases
  (assume : a = 0, by rw [this, neg_zero, div_zero, neg_zero])
  (assume : a ≠ 0, division_ring.one_div_neg_eq_neg_one_div this)

lemma neg_div_neg_eq (a b : α) : (-a) / (-b) = a / b :=
decidable.by_cases
  (assume hb : b = 0, by rw [hb, neg_zero, div_zero, div_zero])
  (assume hb : b ≠ 0, division_ring.neg_div_neg_eq _ hb)

lemma one_div_one_div (a : α) : 1 / (1 / a) = a :=
decidable.by_cases
  (assume ha : a = 0, by rw [ha, div_zero, div_zero])
  (assume ha : a ≠ 0, division_ring.one_div_one_div ha)

lemma eq_of_one_div_eq_one_div {a b : α} (h : 1 / a = 1 / b) : a = b :=
decidable.by_cases
  (assume ha : a = 0,
   have hb : b = 0, from eq_zero_of_one_div_eq_zero (by rw [← h, ha, div_zero]),
   hb.symm ▸ ha)
  (assume ha : a ≠ 0,
   have hb : b ≠ 0, from ne_zero_of_one_div_ne_zero (h ▸ (one_div_ne_zero ha)),
   division_ring.eq_of_one_div_eq_one_div ha hb h)

lemma mul_inv' (a b : α) : (b * a)⁻¹ = a⁻¹ * b⁻¹ :=
decidable.by_cases
  (assume ha : a = 0, by rw [ha, mul_zero, inv_zero, zero_mul])
  (assume ha : a ≠ 0,
    decidable.by_cases
      (assume hb : b = 0, by rw [hb, zero_mul, inv_zero, mul_zero])
      (assume hb : b ≠ 0, mul_inv_eq ha hb))

-- the following are specifically for fields
lemma one_div_mul_one_div (a b : α) : (1 / a) * (1 / b) =  1 / (a * b) :=
by rw [one_div_mul_one_div', mul_comm b]

lemma div_mul_right {a : α} (b : α) (ha : a ≠ 0) : a / (a * b) = 1 / b :=
decidable.by_cases
  (assume hb : b = 0, by rw [hb, mul_zero, div_zero, div_zero])
  (assume hb : b ≠ 0, field.div_mul_right hb (mul_ne_zero ha hb))

lemma div_mul_left (a : α) {b : α} (hb : b ≠ 0) : b / (a * b) = 1 / a :=
by rw [mul_comm a, div_mul_right _ hb]

lemma div_mul_div (a b c d : α) : (a / b) * (c / d) = (a * c) / (b * d) :=
decidable.by_cases
  (assume hb : b = 0, by rw [hb, div_zero, zero_mul, zero_mul, div_zero])
  (assume hb : b ≠ 0,
    decidable.by_cases
      (assume hd : d = 0, by rw [hd, div_zero, mul_zero, mul_zero, div_zero])
      (assume hd : d ≠ 0, field.div_mul_div _ _ hb hd))

lemma mul_div_mul_left' (a b : α) {c : α} (hc : c ≠ 0) : (c * a) / (c * b) = a / b :=
decidable.by_cases
  (assume hb : b = 0, by rw [hb, mul_zero, div_zero, div_zero])
  (assume hb : b ≠ 0, mul_div_mul_left _ hb hc)

lemma mul_div_mul_right' (a b : α) {c : α} (hc : c ≠ 0) : (a * c) / (b * c) = a / b :=
by rw [mul_comm a, mul_comm b, (mul_div_mul_left' _ _ hc)]

lemma div_mul_eq_mul_div_comm (a b c : α) : (b / c) * a = b * (a / c) :=
decidable.by_cases
  (assume hc : c = 0, by rw [hc, div_zero, zero_mul, div_zero, mul_zero])
  (assume hc : c ≠ 0, field.div_mul_eq_mul_div_comm _ _ hc)

lemma one_div_div (a b : α) : 1 / (a / b) = b / a :=
decidable.by_cases
  (assume ha : a = 0, by rw [ha, zero_div, div_zero, div_zero])
  (assume ha : a ≠ 0,
    decidable.by_cases
      (assume hb : b = 0, by rw [hb, div_zero, zero_div, div_zero])
      (assume hb : b ≠ 0, division_ring.one_div_div ha hb))

lemma div_div_eq_mul_div (a b c : α) : a / (b / c) = (a * c) / b :=
by rw [div_eq_mul_one_div, one_div_div, ← mul_div_assoc]

lemma div_div_eq_div_mul (a b c : α) : (a / b) / c = a / (b * c) :=
by rw [div_eq_mul_one_div, div_mul_div, mul_one]

lemma div_div_div_div_eq (a b c d : α) : (a / b) / (c / d) = (a * d) / (b * c) :=
by rw [div_div_eq_mul_div, div_mul_eq_mul_div, div_div_eq_div_mul]

lemma div_helper {a : α} (b : α) (h : a ≠ 0) : (1 / (a * b)) * a = 1 / b :=
by rw [div_mul_eq_mul_div, one_mul, div_mul_right _ h]

lemma div_mul_eq_div_mul_one_div (a b c : α) : a / (b * c) = (a / b) * (1 / c) :=
by rw [← div_div_eq_div_mul, ← div_eq_mul_one_div]

end discrete_field
