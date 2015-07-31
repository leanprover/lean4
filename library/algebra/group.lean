/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Various multiplicative and additive structures. Partially modeled on Isabelle's library.
-/

import logic.eq data.unit data.sigma data.prod
import algebra.binary algebra.priority

open eq eq.ops   -- note: ⁻¹ will be overloaded
open binary

namespace algebra

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

infixl [priority algebra.prio] `*`   := has_mul.mul
infixl [priority algebra.prio] `+`   := has_add.add
postfix [priority algebra.prio] `⁻¹` := has_inv.inv
prefix [priority algebra.prio] `-`   := has_neg.neg
notation 1  := !has_one.one
notation 0  := !has_zero.zero

/- semigroup -/

structure semigroup [class] (A : Type) extends has_mul A :=
(mul_assoc : ∀a b c, mul (mul a b) c = mul a (mul b c))

theorem mul.assoc [s : semigroup A] (a b c : A) : a * b * c = a * (b * c) :=
!semigroup.mul_assoc

structure comm_semigroup [class] (A : Type) extends semigroup A :=
(mul_comm : ∀a b, mul a b = mul b a)

theorem mul.comm [s : comm_semigroup A] (a b : A) : a * b = b * a :=
!comm_semigroup.mul_comm

theorem mul.left_comm [s : comm_semigroup A] (a b c : A) : a * (b * c) = b * (a * c) :=
binary.left_comm (@mul.comm A s) (@mul.assoc A s) a b c

theorem mul.right_comm [s : comm_semigroup A] (a b c : A) : (a * b) * c = (a * c) * b :=
binary.right_comm (@mul.comm A s) (@mul.assoc A s) a b c

structure left_cancel_semigroup [class] (A : Type) extends semigroup A :=
(mul_left_cancel : ∀a b c, mul a b = mul a c → b = c)

theorem mul.left_cancel [s : left_cancel_semigroup A] {a b c : A} :
  a * b = a * c → b = c :=
!left_cancel_semigroup.mul_left_cancel

abbreviation eq_of_mul_eq_mul_left' := @mul.left_cancel

structure right_cancel_semigroup [class] (A : Type) extends semigroup A :=
(mul_right_cancel : ∀a b c, mul a b = mul c b → a = c)

theorem mul.right_cancel [s : right_cancel_semigroup A] {a b c : A} :
  a * b = c * b → a = c :=
!right_cancel_semigroup.mul_right_cancel

abbreviation eq_of_mul_eq_mul_right' := @mul.right_cancel

/- additive semigroup -/

structure add_semigroup [class] (A : Type) extends has_add A :=
(add_assoc : ∀a b c, add (add a b) c = add a (add b c))

theorem add.assoc [s : add_semigroup A] (a b c : A) : a + b + c = a + (b + c) :=
!add_semigroup.add_assoc

structure add_comm_semigroup [class] (A : Type) extends add_semigroup A :=
(add_comm : ∀a b, add a b = add b a)

theorem add.comm [s : add_comm_semigroup A] (a b : A) : a + b = b + a :=
!add_comm_semigroup.add_comm

theorem add.left_comm [s : add_comm_semigroup A] (a b c : A) :
  a + (b + c) = b + (a + c) :=
binary.left_comm (@add.comm A s) (@add.assoc A s) a b c

theorem add.right_comm [s : add_comm_semigroup A] (a b c : A) : (a + b) + c = (a + c) + b :=
binary.right_comm (@add.comm A s) (@add.assoc A s) a b c

structure add_left_cancel_semigroup [class] (A : Type) extends add_semigroup A :=
(add_left_cancel : ∀a b c, add a b = add a c → b = c)

theorem add.left_cancel [s : add_left_cancel_semigroup A] {a b c : A} :
  a + b = a + c → b = c :=
!add_left_cancel_semigroup.add_left_cancel

abbreviation eq_of_add_eq_add_left := @add.left_cancel

structure add_right_cancel_semigroup [class] (A : Type) extends add_semigroup A :=
(add_right_cancel : ∀a b c, add a b = add c b → a = c)

theorem add.right_cancel [s : add_right_cancel_semigroup A] {a b c : A} :
  a + b = c + b → a = c :=
!add_right_cancel_semigroup.add_right_cancel

abbreviation eq_of_add_eq_add_right := @add.right_cancel

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

definition add_monoid.to_monoid {A : Type} [s : add_monoid A] : monoid A :=
⦃ monoid,
  mul         := add_monoid.add,
  mul_assoc   := add_monoid.add_assoc,
  one         := add_monoid.zero A,
  mul_one     := add_monoid.add_zero,
  one_mul     := add_monoid.zero_add
⦄

definition add_comm_monoid.to_comm_monoid {A : Type} [s : add_comm_monoid A] : comm_monoid A :=
⦃ comm_monoid,
  add_monoid.to_monoid,
  mul_comm    := add_comm_monoid.add_comm
⦄

section add_comm_monoid

  theorem add_comm_three {A : Type} [s : add_comm_monoid A] (a b c : A) : a + b + c = c + b + a :=
    by rewrite [{a + _}add.comm, {_ + c}add.comm, -*add.assoc]

end add_comm_monoid

/- group -/

structure group [class] (A : Type) extends monoid A, has_inv A :=
(mul_left_inv : ∀a, mul (inv a) a = one)

-- Note: with more work, we could derive the axiom one_mul

section group

  variable [s : group A]
  include s

  theorem mul.left_inv (a : A) : a⁻¹ * a = 1 := !group.mul_left_inv

  theorem inv_mul_cancel_left (a b : A) : a⁻¹ * (a * b) = b :=
  by rewrite [-mul.assoc, mul.left_inv, one_mul]

  theorem inv_mul_cancel_right (a b : A) : a * b⁻¹ * b = a :=
  by rewrite [mul.assoc, mul.left_inv, mul_one]

  theorem inv_eq_of_mul_eq_one {a b : A} (H : a * b = 1) : a⁻¹ = b :=
  by rewrite [-mul_one a⁻¹, -H, inv_mul_cancel_left]

  theorem one_inv : 1⁻¹ = (1 : A) := inv_eq_of_mul_eq_one (one_mul 1)

  theorem inv_inv (a : A) : (a⁻¹)⁻¹ = a := inv_eq_of_mul_eq_one (mul.left_inv a)

  theorem inv.inj {a b : A} (H : a⁻¹ = b⁻¹) : a = b :=
  by rewrite [-inv_inv, H, inv_inv]

  theorem inv_eq_inv_iff_eq (a b : A) : a⁻¹ = b⁻¹ ↔ a = b :=
  iff.intro (assume H, inv.inj H) (assume H, congr_arg _ H)

  theorem inv_eq_one_iff_eq_one (a b : A) : a⁻¹ = 1 ↔ a = 1 :=
  one_inv ▸ inv_eq_inv_iff_eq a 1

  theorem eq_inv_of_eq_inv {a b : A} (H : a = b⁻¹) : b = a⁻¹ :=
  by rewrite [H, inv_inv]

  theorem eq_inv_iff_eq_inv (a b : A) : a = b⁻¹ ↔ b = a⁻¹ :=
  iff.intro !eq_inv_of_eq_inv !eq_inv_of_eq_inv

  theorem eq_inv_of_mul_eq_one {a b : A} (H : a * b = 1) : a = b⁻¹ :=
  begin rewrite [eq_inv_iff_eq_inv], apply eq.symm, exact inv_eq_of_mul_eq_one H end

  theorem mul.right_inv (a : A) : a * a⁻¹ = 1 :=
  calc
    a * a⁻¹ = (a⁻¹)⁻¹ * a⁻¹ : inv_inv
        ... = 1             : mul.left_inv

  theorem mul_inv_cancel_left (a b : A) : a * (a⁻¹ * b) = b :=
  calc
    a * (a⁻¹ * b) = a * a⁻¹ * b : by rewrite mul.assoc
      ... = 1 * b               : mul.right_inv
      ... = b                   : one_mul

  theorem mul_inv_cancel_right (a b : A) : a * b * b⁻¹ = a :=
  calc
    a * b * b⁻¹ = a * (b * b⁻¹) : mul.assoc
      ... = a * 1 : mul.right_inv
      ... = a : mul_one

  theorem mul_inv (a b : A) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  inv_eq_of_mul_eq_one
    (calc
      a * b * (b⁻¹ * a⁻¹) = a * (b * (b⁻¹ * a⁻¹)) : mul.assoc
        ... = a * a⁻¹                             : mul_inv_cancel_left
        ... = 1                                   : mul.right_inv)

  theorem eq_of_mul_inv_eq_one {a b : A} (H : a * b⁻¹ = 1) : a = b :=
  calc
    a = a * b⁻¹ * b : by rewrite inv_mul_cancel_right
      ... = 1 * b   : H
      ... = b       : one_mul

  theorem eq_mul_inv_of_mul_eq {a b c : A} (H : a * c = b) : a = b * c⁻¹ :=
  by rewrite [-H, mul_inv_cancel_right]

  theorem eq_inv_mul_of_mul_eq {a b c : A} (H : b * a = c) : a = b⁻¹ * c :=
  by rewrite [-H, inv_mul_cancel_left]

  theorem inv_mul_eq_of_eq_mul {a b c : A} (H : b = a * c) : a⁻¹ * b = c :=
  by rewrite [H, inv_mul_cancel_left]

  theorem mul_inv_eq_of_eq_mul {a b c : A} (H : a = c * b) : a * b⁻¹ = c :=
  by rewrite [H, mul_inv_cancel_right]

  theorem eq_mul_of_mul_inv_eq {a b c : A} (H : a * c⁻¹ = b) : a = b * c :=
  !inv_inv ▸ (eq_mul_inv_of_mul_eq H)

  theorem eq_mul_of_inv_mul_eq {a b c : A} (H : b⁻¹ * a = c) : a = b * c :=
  !inv_inv ▸ (eq_inv_mul_of_mul_eq H)

  theorem mul_eq_of_eq_inv_mul {a b c : A} (H : b = a⁻¹ * c) : a * b = c :=
  !inv_inv ▸ (inv_mul_eq_of_eq_mul H)

  theorem mul_eq_of_eq_mul_inv {a b c : A} (H : a = c * b⁻¹) : a * b = c :=
  !inv_inv ▸ (mul_inv_eq_of_eq_mul H)

  theorem mul_eq_iff_eq_inv_mul (a b c : A) : a * b = c ↔ b = a⁻¹ * c :=
  iff.intro eq_inv_mul_of_mul_eq mul_eq_of_eq_inv_mul

  theorem mul_eq_iff_eq_mul_inv (a b c : A) : a * b = c ↔ a = c * b⁻¹ :=
  iff.intro eq_mul_inv_of_mul_eq mul_eq_of_eq_mul_inv

  theorem mul_left_cancel {a b c : A} (H : a * b = a * c) : b = c :=
  by rewrite [-inv_mul_cancel_left a b, H, inv_mul_cancel_left]

  theorem mul_right_cancel {a b c : A} (H : a * b = c * b) : a = c :=
  by rewrite [-mul_inv_cancel_right a b, H, mul_inv_cancel_right]

  theorem mul_eq_one_of_mul_eq_one {a b : A} (H : b * a = 1) : a * b = 1 :=
  by rewrite [-inv_eq_of_mul_eq_one H, mul.left_inv]

  theorem mul_eq_one_iff_mul_eq_one (a b : A) : a * b = 1 ↔ b * a = 1 :=
  iff.intro !mul_eq_one_of_mul_eq_one !mul_eq_one_of_mul_eq_one

  definition conj_by (g a : A) := g * a * g⁻¹
  definition is_conjugate (a b : A) := ∃ x, conj_by x b = a

  local infixl `~` := is_conjugate
  local infixr `∘c`:55 := conj_by

  lemma conj_compose (f g a : A) : f ∘c g ∘c a = f*g ∘c a :=
      calc f ∘c g ∘c a = f * (g * a * g⁻¹) * f⁻¹ : rfl
      ... = f * (g * a) * g⁻¹ * f⁻¹ : mul.assoc
      ... = f * g * a * g⁻¹ * f⁻¹ : mul.assoc
      ... = f * g * a * (g⁻¹ * f⁻¹) : mul.assoc
      ... = f * g * a * (f * g)⁻¹ : mul_inv
  lemma conj_id (a : A) : 1 ∘c a = a :=
      calc 1 * a * 1⁻¹ = a * 1⁻¹ : one_mul
      ... = a * 1 : one_inv
      ... = a : mul_one
  lemma conj_one (g : A) : g ∘c 1 = 1 :=
      calc g * 1 * g⁻¹ = g * g⁻¹ : mul_one
      ... = 1 : mul.right_inv
  lemma conj_inv_cancel (g : A) : ∀ a, g⁻¹ ∘c g ∘c a = a :=
      assume a, calc
      g⁻¹ ∘c g ∘c a = g⁻¹*g ∘c a : conj_compose
      ... = 1 ∘c a : mul.left_inv
      ... = a : conj_id

  lemma conj_inv (g : A) : ∀ a, (g ∘c a)⁻¹ = g ∘c a⁻¹ :=
    take a, calc
    (g * a * g⁻¹)⁻¹ = g⁻¹⁻¹ * (g * a)⁻¹   : mul_inv
                ... = g⁻¹⁻¹ * (a⁻¹ * g⁻¹) : mul_inv
                ... = g⁻¹⁻¹ * a⁻¹ * g⁻¹   : mul.assoc
                ... = g * a⁻¹ * g⁻¹       : inv_inv

  lemma is_conj.refl (a : A) : a ~ a := exists.intro 1 (conj_id a)

  lemma is_conj.symm (a b : A) : a ~ b → b ~ a :=
      assume Pab, obtain x (Pconj : x ∘c b = a), from Pab,
      assert Pxinv : x⁻¹ ∘c x ∘c b = x⁻¹ ∘c a, from (congr_arg2 conj_by (eq.refl x⁻¹) Pconj),
      exists.intro x⁻¹ (eq.symm (conj_inv_cancel x b ▸ Pxinv))

  lemma is_conj.trans (a b c : A) : a ~ b → b ~ c → a ~ c :=
      assume Pab, assume Pbc,
      obtain x (Px : x ∘c b = a), from Pab,
      obtain y (Py : y ∘c c = b), from Pbc,
      exists.intro (x*y) (calc
      x*y ∘c c = x ∘c y ∘c c : conj_compose
      ... = x ∘c b : Py
      ... = a : Px)

  definition group.to_left_cancel_semigroup [trans-instance] [coercion] [reducible] :
    left_cancel_semigroup A :=
  ⦃ left_cancel_semigroup, s,
    mul_left_cancel := @mul_left_cancel A s ⦄

  definition group.to_right_cancel_semigroup [trans-instance] [coercion] [reducible] :
    right_cancel_semigroup A :=
  ⦃ right_cancel_semigroup, s,
    mul_right_cancel := @mul_right_cancel A s ⦄

end group

structure comm_group [class] (A : Type) extends group A, comm_monoid A

/- additive group -/

structure add_group [class] (A : Type) extends add_monoid A, has_neg A :=
(add_left_inv : ∀a, add (neg a) a = zero)

section add_group

  variables [s : add_group A]
  include s

  theorem add.left_inv (a : A) : -a + a = 0 := !add_group.add_left_inv

  theorem neg_add_cancel_left (a b : A) : -a + (a + b) = b :=
  by rewrite [-add.assoc, add.left_inv, zero_add]

  theorem neg_add_cancel_right (a b : A) : a + -b + b = a :=
  by rewrite [add.assoc, add.left_inv, add_zero]

  theorem neg_eq_of_add_eq_zero {a b : A} (H : a + b = 0) : -a = b :=
  by rewrite [-add_zero, -H, neg_add_cancel_left]

  theorem neg_zero : -0 = (0 : A) := neg_eq_of_add_eq_zero (zero_add 0)

  theorem neg_neg (a : A) : -(-a) = a := neg_eq_of_add_eq_zero (add.left_inv a)

  theorem eq_neg_of_add_eq_zero {a b : A} (H : a + b = 0) : a = -b :=
  by rewrite [-neg_eq_of_add_eq_zero H, neg_neg]

  theorem neg.inj {a b : A} (H : -a = -b) : a = b :=
  calc
    a = -(-a) : neg_neg
      ... = b : neg_eq_of_add_eq_zero (H⁻¹ ▸ (add.left_inv _))

  theorem neg_eq_neg_iff_eq (a b : A) : -a = -b ↔ a = b :=
  iff.intro (assume H, neg.inj H) (assume H, congr_arg _ H)

  theorem neg_eq_zero_iff_eq_zero (a : A) : -a = 0 ↔ a = 0 :=
  neg_zero ▸ !neg_eq_neg_iff_eq

  theorem eq_neg_of_eq_neg {a b : A} (H : a = -b) : b = -a :=
  H⁻¹ ▸ (neg_neg b)⁻¹

  theorem eq_neg_iff_eq_neg (a b : A) : a = -b ↔ b = -a :=
  iff.intro !eq_neg_of_eq_neg !eq_neg_of_eq_neg

  theorem add.right_inv (a : A) : a + -a = 0 :=
  calc
    a + -a = -(-a) + -a : neg_neg
      ... = 0 : add.left_inv

  theorem add_neg_cancel_left (a b : A) : a + (-a + b) = b :=
  by rewrite [-add.assoc, add.right_inv, zero_add]

  theorem add_neg_cancel_right (a b : A) : a + b + -b = a :=
  by rewrite [add.assoc, add.right_inv, add_zero]

  theorem neg_add_rev (a b : A) : -(a + b) = -b + -a :=
  neg_eq_of_add_eq_zero
    begin
      rewrite [add.assoc, add_neg_cancel_left, add.right_inv]
    end

  -- TODO: delete these in favor of sub rules?
  theorem eq_add_neg_of_add_eq {a b c : A} (H : a + c = b) : a = b + -c :=
  H ▸ !add_neg_cancel_right⁻¹

  theorem eq_neg_add_of_add_eq {a b c : A} (H : b + a = c) : a = -b + c :=
  H ▸ !neg_add_cancel_left⁻¹

  theorem neg_add_eq_of_eq_add {a b c : A} (H : b = a + c) : -a + b = c :=
  H⁻¹ ▸ !neg_add_cancel_left

  theorem add_neg_eq_of_eq_add {a b c : A} (H : a = c + b) : a + -b = c :=
  H⁻¹ ▸ !add_neg_cancel_right

  theorem eq_add_of_add_neg_eq {a b c : A} (H : a + -c = b) : a = b + c :=
  !neg_neg ▸ (eq_add_neg_of_add_eq H)

  theorem eq_add_of_neg_add_eq {a b c : A} (H : -b + a = c) : a = b + c :=
  !neg_neg ▸ (eq_neg_add_of_add_eq H)

  theorem add_eq_of_eq_neg_add {a b c : A} (H : b = -a + c) : a + b = c :=
  !neg_neg ▸ (neg_add_eq_of_eq_add H)

  theorem add_eq_of_eq_add_neg {a b c : A} (H : a = c + -b) : a + b = c :=
  !neg_neg ▸ (add_neg_eq_of_eq_add H)

  theorem add_eq_iff_eq_neg_add (a b c : A) : a + b = c ↔ b = -a + c :=
  iff.intro eq_neg_add_of_add_eq add_eq_of_eq_neg_add

  theorem add_eq_iff_eq_add_neg (a b c : A) : a + b = c ↔ a = c + -b :=
  iff.intro eq_add_neg_of_add_eq add_eq_of_eq_add_neg

  theorem add_left_cancel {a b c : A} (H : a + b = a + c) : b = c :=
  calc b = -a + (a + b) : !neg_add_cancel_left⁻¹
     ... = -a + (a + c) : H
     ... = c : neg_add_cancel_left

  theorem add_right_cancel {a b c : A} (H : a + b = c + b) : a = c :=
  calc a = (a + b) + -b : !add_neg_cancel_right⁻¹
     ... = (c + b) + -b : H
     ... = c : add_neg_cancel_right

  definition add_group.to_left_cancel_semigroup [trans-instance] [coercion] [reducible] :
    add_left_cancel_semigroup A :=
  ⦃ add_left_cancel_semigroup, s,
    add_left_cancel := @add_left_cancel A s ⦄

  definition add_group.to_add_right_cancel_semigroup [trans-instance] [coercion] [reducible] :
    add_right_cancel_semigroup A :=
  ⦃ add_right_cancel_semigroup, s,
    add_right_cancel := @add_right_cancel A s ⦄

  /- sub -/

  -- TODO: derive corresponding facts for div in a field
  definition sub [reducible] (a b : A) : A := a + -b

  infix [priority algebra.prio] `-` := sub

  theorem sub_eq_add_neg (a b : A) : a - b = a + -b := rfl

  theorem sub_self (a : A) : a - a = 0 := !add.right_inv

  theorem sub_add_cancel (a b : A) : a - b + b = a := !neg_add_cancel_right

  theorem add_sub_cancel (a b : A) : a + b - b = a := !add_neg_cancel_right

  theorem eq_of_sub_eq_zero {a b : A} (H : a - b = 0) : a = b :=
  calc
    a = (a - b) + b : !sub_add_cancel⁻¹
      ... = 0 + b : H
      ... = b : zero_add

  theorem eq_iff_sub_eq_zero (a b : A) : a = b ↔ a - b = 0 :=
  iff.intro (assume H, H ▸ !sub_self) (assume H, eq_of_sub_eq_zero H)

  theorem zero_sub (a : A) : 0 - a = -a := !zero_add

  theorem sub_zero (a : A) : a - 0 = a := subst (eq.symm neg_zero) !add_zero

  theorem sub_neg_eq_add (a b : A) : a - (-b) = a + b :=
  by change a + -(-b) = a + b; rewrite neg_neg

  theorem neg_sub (a b : A) : -(a - b) = b - a :=
  neg_eq_of_add_eq_zero
    (calc
      a - b + (b - a) = a - b + b - a : by krewrite -add.assoc
        ... = a - a                   : sub_add_cancel
        ... = 0                       : sub_self)

  theorem add_sub (a b c : A) : a + (b - c) = a + b - c := !add.assoc⁻¹

  theorem sub_add_eq_sub_sub_swap (a b c : A) : a - (b + c) = a - c - b :=
  calc
    a - (b + c) = a + (-c - b) : neg_add_rev
            ... = a - c - b    : by krewrite -add.assoc

  theorem sub_eq_iff_eq_add (a b c : A) : a - b = c ↔ a = c + b :=
  iff.intro (assume H, eq_add_of_add_neg_eq H) (assume H, add_neg_eq_of_eq_add H)

  theorem eq_sub_iff_add_eq (a b c : A) : a = b - c ↔ a + c = b :=
  iff.intro (assume H, add_eq_of_eq_add_neg H) (assume H, eq_add_neg_of_add_eq H)

  theorem eq_iff_eq_of_sub_eq_sub {a b c d : A} (H : a - b = c - d) : a = b ↔ c = d :=
  calc
    a = b ↔ a - b = 0   : eq_iff_sub_eq_zero
      ... = (c - d = 0) : H
      ... ↔ c = d       : iff.symm (eq_iff_sub_eq_zero c d)

  theorem eq_sub_of_add_eq {a b c : A} (H : a + c = b) : a = b - c :=
  !eq_add_neg_of_add_eq H

  theorem sub_eq_of_eq_add {a b c : A} (H : a = c + b) : a - b = c :=
  !add_neg_eq_of_eq_add H

  theorem eq_add_of_sub_eq {a b c : A} (H : a - c = b) : a = b + c :=
  eq_add_of_add_neg_eq H

  theorem add_eq_of_eq_sub {a b c : A} (H : a = c - b) : a + b = c :=
  add_eq_of_eq_add_neg H
end add_group

structure add_comm_group [class] (A : Type) extends add_group A, add_comm_monoid A

section add_comm_group
  variable [s : add_comm_group A]
  include s

  theorem sub_add_eq_sub_sub (a b c : A) : a - (b + c) = a - b - c :=
  !add.comm ▸ !sub_add_eq_sub_sub_swap

  theorem neg_add_eq_sub (a b : A) : -a + b = b - a := !add.comm

  theorem neg_add (a b : A) : -(a + b) = -a + -b := add.comm (-b) (-a) ▸ neg_add_rev a b

  theorem sub_add_eq_add_sub (a b c : A) : a - b + c = a + c - b := !add.right_comm

  theorem sub_sub (a b c : A) : a - b - c = a - (b + c) :=
  by rewrite [▸ a + -b + -c = _, add.assoc, -neg_add]

  theorem add_sub_add_left_eq_sub (a b c : A) : (c + a) - (c + b) = a - b :=
  by rewrite [sub_add_eq_sub_sub, (add.comm c a), add_sub_cancel]

  theorem eq_sub_of_add_eq' {a b c : A} (H : c + a = b) : a = b - c :=
  !eq_sub_of_add_eq (!add.comm ▸ H)

  theorem sub_eq_of_eq_add' {a b c : A} (H : a = b + c) : a - b = c :=
  !sub_eq_of_eq_add (!add.comm ▸ H)

  theorem eq_add_of_sub_eq' {a b c : A} (H : a - b = c) : a = b + c :=
  !add.comm ▸ eq_add_of_sub_eq H

  theorem add_eq_of_eq_sub' {a b c : A} (H : b = c - a) : a + b = c :=
  !add.comm ▸ add_eq_of_eq_sub H

  theorem sub_sub_self (a b : A) : a - (a - b) = b :=
  by rewrite [sub_eq_add_neg, neg_sub, add.comm, sub_add_cancel]
 
end add_comm_group

definition group_of_add_group (A : Type) [G : add_group A] : group A :=
⦃group,
  mul             := has_add.add,
  mul_assoc       := add.assoc,
  one             := !has_zero.zero,
  one_mul         := zero_add,
  mul_one         := add_zero,
  inv             := has_neg.neg,
  mul_left_inv    := add.left_inv⦄

end algebra
