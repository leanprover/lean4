/-
Copyright (c) 2015 Jacob Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Gross, Jeremy Avigad

Extended reals.
-/
import data.real
open real eq.ops classical

-- This is a hack, to get around the fact that the top level names are inaccessible when
-- defining these theorems in the ereal namespace. Is there a better way?
private definition zero_mul' := @zero_mul
private definition mul_zero' := @mul_zero
private definition neg_neg'  := @neg_neg

noncomputable theory

inductive ereal : Type :=
| of_real : ℝ → ereal
| infty : ereal
| neginfty : ereal

attribute ereal.of_real [coercion]
notation `∞` := ereal.infty
notation `-∞` := ereal.neginfty

namespace ereal

protected definition prio := num.pred real.prio

/- arithmetic operations on the ereals -/

definition ereal_has_zero [instance] [priority ereal.prio] : has_zero ereal :=
has_zero.mk (of_real 0)

definition ereal_has_one [instance] [priority ereal.prio] : has_one ereal :=
has_one.mk (of_real 1)

protected definition add : ereal → ereal → ereal
| (of_real x) (of_real y) := of_real (x + y)
| ∞ _                     := ∞
| _ ∞                     := ∞
| -∞ _                    := -∞
| _ -∞                    := -∞

protected definition neg : ereal → ereal
| (of_real x) := of_real (-x)
| ∞           := -∞
| -∞          := ∞

private definition blow_up [reducible] : ereal → ereal
| (of_real x) := if x = 0 then of_real 0 else if x > 0 then ∞ else -∞
| ∞           := ∞
| -∞          := -∞

protected definition mul : ereal → ereal → ereal
| (of_real x) (of_real y) := of_real (x * y)
| ∞ a                     := blow_up a
| a ∞                     := blow_up a
| -∞ a                    := ereal.neg (blow_up a)
| a -∞                    := ereal.neg (blow_up a)

definition ereal_has_add [instance] [priority ereal.prio] : has_add ereal :=
has_add.mk ereal.add

definition ereal_has_neg [instance] [priority ereal.prio] : has_neg ereal :=
has_neg.mk ereal.neg

protected definition sub (u v : ereal) : ereal := u + -v

definition ereal_has_sub [instance] [priority ereal.prio] : has_sub ereal :=
has_sub.mk ereal.sub

definition ereal_has_mul [instance] [priority ereal.prio] : has_mul ereal :=
has_mul.mk ereal.mul

protected theorem zero_def : (0 : ereal) = of_real 0 := rfl

protected theorem one_def : (1 : ereal) = of_real 1 := rfl

protected theorem add_def (x y : ereal) : x + y = ereal.add x y := rfl

protected theorem neg_def (x : ereal) : -x = ereal.neg x := rfl

protected theorem sub_eq_add_neg (u v : ereal) : u - v = u + -v := rfl

protected theorem mul_def (x y : ereal) : x * y = ereal.mul x y := rfl

theorem of_real.inj {x y : real} (H : of_real x = of_real y) : x = y :=
ereal.no_confusion H (assume H1, H1)

abbreviation eq_of_of_real_eq_of_real := @of_real.inj

theorem of_real_add (x y : real) : of_real (x + y) = of_real x + of_real y := rfl

theorem of_real_mul (x y : real) : of_real (x * y) = of_real x * of_real y := rfl

theorem infty_ne_neg_infty : ∞ ≠ -∞ := ereal.no_confusion

theorem infty_ne_of_real (x : real) : ∞ ≠ of_real x := ereal.no_confusion

theorem neg_infty_ne_of_real (x : real) : -∞ ≠ of_real x := ereal.no_confusion

/- properties of the arithmetic operations -/

protected theorem add_comm : ∀ u v : ereal, u + v = v + u
| (of_real x) (of_real y) := congr_arg of_real !add.comm
| ∞ v                     := by rewrite[*ereal.add_def, ↑ereal.add]
| u ∞                     := by rewrite[*ereal.add_def, ↑ereal.add]
| -∞ v                    := by rewrite[*ereal.add_def, ↑ereal.add]
| u -∞                    := by rewrite[*ereal.add_def, ↑ereal.add]

theorem infty_add : ∀ u, ∞ + u = ∞
| (of_real x) := rfl
| ∞           := rfl
| -∞          := rfl

theorem add_infty : ∀ u, u + ∞ = ∞
| (of_real x) := rfl
| ∞           := rfl
| -∞          := rfl

protected theorem add_assoc : ∀ u v w : ereal, (u + v) + w = u + (v + w)
| (of_real x) (of_real y) (of_real z) := congr_arg of_real !add.assoc
| ∞ v w                               := by rewrite [*infty_add, *add_infty]
| u ∞ w                               := by rewrite [*infty_add, *add_infty, infty_add]
| u v ∞                               := by rewrite [*infty_add, *add_infty]
| (of_real x) (of_real y) -∞          := by rewrite[*ereal.add_def, ↑ereal.add]
| (of_real x) -∞ (of_real z)          := by rewrite[*ereal.add_def, ↑ereal.add]
| -∞ (of_real y) (of_real z)          := by rewrite[*ereal.add_def, ↑ereal.add]
| (of_real x) -∞ -∞                   := by rewrite[*ereal.add_def, ↑ereal.add]
| -∞ (of_real y) -∞                   := rfl
| -∞ -∞ (of_real z)                   := by rewrite[*ereal.add_def, ↑ereal.add]
| -∞ -∞ -∞                            := rfl

protected theorem zero_add : ∀ u : ereal, 0 + u = u
| (of_real x) := congr_arg of_real !real.zero_add
| ∞           := rfl
| -∞          := rfl

protected theorem add_zero : ∀ u : ereal, u + 0 = u :=
by intro u; rewrite [ereal.add_comm, ereal.zero_add]

protected theorem mul_comm : ∀ u v : ereal, u * v = v * u
| (of_real x) (of_real y) := congr_arg of_real !mul.comm
| ∞ a                     := by rewrite [*ereal.mul_def, ↑ereal.mul]
| a ∞                     := by rewrite [*ereal.mul_def, ↑ereal.mul]
| -∞ a                    := by rewrite [*ereal.mul_def, ↑ereal.mul]
| a -∞                    := by rewrite [*ereal.mul_def, ↑ereal.mul]

protected theorem neg_neg : ∀ u : ereal, -(-u) = u
| ∞           := rfl
| (of_real x) := by rewrite [*ereal.neg_def, ↑ereal.neg, ▸*,
                             (neg_neg' x)]
| -∞          := rfl

theorem neg_infty : -∞ = - ∞  := rfl

protected theorem neg_zero : -(0 : ereal) = 0 := rfl

theorem infty_mul_pos {x : real} (H : x > 0) : ∞ * x = ∞ :=
have H1 : x ≠ 0, from ne_of_gt H,
by rewrite [*ereal.mul_def, ↑ereal.mul, if_neg H1, if_pos H]

theorem pos_mul_infty {x : real} (H : x > 0) : x * ∞ = ∞ :=
by rewrite [ereal.mul_comm, infty_mul_pos H]

theorem infty_mul_neg {x : real} (H : x < 0) : ∞ * x = -∞ :=
have H1 : x ≠ 0, from ne_of_lt H,
have H2 : ¬ x > 0, from not_lt_of_gt H,
by rewrite [*ereal.mul_def, ↑ereal.mul, if_neg H1, if_neg H2]

theorem neg_mul_infty {x : real} (H : x < 0) : x * ∞ = -∞ :=
by rewrite [ereal.mul_comm, infty_mul_neg H]

private theorem infty_mul_zero : ∞ * 0 = 0 :=
by rewrite [*ereal.mul_def, ↑ereal.mul, ereal.zero_def, ↑blow_up, if_pos rfl]

private theorem zero_mul_infty : 0 * ∞ = 0 :=
by rewrite [ereal.mul_comm, infty_mul_zero]

theorem infty_mul_infty : ∞ * ∞ = ∞ := rfl

protected theorem neg_of_real (x : real) : -(of_real x) = of_real (-x) :=
rfl

private theorem aux1 : ∀ v : ereal, -∞ * v = -(∞ * v)
| ∞           := rfl
| (of_real x) := rfl
| -∞          := rfl

private theorem aux2 : ∀ u : ereal, -u * ∞ = -(u * ∞)
| ∞ := rfl
| (of_real x) := lt.by_cases
                   (assume H : x < 0,
                      by rewrite [ereal.neg_of_real, pos_mul_infty (neg_pos_of_neg H),
                                  neg_mul_infty H])
                   (assume H : x = 0,
                      by krewrite [H, ereal.neg_zero, *zero_mul_infty, ereal.neg_zero])
                   (assume H : x > 0,
                      by rewrite [ereal.neg_of_real, neg_mul_infty (neg_neg_of_pos H),
                                   pos_mul_infty H])
| -∞ := rfl

theorem ereal_neg_mul : ∀ u v : ereal, -u * v = -(u * v)
| ∞ v                     := aux1 v
| -∞ v                    := by rewrite [aux1, *ereal.neg_neg]
| u ∞                     := by rewrite [-aux2]
| u -∞                    := by rewrite [ereal.mul_comm, ereal.mul_comm u,
                                         *aux1, ereal.mul_comm, aux2, *ereal.neg_neg]
| (of_real x) (of_real y) := congr_arg of_real (eq.symm (neg_mul_eq_neg_mul x y))

theorem ereal_mul_neg (u v : ereal) : u * -v = -(u * v) :=
by rewrite [*ereal.mul_comm u, ereal_neg_mul]

protected theorem mul_zero : ∀ u : ereal, u * 0 = 0
| ∞ := infty_mul_zero
| -∞ := by rewrite [neg_infty, ereal_neg_mul, infty_mul_zero]
| (of_real x) := congr_arg of_real (mul_zero' x)

protected theorem zero_mul (u : ereal) : 0 * u = 0 :=
by rewrite [ereal.mul_comm, ereal.mul_zero]

private theorem aux3 : ∀ u, ∞ * (∞ * u) = ∞ * u
| ∞           := rfl
| (of_real x) := if H : x = 0 then
                   by rewrite [*ereal.mul_def, ↑ereal.mul, ↑blow_up, *H, *if_pos rfl]
                 else if H1 : x > 0 then
                   by rewrite [*ereal.mul_def, ↑ereal.mul, ↑blow_up, if_neg H, if_pos H1]
                 else
                   by rewrite [*ereal.mul_def, ↑ereal.mul, ↑blow_up, if_neg H, if_neg H1]
| -∞          := rfl

private theorem aux4 (x y : real) : ∞ * x * y = ∞ * (x * y) :=
lt.by_cases
  (assume H : x < 0,
    lt.by_cases
      (assume H1 : y < 0, by rewrite [infty_mul_neg H, neg_infty, ereal_neg_mul, -of_real_mul,
                                     infty_mul_neg H1, infty_mul_pos (mul_pos_of_neg_of_neg H H1)])
      (assume H1 : y = 0, by krewrite [H1, *ereal.mul_zero])
      (assume H1 : y > 0, by rewrite [infty_mul_neg H, neg_infty, *ereal_neg_mul, -of_real_mul,
                                     infty_mul_pos H1, infty_mul_neg (mul_neg_of_neg_of_pos H H1)]))
  (assume H : x = 0,
    by krewrite [H, ereal.mul_zero, *ereal.zero_mul, ereal.mul_zero])
  (assume H : x > 0,
    lt.by_cases
      (assume H1 : y < 0, by rewrite [infty_mul_pos H, infty_mul_neg H1, -of_real_mul,
                                     infty_mul_neg (mul_neg_of_pos_of_neg H H1)])
      (assume H1 : y = 0, by krewrite [H1, *ereal.mul_zero])
      (assume H1 : y > 0, by rewrite [infty_mul_pos H, infty_mul_pos H1, -of_real_mul,
                                     infty_mul_pos (mul_pos H H1)]))

private theorem aux5 : ∀ u v, ∞ * u * v = ∞ * (u * v)
| ∞ v  := by rewrite [infty_mul_infty, aux3]
| u ∞  := by rewrite [-*ereal.mul_comm ∞]
| -∞ v := by rewrite [neg_infty, *ereal_neg_mul, *ereal_mul_neg, ereal_neg_mul, infty_mul_infty,
                      aux3]
| u -∞ := by rewrite [neg_infty, *ereal_mul_neg]
| (of_real x) (of_real y) := aux4 x y

protected theorem mul_assoc : ∀ u v w : ereal, u * v * w = u * (v * w)
| ∞ v w  := !aux5
| u ∞ w  := by rewrite [-*ereal.mul_comm ∞, *ereal.mul_comm u, *aux5, *ereal.mul_comm u]
| u v ∞  := by rewrite [-*ereal.mul_comm ∞, *ereal.mul_comm u, aux5]
| -∞ v w := by rewrite [neg_infty, *ereal_neg_mul, aux5]
| u -∞ w := by rewrite [neg_infty, *ereal_mul_neg, *ereal_neg_mul, ereal_mul_neg, *ereal.mul_comm u,
                        *aux5, ereal.mul_comm u]
| u v -∞ := by rewrite [neg_infty, *ereal_mul_neg, *ereal.mul_comm u, -*ereal.mul_comm ∞, aux5]
| (of_real x) (of_real y) (of_real z) := congr_arg of_real (mul.assoc x y z)

protected theorem one_mul : ∀ u : ereal, of_real 1 * u = u
| (of_real x) := !real.one_mul ▸ rfl
| ∞           := pos_mul_infty zero_lt_one
| -∞          := by rewrite [neg_infty, ereal_mul_neg, pos_mul_infty zero_lt_one]

protected theorem mul_one (u : ereal) : u * 1 = u :=
by krewrite [ereal.mul_comm, ereal.one_mul]

/- instantiating arithmetic structures -/

-- Note that distributivity fails, e.g. ∞ ⬝ (-1 + 1) ≠ ∞ * -1 + ∞ * 1

protected definition comm_monoid [trans_instance] : comm_monoid ereal :=
⦃comm_monoid,
  mul       := ereal.mul,
  mul_assoc := ereal.mul_assoc,
  one       := 1,
  one_mul   := ereal.one_mul,
  mul_one   := ereal.mul_one,
  mul_comm  := ereal.mul_comm
⦄

protected definition add_comm_monoid [trans_instance] : add_comm_monoid ereal :=
⦃add_comm_monoid,
  add       := ereal.add,
  add_assoc := ereal.add_assoc,
  zero      := 0,
  zero_add  := ereal.zero_add,
  add_zero  := ereal.add_zero,
  add_comm  := ereal.add_comm
⦄

/- ordering on the ereals -/

protected definition le : ereal → ereal → Prop
| u ∞                     := true
| -∞ v                    := true
| (of_real x) (of_real y) := x ≤ y
| (of_real x) -∞          := false
| ∞ (of_real y)           := false
| ∞ -∞                    := false

definition ereal_has_le [instance] [priority ereal.prio] : has_le ereal :=
has_le.mk ereal.le

theorem of_real_le_of_real (x y : real) : of_real x ≤ of_real y ↔ x ≤ y :=
!iff.refl

theorem le_infty : ∀ u, u ≤ ∞
| ∞           := trivial
| (of_real x) := trivial
| -∞          := trivial

theorem neg_infty_le : ∀ v, -∞ ≤ v
| ∞           := trivial
| (of_real x) := trivial
| -∞          := trivial

protected theorem le_refl : ∀ u : ereal, u ≤ u
| ∞           := trivial
| -∞          := trivial
| (of_real x) := by rewrite [of_real_le_of_real]

protected theorem le_trans : ∀ u v w : ereal, u ≤ v → v ≤ w → u ≤ w
| u v ∞            H1 H2 := !le_infty
| -∞ v w           H1 H2 := !neg_infty_le
| u ∞ (of_real x)  H1 H2 := false.elim H2
| ∞ (of_real x) v  H1 H2 := false.elim H1
| ∞ -∞ v           H1 H2 := false.elim H1
| u (of_real x) -∞ H1 H2 := false.elim H2
| u ∞ -∞           H1 H2 := false.elim H2
| (of_real x) -∞ v H1 H2 := false.elim H1
| (of_real x) (of_real y) (of_real z) H1 H2 :=
    iff.mpr !of_real_le_of_real
      (le.trans (iff.mp !of_real_le_of_real H1) (iff.mp !of_real_le_of_real H2))

protected theorem le_antisymm : ∀ u v : ereal, u ≤ v → v ≤ u → u = v
| ∞ ∞            H1 H2 := rfl
| ∞ (of_real x)  H1 H2 := false.elim H1
| ∞ -∞           H1 H2 := false.elim H1
| -∞ -∞          H1 H2 := rfl
| -∞ (of_real x) H1 H2 := false.elim H2
| -∞ ∞           H1 H2 := false.elim H2
| (of_real x) ∞  H1 H2 := false.elim H2
| (of_real x) -∞ H1 H2 := false.elim H1
| (of_real x) (of_real y) H1 H2 :=
    congr_arg of_real (le.antisymm (iff.mp !of_real_le_of_real H1) (iff.mp !of_real_le_of_real H2))

protected definition lt (x y : ereal) : Prop := x ≤ y ∧ x ≠ y

definition ereal_has_lt [instance] [priority ereal.prio] :
  has_lt ereal :=
has_lt.mk ereal.lt

protected theorem le_iff_lt_or_eq (u v : ereal) : u ≤ v ↔ u < v ∨ u = v :=
iff.intro
  (assume H : u ≤ v,
    by_cases
      (assume H1 : u = v, or.inr H1)
      (assume H1 : u ≠ v, or.inl (and.intro H H1)))
  (assume H : u < v ∨ u = v,
    or.elim H
      (assume H1 : u < v, and.left H1)
      (assume H1 : u = v, by rewrite H1; apply ereal.le_refl))

protected theorem le_total : ∀ u v : ereal, u ≤ v ∨ v ≤ u
| u ∞  := or.inl (le_infty u)
| u -∞ := or.inr (neg_infty_le u)
| ∞ v  := or.inr (le_infty v)
| -∞ v := or.inl (neg_infty_le v)
| (of_real x) (of_real y) :=
    or.elim (le.total x y)
      (assume H : x ≤[real] y, or.inl (iff.mpr !of_real_le_of_real H))
      (assume H : x ≥[real] y, or.inr (iff.mpr !of_real_le_of_real H))

theorem neg_infty_lt_infty : -∞ < ∞ := and.intro trivial (ne.symm infty_ne_neg_infty)

theorem neg_infty_lt_of_real (x : real) : -∞ < of_real x :=  and.intro trivial !neg_infty_ne_of_real

theorem of_real_lt_infty (x : real) : of_real x < ∞ := and.intro trivial (ne.symm !infty_ne_of_real)

protected definition decidable_linear_order [trans_instance] : decidable_linear_order ereal :=
⦃decidable_linear_order,
  le              := ereal.le,
  le_refl         := ereal.le_refl,
  le_trans        := ereal.le_trans,
  le_antisymm     := ereal.le_antisymm,
  lt              := ereal.lt,
  le_iff_lt_or_eq := ereal.le_iff_lt_or_eq,
  lt_irrefl       := abstract λ u H, and.right H rfl end,
  decidable_lt    := abstract λ u v : ereal, prop_decidable (u < v) end,
  le_total        := ereal.le_total
⦄

-- TODO : we still need some properties relating the arithmetic operations and the order.

end ereal
