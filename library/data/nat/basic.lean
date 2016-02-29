/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad

Basic operations on the natural numbers.
-/
import ..num algebra.ring
open binary eq.ops

namespace nat

/- a variant of add, defined by recursion on the first argument -/

definition addl (x y : ℕ) : ℕ :=
nat.rec y (λ n r, succ r) x
infix ` ⊕ `:65 := addl

theorem addl_succ_right (n m : ℕ) : n ⊕ succ m = succ (n ⊕ m) :=
nat.induction_on n
  rfl
  (λ n₁ ih, calc
    succ n₁ ⊕ succ m = succ (n₁ ⊕ succ m)   : rfl
             ...     = succ (succ (n₁ ⊕ m)) : ih
             ...     = succ (succ n₁ ⊕ m)   : rfl)

theorem add_eq_addl (x : ℕ) : ∀y, x + y = x ⊕ y :=
nat.induction_on x
  (λ y, nat.induction_on y
    rfl
    (λ y₁ ih, calc
      0 + succ y₁ = succ (0 + y₁)  : rfl
           ...    = succ (0 ⊕ y₁) : {ih}
           ...    = 0 ⊕ (succ y₁) : rfl))
  (λ x₁ ih₁ y, nat.induction_on y
    (calc
      succ x₁ + 0  = succ (x₁ + 0)  : rfl
               ... = succ (x₁ ⊕ 0) : {ih₁ 0}
               ... = succ x₁ ⊕ 0   : rfl)
    (λ y₁ ih₂, calc
      succ x₁ + succ y₁ = succ (succ x₁ + y₁) : rfl
                   ...  = succ (succ x₁ ⊕ y₁) : {ih₂}
                   ...  = succ x₁ ⊕ succ y₁   : addl_succ_right))

/- successor and predecessor -/

theorem succ_ne_zero [simp] (n : ℕ) : succ n ≠ 0 :=
by contradiction

theorem add_one_ne_zero [simp] (n : ℕ) : n + 1 ≠ 0 :=
by contradiction

-- add_rewrite succ_ne_zero

theorem pred_zero [simp] : pred 0 = 0 :=
rfl

theorem pred_succ [simp] (n : ℕ) : pred (succ n) = n :=
rfl

theorem eq_zero_or_eq_succ_pred (n : ℕ) : n = 0 ∨ n = succ (pred n) :=
nat.induction_on n
  (or.inl rfl)
  (take m IH, or.inr
    (show succ m = succ (pred (succ m)), from congr_arg succ !pred_succ⁻¹))

theorem exists_eq_succ_of_ne_zero {n : ℕ} (H : n ≠ 0) : ∃k : ℕ, n = succ k :=
exists.intro _ (or_resolve_right !eq_zero_or_eq_succ_pred H)

theorem succ.inj {n m : ℕ} (H : succ n = succ m) : n = m :=
nat.no_confusion H imp.id

abbreviation eq_of_succ_eq_succ := @succ.inj

theorem succ_ne_self {n : ℕ} : succ n ≠ n :=
nat.induction_on n
  (take H : 1 = 0,
    have ne : 1 ≠ 0, from !succ_ne_zero,
    absurd H ne)
  (take k IH H, IH (succ.inj H))

theorem discriminate {B : Prop} {n : ℕ} (H1: n = 0 → B) (H2 : ∀m, n = succ m → B) : B :=
have H : n = n → B, from nat.cases_on n H1 H2,
H rfl

theorem two_step_induction_on {P : ℕ → Prop} (a : ℕ) (H1 : P 0) (H2 : P 1)
    (H3 : ∀ (n : ℕ) (IH1 : P n) (IH2 : P (succ n)), P (succ (succ n))) : P a :=
have stronger : P a ∧ P (succ a), from
  nat.induction_on a
    (and.intro H1 H2)
    (take k IH,
      have IH1 : P k, from and.elim_left IH,
      have IH2 : P (succ k), from and.elim_right IH,
        and.intro IH2 (H3 k IH1 IH2)),
  and.elim_left stronger

theorem sub_induction {P : ℕ → ℕ → Prop} (n m : ℕ) (H1 : ∀m, P 0 m)
   (H2 : ∀n, P (succ n) 0) (H3 : ∀n m, P n m → P (succ n) (succ m)) : P n m :=
have general : ∀m, P n m, from nat.induction_on n H1
  (take k : ℕ,
    assume IH : ∀m, P k m,
    take m : ℕ,
    nat.cases_on m (H2 k) (take l, (H3 k l (IH l)))),
general m

/- addition -/

protected theorem add_zero (n : ℕ) : n + 0 = n :=
rfl

theorem add_succ (n m : ℕ) : n + succ m = succ (n + m) :=
rfl

/-
Remark: we use 'local attributes' because in the end of the file
we show not is a comm_semiring, and we will automatically inherit
the associated [simp] lemmas from algebra
-/
local attribute nat.add_zero nat.add_succ [simp]

protected theorem zero_add (n : ℕ) : 0 + n = n :=
by rec_simp

theorem succ_add (n m : ℕ) : (succ n) + m = succ (n + m) :=
by rec_simp

local attribute nat.zero_add nat.succ_add [simp]

protected theorem add_comm (n m : ℕ) : n + m = m + n :=
by rec_simp

theorem succ_add_eq_succ_add (n m : ℕ) : succ n + m = n + succ m :=
by simp

protected theorem add_assoc (n m k : ℕ) : (n + m) + k = n + (m + k) :=
by rec_simp

protected theorem add_left_comm : Π (n m k : ℕ), n + (m + k) = m + (n + k) :=
left_comm nat.add_comm nat.add_assoc

local attribute nat.add_comm nat.add_assoc nat.add_left_comm [simp]

protected theorem add_right_comm : Π (n m k : ℕ), n + m + k = n + k + m :=
right_comm nat.add_comm nat.add_assoc

protected theorem add_left_cancel {n m k : ℕ} : n + m = n + k → m = k :=
nat.induction_on n
  (by simp)
  (take a iH,
    -- TODO(Leo): replace with forward reasoning after we add strategies for it.
    have succ (a + m) = succ (a + k) → a + m = a + k, from !succ.inj,
    by inst_simp)

protected theorem add_right_cancel {n m k : ℕ} (H : n + m = k + m) : n = k :=
have H2 : m + n = m + k, by simp,
nat.add_left_cancel H2

theorem eq_zero_of_add_eq_zero_right {n m : ℕ} : n + m = 0 → n = 0 :=
nat.induction_on n
  (by simp)
  (take k iH, assume H : succ k + m = 0,
    absurd
      (show succ (k + m) = 0, by simp)
      !succ_ne_zero)

theorem eq_zero_of_add_eq_zero_left {n m : ℕ} (H : n + m = 0) : m = 0 :=
eq_zero_of_add_eq_zero_right (!nat.add_comm ⬝ H)

theorem eq_zero_and_eq_zero_of_add_eq_zero {n m : ℕ} (H : n + m = 0) : n = 0 ∧ m = 0 :=
and.intro (eq_zero_of_add_eq_zero_right H) (eq_zero_of_add_eq_zero_left H)

theorem add_one (n : ℕ) : n + 1 = succ n := rfl

local attribute add_one [simp]

theorem one_add (n : ℕ) : 1 + n = succ n :=
by simp

theorem succ_eq_add_one (n : ℕ) : succ n = n + 1 :=
rfl

/- multiplication -/

protected theorem mul_zero (n : ℕ) : n * 0 = 0 :=
rfl

theorem mul_succ (n m : ℕ) : n * succ m = n * m + n :=
rfl

local attribute nat.mul_zero nat.mul_succ [simp]

-- commutativity, distributivity, associativity, identity

protected theorem zero_mul (n : ℕ) : 0 * n = 0 :=
by rec_simp

theorem succ_mul (n m : ℕ) : (succ n) * m = (n * m) + m :=
by rec_simp

local attribute nat.zero_mul nat.succ_mul [simp]

protected theorem mul_comm (n m : ℕ) : n * m = m * n :=
by rec_simp

protected theorem right_distrib (n m k : ℕ) : (n + m) * k = n * k + m * k :=
by rec_simp

protected theorem left_distrib (n m k : ℕ) : n * (m + k) = n * m + n * k :=
by rec_simp

local attribute nat.mul_comm nat.right_distrib nat.left_distrib [simp]

protected theorem mul_assoc (n m k : ℕ) : (n * m) * k = n * (m * k) :=
by rec_simp

local attribute nat.mul_assoc [simp]

protected theorem mul_one (n : ℕ) : n * 1 = n :=
calc
  n * 1 = n * 0 + n : mul_succ
    ... = n         : by simp

local attribute nat.mul_one [simp]

protected theorem one_mul (n : ℕ) : 1 * n = n :=
by simp

local attribute nat.one_mul [simp]

theorem eq_zero_or_eq_zero_of_mul_eq_zero {n m : ℕ} : n * m = 0 → n = 0 ∨ m = 0 :=
nat.cases_on n (by simp)
  (take n',
    nat.cases_on m
      (by simp)
      (take m', assume H,
        absurd
          (show succ (succ n' * m' + n') = 0, by simp)
          !succ_ne_zero))

protected definition comm_semiring [trans_instance] : comm_semiring nat :=
⦃comm_semiring,
 add            := nat.add,
 add_assoc      := nat.add_assoc,
 zero           := nat.zero,
 zero_add       := nat.zero_add,
 add_zero       := nat.add_zero,
 add_comm       := nat.add_comm,
 mul            := nat.mul,
 mul_assoc      := nat.mul_assoc,
 one            := nat.succ nat.zero,
 one_mul        := nat.one_mul,
 mul_one        := nat.mul_one,
 left_distrib   := nat.left_distrib,
 right_distrib  := nat.right_distrib,
 zero_mul       := nat.zero_mul,
 mul_zero       := nat.mul_zero,
 mul_comm       := nat.mul_comm⦄

end nat

section
open nat
definition iterate {A : Type} (op : A → A) : ℕ → A → A
 | 0 := λ a, a
 | (succ k) := λ a, op (iterate k a)

notation f`^[`n`]` := iterate f n
end
