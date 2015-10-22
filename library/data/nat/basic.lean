/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad

Basic operations on the natural numbers.
-/
import logic.connectives data.num algebra.binary algebra.ring
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

theorem succ_ne_zero (n : ℕ) : succ n ≠ 0 :=
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

protected theorem add_zero [simp] (n : ℕ) : n + 0 = n :=
rfl

theorem add_succ [simp] (n m : ℕ) : n + succ m = succ (n + m) :=
rfl

protected theorem zero_add [simp] (n : ℕ) : 0 + n = n :=
nat.induction_on n
    !nat.add_zero
    (take m IH, show 0 + succ m = succ m, from
      calc
        0 + succ m = succ (0 + m) : add_succ
               ... = succ m       : IH)

theorem succ_add [simp] (n m : ℕ) : (succ n) + m = succ (n + m) :=
nat.induction_on m
    (!nat.add_zero ▸ !nat.add_zero)
    (take k IH, calc
      succ n + succ k = succ (succ n + k)    : add_succ
                  ... = succ (succ (n + k))  : IH
                  ... = succ (n + succ k)    : add_succ)

protected theorem add_comm [simp] (n m : ℕ) : n + m = m + n :=
nat.induction_on m
    (by rewrite [nat.add_zero, nat.zero_add])
    (take k IH, calc
        n + succ k = succ (n+k)   : add_succ
               ... = succ (k + n) : IH
               ... = succ k + n   : succ_add)

theorem succ_add_eq_succ_add (n m : ℕ) : succ n + m = n + succ m :=
!succ_add ⬝ !add_succ⁻¹

protected theorem add_assoc [simp] (n m k : ℕ) : (n + m) + k = n + (m + k) :=
nat.induction_on k
    (by rewrite +nat.add_zero)
    (take l IH,
      calc
        (n + m) + succ l = succ ((n + m) + l)  : add_succ
                     ... = succ (n + (m + l))  : IH
                     ... = n + succ (m + l)    : add_succ
                     ... = n + (m + succ l)    : add_succ)

protected theorem add.left_comm : Π (n m k : ℕ), n + (m + k) = m + (n + k) :=
left_comm nat.add_comm nat.add_assoc

protected theorem add.right_comm : Π (n m k : ℕ), n + m + k = n + k + m :=
right_comm nat.add_comm nat.add_assoc

theorem add.cancel_left {n m k : ℕ} : n + m = n + k → m = k :=
nat.induction_on n
  (take H : 0 + m = 0 + k,
    !nat.zero_add⁻¹ ⬝ H ⬝ !nat.zero_add)
  (take (n : ℕ) (IH : n + m = n + k → m = k) (H : succ n + m = succ n + k),
    have succ (n + m) = succ (n + k),
    from calc
      succ (n + m) = succ n + m   : succ_add
               ... = succ n + k   : H
               ... = succ (n + k) : succ_add,
    have n + m = n + k, from succ.inj this,
    IH this)

theorem add.cancel_right {n m k : ℕ} (H : n + m = k + m) : n = k :=
have H2 : m + n = m + k, from !nat.add_comm ⬝ H ⬝ !nat.add_comm,
  add.cancel_left H2

theorem eq_zero_of_add_eq_zero_right {n m : ℕ} : n + m = 0 → n = 0 :=
nat.induction_on n
  (take (H : 0 + m = 0), rfl)
  (take k IH,
    assume H : succ k + m = 0,
    absurd
      (show succ (k + m) = 0, from calc
         succ (k + m) = succ k + m : succ_add
                  ... = 0          : H)
      !succ_ne_zero)

theorem eq_zero_of_add_eq_zero_left {n m : ℕ} (H : n + m = 0) : m = 0 :=
eq_zero_of_add_eq_zero_right (!nat.add_comm ⬝ H)

theorem eq_zero_and_eq_zero_of_add_eq_zero {n m : ℕ} (H : n + m = 0) : n = 0 ∧ m = 0 :=
and.intro (eq_zero_of_add_eq_zero_right H) (eq_zero_of_add_eq_zero_left H)

theorem add_one [simp] (n : ℕ) : n + 1 = succ n := rfl

theorem one_add (n : ℕ) : 1 + n = succ n :=
!nat.zero_add ▸ !succ_add

/- multiplication -/

protected theorem mul_zero [simp] (n : ℕ) : n * 0 = 0 :=
rfl

theorem mul_succ [simp] (n m : ℕ) : n * succ m = n * m + n :=
rfl

-- commutativity, distributivity, associativity, identity

protected theorem zero_mul [simp] (n : ℕ) : 0 * n = 0 :=
nat.induction_on n
  !nat.mul_zero
  (take m IH, !mul_succ ⬝ !nat.add_zero ⬝ IH)

theorem succ_mul [simp] (n m : ℕ) : (succ n) * m = (n * m) + m :=
nat.induction_on m
  (by rewrite nat.mul_zero)
  (take k IH, calc
    succ n * succ k = succ n * k + succ n   : mul_succ
                ... = n * k + k + succ n    : IH
                ... = n * k + (k + succ n)  : nat.add_assoc
                ... = n * k + (succ n + k)  : nat.add_comm
                ... = n * k + (n + succ k)  : succ_add_eq_succ_add
                ... = n * k + n + succ k    : nat.add_assoc
                ... = n * succ k + succ k   : mul_succ)

protected theorem mul_comm [simp] (n m : ℕ) : n * m = m * n :=
nat.induction_on m
  (!nat.mul_zero ⬝ !nat.zero_mul⁻¹)
  (take k IH, calc
    n * succ k = n * k + n    : mul_succ
           ... = k * n + n    : IH
           ... = (succ k) * n : succ_mul)

protected theorem right_distrib (n m k : ℕ) : (n + m) * k = n * k + m * k :=
nat.induction_on k
  (calc
    (n + m) * 0 = 0             : nat.mul_zero
            ... = 0 + 0         : nat.add_zero
            ... = n * 0 + 0     : nat.mul_zero
            ... = n * 0 + m * 0 : nat.mul_zero)
  (take l IH, calc
    (n + m) * succ l = (n + m) * l + (n + m)    : mul_succ
                 ... = n * l + m * l + (n + m)  : IH
                 ... = n * l + m * l + n + m    : nat.add_assoc
                 ... = n * l + n + m * l + m    : nat.add.right_comm
                 ... = n * l + n + (m * l + m)  : nat.add_assoc
                 ... = n * succ l + (m * l + m) : mul_succ
                 ... = n * succ l + m * succ l  : mul_succ)

protected theorem left_distrib (n m k : ℕ) : n * (m + k) = n * m + n * k :=
calc
  n * (m + k) = (m + k) * n    : nat.mul_comm
          ... = m * n + k * n  : nat.right_distrib
          ... = n * m + k * n  : nat.mul_comm
          ... = n * m + n * k  : nat.mul_comm

protected theorem mul_assoc [simp] (n m k : ℕ) : (n * m) * k = n * (m * k) :=
nat.induction_on k
  (calc
    (n * m) * 0 = n * (m * 0) : nat.mul_zero)
  (take l IH,
    calc
      (n * m) * succ l = (n * m) * l + n * m : mul_succ
                   ... = n * (m * l) + n * m : IH
                   ... = n * (m * l + m)     : nat.left_distrib
                   ... = n * (m * succ l)    : mul_succ)

protected theorem mul_one [simp] (n : ℕ) : n * 1 = n :=
calc
  n * 1 = n * 0 + n : mul_succ
    ... = 0 + n     : nat.mul_zero
    ... = n         : nat.zero_add

protected theorem one_mul [simp] (n : ℕ) : 1 * n = n :=
calc
  1 * n = n * 1 : nat.mul_comm
    ... = n     : nat.mul_one

theorem eq_zero_or_eq_zero_of_mul_eq_zero {n m : ℕ} : n * m = 0 → n = 0 ∨ m = 0 :=
nat.cases_on n
  (assume H, or.inl rfl)
  (take n',
    nat.cases_on m
      (assume H, or.inr rfl)
      (take m',
        assume H : succ n' * succ m' = 0,
        absurd
          (calc
            0 = succ n' * succ m' : H
             ... = succ n' * m' + succ n' : mul_succ
             ... = succ (succ n' * m' + n') : add_succ)⁻¹
          !succ_ne_zero))

open algebra
protected definition comm_semiring [reducible] [trans_instance] : algebra.comm_semiring nat :=
⦃algebra.comm_semiring,
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
