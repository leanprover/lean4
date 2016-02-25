/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Properties of finite sums and products in various structures, including ordered rings and fields.
There are two versions of every theorem: one for finsets, and one for finite sets.
-/
import .group_bigops .ordered_field

variables {A B : Type}
variable [deceqA : decidable_eq A]

/-
-- finset versions
-/

namespace finset

section comm_semiring
  variable [csB : comm_semiring B]
  include deceqA csB

  proposition mul_Sum (f : A → B) {s : finset A} (b : B) :
    b * (∑ x ∈ s, f x) = ∑ x ∈ s, b * f x :=
  begin
    induction s with a s ans ih,
      {rewrite [+Sum_empty, mul_zero]},
    rewrite [Sum_insert_of_not_mem f ans, Sum_insert_of_not_mem (λ x, b * f x) ans],
    rewrite [-ih, left_distrib]
  end

  proposition Sum_mul (f : A → B) {s : finset A} (b : B) :
    (∑ x ∈ s, f x) * b = ∑ x ∈ s, f x * b :=
  by rewrite [mul.comm _ b, mul_Sum]; apply Sum_ext; intros; apply mul.comm

  proposition Prod_eq_zero (f : A → B) {s : finset A} {a : A} (H : a ∈ s) (fa0 : f a = 0) :
    (∏ x ∈ s, f x) = 0 :=
  begin
    induction s with b s bns ih,
      {exact absurd H !not_mem_empty},
    rewrite [Prod_insert_of_not_mem f bns],
    have a = b ∨ a ∈ s, from eq_or_mem_of_mem_insert H,
    cases this with aeqb ains,
      {rewrite [-aeqb, fa0, zero_mul]},
    rewrite [ih ains, mul_zero]
  end
end comm_semiring

section ordered_comm_group
  variable [ocgB : ordered_comm_group B]
  include deceqA ocgB

  proposition Sum_le_Sum (f g : A → B) {s : finset A} (H: ∀ x, x ∈ s → f x ≤ g x) :
    (∑ x ∈ s, f x) ≤ (∑ x ∈ s, g x) :=
  begin
    induction s with a s ans ih,
      {exact le.refl _},
    have H1 : f a ≤ g a, from H _ !mem_insert,
    have H2 : (∑ x ∈ s, f x) ≤  (∑ x ∈ s, g x), from ih (forall_of_forall_insert H),
    rewrite [Sum_insert_of_not_mem f ans, Sum_insert_of_not_mem g ans],
    apply add_le_add H1 H2
  end

  proposition Sum_nonneg (f : A → B) {s : finset A} (H : ∀x, x ∈ s → f x ≥ 0) :
    (∑ x ∈ s, f x) ≥ 0 :=
  calc
      0 = (∑ x ∈ s, 0)   : Sum_zero
    ... ≤ (∑ x ∈ s, f x) : Sum_le_Sum (λ x, 0) f H

  proposition Sum_nonpos (f : A → B) {s : finset A} (H : ∀x, x ∈ s → f x ≤ 0) :
    (∑ x ∈ s, f x) ≤ 0 :=
  calc
      0 = (∑ x ∈ s, 0)   : Sum_zero
    ... ≥ (∑ x ∈ s, f x) : Sum_le_Sum f (λ x, 0) H
end ordered_comm_group

section decidable_linear_ordered_comm_group
  variable [dloocgB : decidable_linear_ordered_comm_group B]
  include deceqA dloocgB

  proposition abs_Sum_le (f : A → B) (s : finset A) : abs (∑ x ∈ s, f x) ≤ (∑ x ∈ s, abs (f x)) :=
  begin
    induction s with a s ans ih,
      {rewrite [+Sum_empty, abs_zero]},
    rewrite [Sum_insert_of_not_mem f ans, Sum_insert_of_not_mem _ ans],
    apply le.trans,
      apply abs_add_le_abs_add_abs,
    apply add_le_add_left ih
  end
end decidable_linear_ordered_comm_group

end finset

/-
-- set versions
-/

namespace set
open classical

section comm_semiring
  variable [csB : comm_semiring B]
  include csB

  proposition mul_Sum (f : A → B) {s : set A} (b : B) :
    b * (∑ x ∈ s, f x) = ∑ x ∈ s, b * f x :=
  begin
    cases (em (finite s)) with fins nfins,
    rotate 1,
      {rewrite [+Sum_of_not_finite nfins, mul_zero]},
    induction fins with a s fins ans ih,
      {rewrite [+Sum_empty, mul_zero]},
    rewrite [Sum_insert_of_not_mem f ans, Sum_insert_of_not_mem (λ x, b * f x) ans],
    rewrite [-ih, left_distrib]
  end

  proposition Sum_mul (f : A → B) {s : set A} (b : B) :
    (∑ x ∈ s, f x) * b = ∑ x ∈ s, f x * b :=
  by rewrite [mul.comm _ b, mul_Sum]; apply Sum_ext; intros; apply mul.comm

  proposition Prod_eq_zero (f : A → B) {s : set A} [fins : finite s] {a : A} (H : a ∈ s) (fa0 : f a = 0) :
    (∏ x ∈ s, f x) = 0 :=
  begin
    induction fins with b s fins bns ih,
      {exact absurd H !not_mem_empty},
    rewrite [Prod_insert_of_not_mem f bns],
    have a = b ∨ a ∈ s, from eq_or_mem_of_mem_insert H,
    cases this with aeqb ains,
      {rewrite [-aeqb, fa0, zero_mul]},
    rewrite [ih ains, mul_zero]
  end
end comm_semiring

section ordered_comm_group
  variable [ocgB : ordered_comm_group B]
  include ocgB

  proposition Sum_le_Sum (f g : A → B) {s : set A} (H: ∀₀ x ∈ s, f x ≤ g x) :
    (∑ x ∈ s, f x) ≤ (∑ x ∈ s, g x) :=
  begin
    cases (em (finite s)) with fins nfins,
     {induction fins with a s fins ans ih,
       {rewrite +Sum_empty},
       {rewrite [Sum_insert_of_not_mem f ans, Sum_insert_of_not_mem g ans],
         have H1 : f a ≤ g a, from H !mem_insert,
         have H2 : (∑ x ∈ s, f x) ≤ (∑ x ∈ s, g x), from ih (forall_of_forall_insert H),
         apply add_le_add H1 H2}},
    rewrite [+Sum_of_not_finite nfins]
  end

  proposition Sum_nonneg (f : A → B) {s : set A} (H : ∀₀ x ∈ s, f x ≥ 0) :
    (∑ x ∈ s, f x) ≥ 0 :=
  calc
      0 = (∑ x ∈ s, 0)   : Sum_zero
    ... ≤ (∑ x ∈ s, f x) : Sum_le_Sum (λ x, 0) f H

  proposition Sum_nonpos (f : A → B) {s : set A} (H : ∀₀ x ∈ s, f x ≤ 0) :
    (∑ x ∈ s, f x) ≤ 0 :=
  calc
      0 = (∑ x ∈ s, 0)   : Sum_zero
    ... ≥ (∑ x ∈ s, f x) : Sum_le_Sum f (λ x, 0) H
end ordered_comm_group

section decidable_linear_ordered_comm_group
  variable [dloocgB : decidable_linear_ordered_comm_group B]
  include deceqA dloocgB

  proposition abs_Sum_le (f : A → B) (s : set A) : abs (∑ x ∈ s, f x) ≤ (∑ x ∈ s, abs (f x)) :=
  begin
    cases (em (finite s)) with fins nfins,
    rotate 1,
      {rewrite [+Sum_of_not_finite nfins, abs_zero]},
    induction fins with a s fins ans ih,
      {rewrite [+Sum_empty, abs_zero]},
    rewrite [Sum_insert_of_not_mem f ans, Sum_insert_of_not_mem _ ans],
    apply le.trans,
      apply abs_add_le_abs_add_abs,
    apply add_le_add_left ih
  end
end decidable_linear_ordered_comm_group

end set
