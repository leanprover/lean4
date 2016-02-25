/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Min and max over finite sets.

To support constructive theories, we start with the class
decidable_linear_ordered_cancel_comm_monoid, because:
(1) We need a decidable linear order to have min and max
(2) We need a default element for min and max over the empty set, and max empty = 0 is the
    right choice for nat.
(3) All our number classes are instances.
We can define variants of Min and Max if needed.
-/
import .group_bigops .ordered_ring

variables {A B : Type}

section
  variable [decidable_linear_order A]

  definition max_comm_semigroup : comm_semigroup A :=
  ⦃ comm_semigroup,
    mul       := max,
    mul_assoc := max.assoc,
    mul_comm  := max.comm
  ⦄

  definition min_comm_semigroup : comm_semigroup A :=
  ⦃ comm_semigroup,
    mul       := min,
    mul_assoc := min.assoc,
    mul_comm  := min.comm
  ⦄
end

/- finset versions -/

namespace finset

section deceq_A
variable [decidable_eq A]

section decidable_linear_ordered_cancel_comm_monoid_B
  variable [decidable_linear_ordered_cancel_comm_monoid B]

  section max_comm_semigroup
    local attribute max_comm_semigroup [instance]
    open Prod_semigroup

    definition Max (s : finset A) (f : A → B) : B := Prod_semigroup 0 s f
    notation `Max` binders `∈` s `, ` r:(scoped f, Max s f) := r

    proposition Max_empty (f : A → B) : (Max x ∈ ∅, f x) = 0 := !Prod_semigroup_empty

    proposition Max_singleton (f : A → B) (a : A) : (Max x ∈ '{a}, f x) = f a :=
    !Prod_semigroup_singleton

    proposition Max_insert_insert (f : A → B) {a₁ a₂ : A} {s : finset A} :
        a₂ ∉ s → a₁ ∉ insert a₂ s →
      (Max x ∈ insert a₁ (insert a₂ s), f x) = max (f a₁) (Max x ∈ insert a₂ s, f x) :=
    !Prod_semigroup_insert_insert

    proposition Max_insert (f : A → B) {a : A} {s : finset A} (anins : a ∉ s) (sne : s ≠ ∅) :
      (Max x ∈ insert a s, f x) = max (f a) (Max x ∈ s, f x) :=
    !Prod_semigroup_insert anins sne
  end max_comm_semigroup

  proposition Max_pair (f : A → B) (a₁ a₂ : A) : (Max x ∈ '{a₁, a₂}, f x) = max (f a₁) (f a₂) :=
  decidable.by_cases
    (suppose a₁ = a₂, by rewrite [this, pair_eq_singleton, max_self] )
    (suppose a₁ ≠ a₂,
      have a₁ ∉ '{a₂}, by rewrite [mem_singleton_iff]; apply this,
      using this, by rewrite [Max_insert f this !singleton_ne_empty])

  proposition le_Max (f : A → B) {a : A} {s : finset A} (H : a ∈ s) : f a ≤ Max x ∈ s, f x :=
  begin
    induction s with a' s' a'nins' ih,
      {exact false.elim (not_mem_empty a H)},
    cases (decidable.em (s' = ∅)) with s'empty s'nempty,
      {rewrite [s'empty at *, Max_singleton, eq_of_mem_singleton H]},
    rewrite [Max_insert f a'nins' s'nempty],
    cases (eq_or_mem_of_mem_insert H) with aeqa' ains',
      {rewrite aeqa', apply le_max_left},
    apply le.trans (ih ains') !le_max_right
  end

  proposition Max_le (f : A → B) {s : finset A} {b : B} (sne : s ≠ ∅) (H : ∀ a, a ∈ s → f a ≤ b) :
    (Max x ∈ s, f x) ≤ b :=
  begin
    induction s with a' s' a'nins' ih,
      {exact absurd rfl sne},
    cases (decidable.em (s' = ∅)) with s'empty s'nempty,
      {rewrite [s'empty, Max_singleton], exact H a' !mem_insert},
    rewrite [Max_insert f a'nins' s'nempty],
    apply max_le (H a' !mem_insert),
    apply ih s'nempty,
    intro a H',
    exact H a (mem_insert_of_mem a' H')
  end

  proposition Max_add_right (f : A → B) {s : finset A} (b : B) (sne : s ≠ ∅) :
    (Max x ∈ s, f x + b) = (Max x ∈ s, f x) + b :=
  begin
    induction s with a' s' a'nins' ih,
      {exact absurd rfl sne},
    cases (decidable.em (s' = ∅)) with s'empty s'ne,
      {rewrite [s'empty, Max_singleton]},
    rewrite [*Max_insert _ a'nins' s'ne, ih s'ne, max_add_add_right]
  end

  proposition Max_add_left (f : A → B) {s : finset A} (b : B) (sne : s ≠ ∅) :
    (Max x ∈ s, b + f x) = b + (Max x ∈ s, f x) :=
  begin
    induction s with a' s' a'nins' ih,
      {exact absurd rfl sne},
    cases (decidable.em (s' = ∅)) with s'empty s'ne,
      {rewrite [s'empty, Max_singleton]},
    rewrite [*Max_insert _ a'nins' s'ne, ih s'ne, max_add_add_left]
  end

  section min_comm_semigroup
    local attribute min_comm_semigroup [instance]
    open Prod_semigroup

    definition Min (s : finset A) (f : A → B) : B := Prod_semigroup 0 s f
    notation `Min` binders `∈` s `, ` r:(scoped f, Min s f) := r

    proposition Min_empty (f : A → B) : (Min x ∈ ∅, f x) = 0 := !Prod_semigroup_empty

    proposition Min_singleton (f : A → B) (a : A) : (Min x ∈ '{a}, f x) = f a :=
    !Prod_semigroup_singleton

    proposition Min_insert_insert (f : A → B) {a₁ a₂ : A} {s : finset A} :
        a₂ ∉ s → a₁ ∉ insert a₂ s →
      (Min x ∈ insert a₁ (insert a₂ s), f x) = min (f a₁) (Min x ∈ insert a₂ s, f x) :=
    !Prod_semigroup_insert_insert

    proposition Min_insert (f : A → B) {a : A} {s : finset A} (anins : a ∉ s) (sne : s ≠ ∅) :
      (Min x ∈ insert a s, f x) = min (f a) (Min x ∈ s, f x) :=
    !Prod_semigroup_insert anins sne
  end min_comm_semigroup

  proposition Min_pair (f : A → B) (a₁ a₂ : A) : (Min x ∈ '{a₁, a₂}, f x) = min (f a₁) (f a₂) :=
  decidable.by_cases
    (suppose a₁ = a₂, by rewrite [this, pair_eq_singleton, min_self] )
    (suppose a₁ ≠ a₂,
      have a₁ ∉ '{a₂}, by rewrite [mem_singleton_iff]; apply this,
      using this, by rewrite [Min_insert f this !singleton_ne_empty])

  proposition Min_le (f : A → B) {a : A} {s : finset A} (H : a ∈ s) : (Min x ∈ s, f x) ≤ f a :=
  begin
    induction s with a' s' a'nins' ih,
      {exact false.elim (not_mem_empty a H)},
    cases (decidable.em (s' = ∅)) with s'empty s'nempty,
      {rewrite [s'empty at *, Min_singleton, eq_of_mem_singleton H]},
    rewrite [Min_insert f a'nins' s'nempty],
    cases (eq_or_mem_of_mem_insert H) with aeqa' ains',
      {rewrite aeqa', apply min_le_left},
    apply le.trans !min_le_right (ih ains')
  end

  proposition le_Min (f : A → B) {s : finset A} {b : B} (sne : s ≠ ∅) (H : ∀ a, a ∈ s → b ≤ f a) :
    b ≤ Min x ∈ s, f x :=
  begin
    induction s with a' s' a'nins' ih,
      {exact absurd rfl sne},
    cases (decidable.em (s' = ∅)) with s'empty s'nempty,
      {rewrite [s'empty, Min_singleton], exact H a' !mem_insert},
    rewrite [Min_insert f a'nins' s'nempty],
    apply le_min (H a' !mem_insert),
    apply ih s'nempty,
    intro a H',
    exact H a (mem_insert_of_mem a' H')
  end

  proposition Min_add_right (f : A → B) {s : finset A} (b : B) (sne : s ≠ ∅) :
    (Min x ∈ s, f x + b) = (Min x ∈ s, f x) + b :=
  begin
    induction s with a' s' a'nins' ih,
      {exact absurd rfl sne},
    cases (decidable.em (s' = ∅)) with s'empty s'ne,
      {rewrite [s'empty, Min_singleton]},
    rewrite [*Min_insert _ a'nins' s'ne, ih s'ne, min_add_add_right]
  end

  proposition Min_add_left (f : A → B) {s : finset A} (b : B) (sne : s ≠ ∅) :
    (Min x ∈ s, b + f x) = b + (Min x ∈ s, f x) :=
  begin
    induction s with a' s' a'nins' ih,
      {exact absurd rfl sne},
    cases (decidable.em (s' = ∅)) with s'empty s'ne,
      {rewrite [s'empty, Min_singleton]},
    rewrite [*Min_insert _ a'nins' s'ne, ih s'ne, min_add_add_left]
  end
end decidable_linear_ordered_cancel_comm_monoid_B

section decidable_linear_ordered_comm_group_B
  variable [decidable_linear_ordered_comm_group B]

  proposition Max_neg (f : A → B) (s : finset A) : (Max x ∈ s, - f x) = - Min x ∈ s, f x :=
  begin
    cases (decidable.em (s = ∅)) with se sne,
      {rewrite [se, Max_empty, Min_empty, neg_zero]},
    apply eq_of_le_of_ge,
      {apply !Max_le sne,
         intro a ains,
         apply neg_le_neg,
         apply !Min_le ains},
    apply neg_le_of_neg_le,
    apply !le_Min sne,
    intro a ains,
    apply neg_le_of_neg_le,
    apply !le_Max ains
  end

  proposition Min_neg (f : A → B) (s : finset A) : (Min x ∈ s, - f x) = - Max x ∈ s, f x :=
  begin
    cases (decidable.em (s = ∅)) with se sne,
      {rewrite [se, Max_empty, Min_empty, neg_zero]},
    apply eq_of_le_of_ge,
      {apply le_neg_of_le_neg,
        apply !Max_le sne,
        intro a ains,
        apply le_neg_of_le_neg,
        apply !Min_le ains},
    apply !le_Min sne,
    intro a ains,
    apply neg_le_neg,
    apply !le_Max ains
  end

  proposition Max_eq_neg_Min_neg (f : A → B) (s : finset A) :
    (Max x ∈ s, f x) = - Min x ∈ s, - f x :=
  by rewrite [Min_neg, neg_neg]

  proposition Min_eq_neg_Max_neg (f : A → B) (s : finset A) :
    (Min x ∈ s, f x) = - Max x ∈ s, - f x :=
  by rewrite [Max_neg, neg_neg]

end decidable_linear_ordered_comm_group_B

end deceq_A

/- Min and Max *of* a finset -/

section decidable_linear_ordered_semiring_A
  variable [decidable_linear_ordered_semiring A]

  definition Max₀ (s : finset A) : A := Max x ∈ s, x
  definition Min₀ (s : finset A) : A := Min x ∈ s, x

  proposition Max₀_empty : Max₀ ∅ = (0 : A) := !Max_empty

  proposition Max₀_singleton (a : A) : Max₀ '{a} = a := !Max_singleton

  proposition Max₀_insert_insert {a₁ a₂ : A} {s : finset A} (H₁ : a₂ ∉ s) (H₂ : a₁ ∉ insert a₂ s) :
    Max₀ (insert a₁ (insert a₂ s)) = max a₁ (Max₀ (insert a₂ s)) :=
  !Max_insert_insert H₁ H₂

  proposition Max₀_insert {s : finset A} {a : A} (anins : a ∉ s) (sne : s ≠ ∅) :
    Max₀ (insert a s) = max a (Max₀ s) := !Max_insert anins sne

  proposition Max₀_pair (a₁ a₂ : A) : Max₀ '{a₁, a₂} = max a₁ a₂ := !Max_pair

  proposition le_Max₀ {a : A} {s : finset A} (H : a ∈ s) : a ≤ Max₀ s := !le_Max H

  proposition Max₀_le {s : finset A} {a : A} (sne : s ≠ ∅) (H : ∀ x, x ∈ s → x ≤ a) :
    Max₀ s ≤ a := !Max_le sne H

  proposition Min₀_empty : Min₀ ∅ = (0 : A) := !Min_empty

  proposition Min₀_singleton (a : A) : Min₀ '{a} = a := !Min_singleton

  proposition Min₀_insert_insert {a₁ a₂ : A} {s : finset A} (H₁ : a₂ ∉ s) (H₂ : a₁ ∉ insert a₂ s) :
    Min₀ (insert a₁ (insert a₂ s)) = min a₁ (Min₀ (insert a₂ s)) :=
  !Min_insert_insert H₁ H₂

  proposition Min₀_insert {s : finset A} {a : A} (anins : a ∉ s) (sne : s ≠ ∅) :
    Min₀ (insert a s) = min a (Min₀ s) := !Min_insert anins sne

  proposition Min₀_pair (a₁ a₂ : A) : Min₀ '{a₁, a₂} = min a₁ a₂ := !Min_pair

  proposition Min₀_le {a : A} {s : finset A} (H : a ∈ s) : Min₀ s ≤ a := !Min_le H

  proposition le_Min₀ {s : finset A} {a : A} (sne : s ≠ ∅) (H : ∀ x, x ∈ s → a ≤ x) :
    a ≤ Min₀ s := !le_Min sne H
end decidable_linear_ordered_semiring_A

end finset

/- finite set versions -/

namespace set
open classical

section decidable_linear_ordered_cancel_comm_monoid_B
  variable [decidable_linear_ordered_cancel_comm_monoid B]

  noncomputable definition Max (s : set A) (f : A → B) : B := finset.Max (to_finset s) f
  notation `Max` binders `∈` s `, ` r:(scoped f, Max s f) := r

  noncomputable definition Min (s : set A) (f : A → B) : B := finset.Min (to_finset s) f
  notation `Min` binders `∈` s `, ` r:(scoped f, Min s f) := r

  proposition Max_empty (f : A → B) : (Max x ∈ ∅, f x) = 0 :=
  by rewrite [↑set.Max, to_finset_empty, finset.Max_empty]

  proposition Max_singleton (f : A → B) (a : A) : (Max x ∈ '{a}, f x) = f a :=
  by rewrite [↑set.Max, to_finset_insert, to_finset_empty, finset.Max_singleton]

  proposition Max_insert_insert (f : A → B) {a₁ a₂ : A} {s : set A} [h : finite s] :
      a₂ ∉ s → a₁ ∉ insert a₂ s →
    (Max x ∈ insert a₁ (insert a₂ s), f x) = max (f a₁) (Max x ∈ insert a₂ s, f x) :=
  begin
    rewrite [↑set.Max, -+mem_to_finset_eq, +to_finset_insert],
    apply finset.Max_insert_insert
  end

  proposition Max_insert (f : A → B) {a : A} {s : set A} [h : finite s] (anins : a ∉ s)
      (sne : s ≠ ∅) :
    (Max x ∈ insert a s, f x) = max (f a) (Max x ∈ s, f x) :=
  begin
    revert anins sne,
    rewrite [↑set.Max, -+mem_to_finset_eq, +to_finset_insert],
    intro h1 h2,
    apply finset.Max_insert f h1 (λ h', h2 (eq_empty_of_to_finset_eq_empty h')),
  end

  proposition Max_pair (f : A → B) (a₁ a₂ : A) : (Max x ∈ '{a₁, a₂}, f x) = max (f a₁) (f a₂) :=
  by rewrite [↑set.Max, +to_finset_insert, +to_finset_empty, finset.Max_pair]

  proposition le_Max (f : A → B) {a : A} {s : set A} [fins : finite s] (H : a ∈ s) :
    f a ≤ Max x ∈ s, f x :=
  by rewrite [-+mem_to_finset_eq at H, ↑set.Max]; exact finset.le_Max f H

  proposition Max_le (f : A → B) {s : set A} [fins : finite s] {b : B} (sne : s ≠ ∅)
      (H : ∀ a, a ∈ s → f a ≤ b) :
    (Max x ∈ s, f x) ≤ b :=
  begin
    rewrite [↑set.Max],
    apply finset.Max_le f (λ H', sne (eq_empty_of_to_finset_eq_empty H')),
    intro a H', apply H a, rewrite mem_to_finset_eq at H', exact H'
  end

  proposition Max_add_right (f : A → B) {s : set A} [fins : finite s] (b : B) (sne : s ≠ ∅) :
    (Max x ∈ s, f x + b) = (Max x ∈ s, f x) + b :=
  begin
    rewrite [↑set.Max],
    apply finset.Max_add_right f b (λ h, sne (eq_empty_of_to_finset_eq_empty h))
  end

  proposition Max_add_left (f : A → B) {s : set A} [fins : finite s] (b : B) (sne : s ≠ ∅) :
    (Max x ∈ s, b + f x) = b + (Max x ∈ s, f x) :=
  begin
    rewrite [↑set.Max],
    apply finset.Max_add_left f b (λ h, sne (eq_empty_of_to_finset_eq_empty h))
  end

  proposition Min_empty (f : A → B) : (Min x ∈ ∅, f x) = 0 :=
  by rewrite [↑set.Min, to_finset_empty, finset.Min_empty]

  proposition Min_singleton (f : A → B) (a : A) : (Min x ∈ '{a}, f x) = f a :=
  by rewrite [↑set.Min, to_finset_insert, to_finset_empty, finset.Min_singleton]

  proposition Min_insert_insert (f : A → B) {a₁ a₂ : A} {s : set A} [h : finite s] :
      a₂ ∉ s → a₁ ∉ insert a₂ s →
    (Min x ∈ insert a₁ (insert a₂ s), f x) = min (f a₁) (Min x ∈ insert a₂ s, f x) :=
  begin
    rewrite [↑set.Min, -+mem_to_finset_eq, +to_finset_insert],
    apply finset.Min_insert_insert
  end

  proposition Min_insert (f : A → B) {a : A} {s : set A} [h : finite s] (anins : a ∉ s)
      (sne : s ≠ ∅) :
    (Min x ∈ insert a s, f x) = min (f a) (Min x ∈ s, f x) :=
  begin
    revert anins sne,
    rewrite [↑set.Min, -+mem_to_finset_eq, +to_finset_insert],
    intro h1 h2,
    apply finset.Min_insert f h1 (λ h', h2 (eq_empty_of_to_finset_eq_empty h')),
  end

  proposition Min_pair (f : A → B) (a₁ a₂ : A) : (Min x ∈ '{a₁, a₂}, f x) = min (f a₁) (f a₂) :=
  by rewrite [↑set.Min, +to_finset_insert, +to_finset_empty, finset.Min_pair]

  proposition Min_le (f : A → B) {a : A} {s : set A} [fins : finite s] (H : a ∈ s) :
    (Min x ∈ s, f x) ≤ f a :=
  by rewrite [-+mem_to_finset_eq at H, ↑set.Min]; exact finset.Min_le f H

  proposition le_Min (f : A → B) {s : set A} [fins : finite s] {b : B} (sne : s ≠ ∅)
      (H : ∀ a, a ∈ s → b ≤ f a) :
    b ≤ Min x ∈ s, f x :=
  begin
    rewrite [↑set.Min],
    apply finset.le_Min f (λ H', sne (eq_empty_of_to_finset_eq_empty H')),
    intro a H', apply H a, rewrite mem_to_finset_eq at H', exact H'
  end

  proposition Min_add_right (f : A → B) {s : set A} [fins : finite s] (b : B) (sne : s ≠ ∅) :
    (Min x ∈ s, f x + b) = (Min x ∈ s, f x) + b :=
  begin
    rewrite [↑set.Min],
    apply finset.Min_add_right f b (λ h, sne (eq_empty_of_to_finset_eq_empty h))
  end

  proposition Min_add_left (f : A → B) {s : set A} [fins : finite s] (b : B) (sne : s ≠ ∅) :
    (Min x ∈ s, b + f x) = b + (Min x ∈ s, f x) :=
  begin
    rewrite [↑set.Min],
    apply finset.Min_add_left f b (λ h, sne (eq_empty_of_to_finset_eq_empty h))
  end
end decidable_linear_ordered_cancel_comm_monoid_B

section decidable_linear_ordered_comm_group_B
  variable [decidable_linear_ordered_comm_group B]

  proposition Max_neg (f : A → B) (s : set A) : (Max x ∈ s, - f x) = - Min x ∈ s, f x :=
  by rewrite [↑set.Max, finset.Max_neg]

  proposition Min_neg (f : A → B) (s : set A) : (Min x ∈ s, - f x) = - Max x ∈ s, f x :=
  by rewrite [↑set.Min, finset.Min_neg]

  proposition Max_eq_neg_Min_neg (f : A → B) (s : set A) : (Max x ∈ s, f x) = - Min x ∈ s, - f x :=
  by rewrite [↑set.Max, ↑set.Min, finset.Max_eq_neg_Min_neg]

  proposition Min_eq_neg_Max_neg (f : A → B) (s : set A) : (Min x ∈ s, f x) = - Max x ∈ s, - f x :=
  by rewrite [↑set.Max, ↑set.Min, finset.Min_eq_neg_Max_neg]
end decidable_linear_ordered_comm_group_B

section decidable_linear_ordered_semiring_A
  variable [decidable_linear_ordered_semiring A]

  noncomputable definition Max₀ (s : set A) : A := Max x ∈ s, x
  noncomputable definition Min₀ (s : set A) : A := Min x ∈ s, x

  proposition Max₀_empty : Max₀ ∅ = (0 : A) := !Max_empty

  proposition Max₀_singleton (a : A) : Max₀ '{a} = a := !Max_singleton

  proposition Max₀_insert_insert {a₁ a₂ : A} {s : set A} [fins : finite s] (H₁ : a₂ ∉ s)
      (H₂ : a₁ ∉ insert a₂ s) :
    Max₀ (insert a₁ (insert a₂ s)) = max a₁ (Max₀ (insert a₂ s)) :=
  !Max_insert_insert H₁ H₂

  proposition Max₀_insert {s : set A} [fins : finite s] {a : A} (anins : a ∉ s) (sne : s ≠ ∅) :
    Max₀ (insert a s) = max a (Max₀ s) := !Max_insert anins sne

  proposition Max₀_pair (a₁ a₂ : A) : Max₀ '{a₁, a₂} = max a₁ a₂ := !Max_pair

  proposition le_Max₀ {a : A} {s : set A} [fins : finite s] (H : a ∈ s) : a ≤ Max₀ s := !le_Max H

  proposition Max₀_le {s : set A} [fins : finite s] {a : A} (sne : s ≠ ∅) (H : ∀ x, x ∈ s → x ≤ a) :
    Max₀ s ≤ a := !Max_le sne H

  proposition Min₀_empty : Min₀ ∅ = (0 : A) := !Min_empty

  proposition Min₀_singleton (a : A) : Min₀ '{a} = a := !Min_singleton

  proposition Min₀_insert_insert {a₁ a₂ : A} {s : set A} [fins : finite s] (H₁ : a₂ ∉ s)
      (H₂ : a₁ ∉ insert a₂ s) :
    Min₀ (insert a₁ (insert a₂ s)) = min a₁ (Min₀ (insert a₂ s)) :=
  !Min_insert_insert H₁ H₂

  proposition Min₀_insert {s : set A} [fins : finite s] {a : A} (anins : a ∉ s) (sne : s ≠ ∅) :
    Min₀ (insert a s) = min a (Min₀ s) := !Min_insert anins sne

  proposition Min₀_pair (a₁ a₂ : A) : Min₀ '{a₁, a₂} = min a₁ a₂ := !Min_pair

  proposition Min₀_le {a : A} {s : set A} [fins : finite s] (H : a ∈ s) : Min₀ s ≤ a := !Min_le H

  proposition le_Min₀ {s : set A} [fins : finite s] {a : A} (sne : s ≠ ∅) (H : ∀ x, x ∈ s → a ≤ x) :
    a ≤ Min₀ s := !le_Min sne H
end decidable_linear_ordered_semiring_A

end set
