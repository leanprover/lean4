/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Finite sums and products over intervals of natural numbers.
-/
import data.nat.order algebra.group_bigops algebra.interval

namespace nat

/- sums -/

section add_monoid

variables {A : Type} [add_monoid A]

definition sum_up_to (n : ℕ) (f : ℕ → A) : A :=
  nat.rec_on n 0 (λ n a, a + f n)

notation `∑` binders ` < ` n `, ` r:(scoped f, sum_up_to n f) := r

proposition sum_up_to_zero (f : ℕ → A) : (∑ i < 0, f i) = 0 := rfl

proposition sum_up_to_succ (n : ℕ) (f : ℕ → A) : (∑ i < succ n, f i) = (∑ i < n, f i) + f n := rfl

proposition sum_up_to_one (f : ℕ → A) : (∑ i < 1, f i) = f 0 := zero_add (f 0)

definition sum_range (m n : ℕ) (f : ℕ → A) : A := sum_up_to (succ n - m) (λ i, f (i + m))

notation `∑` binders `=` m `...` n `, ` r:(scoped f, sum_range m n f) := r

proposition sum_range_def (m n : ℕ) (f : ℕ → A) :
            (∑ i = m...n, f i) = (∑ i < (succ n - m), f (i + m)) := rfl

proposition sum_range_self (m : ℕ) (f : ℕ → A) :
            (∑ i = m...m, f i) = f m :=
  by rewrite [↑sum_range, succ_sub !le.refl, nat.sub_self, sum_up_to_one, zero_add]

proposition sum_range_succ {m n : ℕ} (f : ℕ → A) (H : m ≤ succ n) :
            (∑ i = m...succ n, f i) = (∑ i = m...n, f i) + f (succ n) :=
  by rewrite [↑sum_range, succ_sub H, sum_up_to_succ, nat.sub_add_cancel H]

proposition sum_up_to_succ_eq_sum_range_zero (n : ℕ) (f : ℕ → A) :
            (∑ i < succ n, f i) = (∑ i = 0...n, f i) := rfl

end add_monoid

section finset
  variables {A : Type} [add_comm_monoid A]
  open finset

proposition sum_up_to_eq_Sum_upto (n : ℕ) (f : ℕ → A) :
            (∑ i < n, f i) = (∑ i ∈ upto n, f i) :=
begin
  induction n with n ih,
    {exact rfl},
  have H : upto n ∩ '{n} = ∅, from
    inter_eq_empty
      (take x,
        suppose x ∈ upto n,
        have x < n, from lt_of_mem_upto this,
        suppose x ∈ '{n},
        have x = n, using this, by rewrite -mem_singleton_iff; apply this,
        have n < n, from eq.subst this `x < n`,
        show false, from !lt.irrefl this),
  rewrite [sum_up_to_succ, ih, upto_succ, Sum_union _ H, Sum_singleton]
end

end finset

section set
  variables {A : Type} [add_comm_monoid A]
  open set interval

proposition sum_range_eq_sum_interval_aux (m n : ℕ) (f : ℕ → A) :
            (∑ i = m...m+n, f i) = (∑ i ∈ '[m, m + n], f i) :=
begin
  induction n with n ih,
    {rewrite [nat.add_zero, sum_range_self, Icc_self, Sum_singleton]},
  have H : m ≤ succ (m + n), from le_of_lt (lt_of_le_of_lt !le_add_right !lt_succ_self),
  have H' : '[m, m + n] ∩ '{succ (m + n)} = ∅, from
    eq_empty_of_forall_not_mem (take x, assume H1,
      have x = succ (m + n), from eq_of_mem_singleton (and.right H1),
      have succ (m + n) ≤ m + n, from eq.subst this (and.right (and.left H1)),
      show false, from not_lt_of_ge this !lt_succ_self),
  rewrite [add_succ, sum_range_succ f H, Icc_eq_Icc_union_Ioc !le_add_right !le_succ,
           nat.Ioc_eq_Icc_succ, Icc_self, Sum_union f H', Sum_singleton, ih]
end

proposition sum_range_eq_sum_interval {m n : ℕ} (f : ℕ → A) (H : m ≤ n) :
            (∑ i = m...n, f i) = (∑ i ∈ '[m, n], f i) :=
  have n = m + (n - m), by rewrite [add.comm, nat.sub_add_cancel H],
  using this, by rewrite this; apply sum_range_eq_sum_interval_aux

proposition sum_range_offset (m n : ℕ) (f : ℕ → A) :
            (∑ i = m...m+n, f i) = (∑ i = 0...n, f (m + i)) :=
  have bij_on (add m) ('[0, n]) ('[m, m+n]), from !nat.bij_on_add_Icc_zero,
  by+ rewrite [-zero_add n at {2}, *sum_range_eq_sum_interval_aux, Sum_eq_of_bij_on f this, zero_add]

end set

/- products -/

section monoid

variables {A : Type} [monoid A]

definition prod_up_to (n : ℕ) (f : ℕ → A) : A :=
  nat.rec_on n 1 (λ n a, a * f n)

notation `∏` binders ` < ` n `, ` r:(scoped f, prod_up_to n f) := r

proposition prod_up_to_zero (f : ℕ → A) : (∏ i < 0, f i) = 1 := rfl

proposition prod_up_to_succ (n : ℕ) (f : ℕ → A) : (∏ i < succ n, f i) = (∏ i < n, f i) * f n := rfl

proposition prod_up_to_one (f : ℕ → A) : (∏ i < 1, f i) = f 0 := one_mul (f 0)

definition prod_range (m n : ℕ) (f : ℕ → A) : A := prod_up_to (succ n - m) (λ i, f (i + m))

notation `∏` binders `=` m `...` n `, ` r:(scoped f, prod_range m n f) := r

proposition prod_range_def (m n : ℕ) (f : ℕ → A) :
            (∏ i = m...n, f i) = (∏ i < (succ n - m), f (i + m)) := rfl

proposition prod_range_self (m : ℕ) (f : ℕ → A) :
            (∏ i = m...m, f i) = f m :=
by rewrite [↑prod_range, succ_sub !le.refl, nat.sub_self, prod_up_to_one, zero_add]

proposition prod_range_succ {m n : ℕ} (f : ℕ → A) (H : m ≤ succ n) :
            (∏ i = m...succ n, f i) = (∏ i = m...n, f i) * f (succ n) :=
by rewrite [↑prod_range, succ_sub H, prod_up_to_succ, nat.sub_add_cancel H]

proposition prod_up_to_succ_eq_prod_range_zero (n : ℕ) (f : ℕ → A) :
            (∏ i < succ n, f i) = (∏ i = 0...n, f i) := rfl

end monoid

section finset
  variables {A : Type} [comm_monoid A]
  open finset

proposition prod_up_to_eq_Prod_upto (n : ℕ) (f : ℕ → A) :
            (∏ i < n, f i) = (∏ i ∈ upto n, f i) :=
begin
  induction n with n ih,
    {exact rfl},
  have H : upto n ∩ '{n} = ∅, from
    inter_eq_empty
      (take x,
        suppose x ∈ upto n,
        have x < n, from lt_of_mem_upto this,
        suppose x ∈ '{n},
        have x = n, using this, by rewrite -mem_singleton_iff; apply this,
        have n < n, from eq.subst this `x < n`,
        show false, from !lt.irrefl this),
  rewrite [prod_up_to_succ, ih, upto_succ, Prod_union _ H, Prod_singleton]
end

end finset

section set
  variables {A : Type} [comm_monoid A]
  open set interval

proposition prod_range_eq_prod_interval_aux (m n : ℕ) (f : ℕ → A) :
            (∏ i = m...m+n, f i) = (∏ i ∈ '[m, m + n], f i) :=
begin
  induction n with n ih,
    {rewrite [nat.add_zero, prod_range_self, Icc_self, Prod_singleton]},
  have H : m ≤ succ (m + n), from le_of_lt (lt_of_le_of_lt !le_add_right !lt_succ_self),
  have H' : '[m, m + n] ∩ '{succ (m + n)} = ∅, from
    eq_empty_of_forall_not_mem (take x, assume H1,
      have x = succ (m + n), from eq_of_mem_singleton (and.right H1),
      have succ (m + n) ≤ m + n, from eq.subst this (and.right (and.left H1)),
      show false, from not_lt_of_ge this !lt_succ_self),
  rewrite [add_succ, prod_range_succ f H, Icc_eq_Icc_union_Ioc !le_add_right !le_succ,
           nat.Ioc_eq_Icc_succ, Icc_self, Prod_union f H', Prod_singleton, ih]
end

proposition prod_range_eq_prod_interval {m n : ℕ} (f : ℕ → A) (H : m ≤ n) :
            (∏ i = m...n, f i) = (∏ i ∈ '[m, n], f i) :=
  have n = m + (n - m), by rewrite [add.comm, nat.sub_add_cancel H],
  using this, by rewrite this; apply prod_range_eq_prod_interval_aux

proposition prod_range_offset (m n : ℕ) (f : ℕ → A) :
            (∏ i = m...m+n, f i) = (∏ i = 0...n, f (m + i)) :=
  have bij_on (add m) ('[0, n]) ('[m, m+n]), from !nat.bij_on_add_Icc_zero,
  by+ rewrite [-zero_add n at {2}, *prod_range_eq_prod_interval_aux, Prod_eq_of_bij_on f this,
               zero_add]

end set

end nat
