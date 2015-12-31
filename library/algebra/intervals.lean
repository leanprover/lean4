/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Notation for intervals and some properties.

The mnemonic: o = open, c = closed, u = unbounded. For example, Iou a b is '(a, ∞).
-/
import .order data.set
open set

-- TODO: move
section
  open set

  theorem mem_singleton_of_eq {A : Type} {x a : A} (H : x = a) : x ∈ '{a} :=
  eq.subst (eq.symm H) (mem_singleton a)
end

namespace intervals

section order_pair
variables {A : Type} [order_pair A]

definition Ioo (a b : A) : set A := {x | a < x ∧ x < b}
definition Ioc (a b : A) : set A := {x | a < x ∧ x ≤ b}
definition Ico (a b : A) : set A := {x | a ≤ x ∧ x < b}
definition Icc (a b : A) : set A := {x | a ≤ x ∧ x ≤ b}
definition Iou (a : A)   : set A := {x | a < x}
definition Icu (a : A)   : set A := {x | a ≤ x}
definition Iuo (b : A)   : set A := {x | x < b}
definition Iuc (b : A)   : set A := {x | x ≤ b}

notation `'` `(` a `, ` b `)`     := Ioo a b
notation `'` `(` a `, ` b `]`     := Ioc a b
notation `'[` a `, ` b `)`        := Ico a b
notation `'[` a `, ` b `]`       := Icc a b
notation `'` `(` a `, ` `∞` `)`   := Iou a
notation `'[` a `, ` `∞` `)`      := Icu a
notation `'` `(` `-∞` `, ` b `)`  := Iuo b
notation `'` `(` `-∞` `, ` b `]`  := Iuc b

variables a b : A

proposition Iou_inter_Iuo : '(a, ∞) ∩ '(-∞, b) = '(a, b) := rfl
proposition Icu_inter_Iuo : '[a, ∞) ∩ '(-∞, b) = '[a, b) := rfl
proposition Iou_inter_Iuc : '(a, ∞) ∩ '(-∞, b] = '(a, b] := rfl
proposition Ioc_inter_Iuc : '[a, ∞) ∩ '(-∞, b] = '[a, b] := rfl

proposition Icc_self : '[a, a] = '{a} :=
set.ext (take x, iff.intro
  (suppose x ∈ '[a, a],
    have x = a, from le.antisymm (and.right this) (and.left this),
    show x ∈ '{a}, from mem_singleton_of_eq this)
  (suppose x ∈ '{a},
    have x = a, from eq_of_mem_singleton this,
    show a ≤ x ∧ x ≤ a, from and.intro (eq.subst this !le.refl) (eq.subst this !le.refl)))

end order_pair

section decidable_linear_order

variables {A : Type} [decidable_linear_order A]

proposition Icc_eq_Icc_union_Ioc {a b c : A} (H1 : a ≤ b) (H2 : b ≤ c) :
  '[a, c] = '[a, b] ∪ '(b, c] :=
set.ext (take x, iff.intro
  (assume H3 :  x ∈ '[a, c],
    decidable.by_cases
      (suppose x ≤ b,
         or.inl (and.intro (and.left H3) this))
      (suppose ¬ x ≤ b,
         or.inr (and.intro (lt_of_not_ge this) (and.right H3))))
  (suppose x ∈ '[a, b] ∪ '(b, c],
    or.elim this
      (suppose x ∈ '[a, b],
         and.intro (and.left this) (le.trans (and.right this) H2))
      (suppose x ∈ '(b, c],
         and.intro (le_of_lt (lt_of_le_of_lt H1 (and.left this))) (and.right this))))

end decidable_linear_order

/- intervals of natural numbers -/

namespace nat
open nat eq.ops
  variables m n : ℕ

  proposition Ioc_eq_Icc_succ : '(m, n] = '[succ m, n] := rfl

  proposition Ioo_eq_Ico_succ : '(m, n) = '[succ m, n) := rfl

  proposition Ico_succ_eq_Icc : '[m, succ n) = '[m, n] :=
  set.ext (take x, iff.intro
    (assume H, and.intro (and.left H) (le_of_lt_succ (and.right H)))
    (assume H, and.intro (and.left H) (lt_succ_of_le (and.right H))))

  proposition Ioo_succ_eq_Ioc : '(m, succ n) = '(m, n] :=
  set.ext (take x, iff.intro
    (assume H, and.intro (and.left H) (le_of_lt_succ (and.right H)))
    (assume H, and.intro (and.left H) (lt_succ_of_le (and.right H))))

  proposition Icu_zero : '[(0 : nat), ∞) = univ :=
  eq_univ_of_forall (take x, zero_le x)

  proposition Icc_zero (n : ℕ) : '[0, n] = '(-∞, n] :=
  have '[0, n] = '[0, ∞) ∩ '(-∞, n], from rfl,
  by+ rewrite [this, Icu_zero, univ_inter]
end nat

section nat -- put the instances in the intervals namespace
open nat eq.ops
  variables m n : ℕ

  proposition nat.Iuc_finite [instance] (n : ℕ) : finite '(-∞, n] :=
  nat.induction_on n
    (have '(-∞, 0] ⊆ '{0}, from λ x H, mem_singleton_of_eq (le.antisymm H !zero_le),
      finite_subset this)
    (take n, assume ih : finite '(-∞, n],
      have '(-∞, succ n] ⊆ '(-∞, n] ∪ '{succ n},
        by intro x H; rewrite [mem_union_iff, mem_singleton_iff]; apply le_or_eq_succ_of_le_succ H,
        finite_subset this)

  proposition nat.Iuo_finite [instance] (n : ℕ) : finite '(-∞, n) :=
  have '(-∞, n) ⊆ '(-∞, n], from λ x, le_of_lt,
  finite_subset this

  proposition nat.Icc_finite [instance] (m n : ℕ) : finite ('[m, n]) :=
  have '[m, n] ⊆ '(-∞, n], from λ x H, and.right H,
  finite_subset this

  proposition nat.Ico_finite [instance] (m n : ℕ) : finite ('[m, n)) :=
  have '[m, n) ⊆ '(-∞, n), from λ x H, and.right H,
  finite_subset this

  proposition nat.Ioc_finite [instance] (m n : ℕ) : finite '(m, n] :=
  have '(m, n] ⊆ '(-∞, n], from λ x H, and.right H,
  finite_subset this
end nat

end intervals
