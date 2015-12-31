/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

Finite products on a monoid, and finite sums on an additive monoid. There are three versions:

  Prodl, Suml : products and sums over lists
  Prod, Sum (in namespace finset) : products and sums over finsets
  Prod, Sum (in namespace set) : products and sums over finite sets

We have to be careful with dependencies. This theory imports files from finset and list, which
import basic files from nat.
-/
import .group .group_power data.list.basic data.list.perm data.finset.basic data.set.finite
open function binary quot subtype list finset

variables {A B : Type}
variable [deceqA : decidable_eq A]

/-
-- list versions.
-/

/- Prodl: product indexed by a list -/

section monoid
  variable [mB : monoid B]
  include mB

  definition mulf (f : A → B) : B → A → B :=
  λ b a, b * f a

  definition Prodl (l : list A) (f : A → B) : B :=
  list.foldl (mulf f) 1 l

  -- ∏ x ← l, f x
  notation `∏` binders `←` l `, ` r:(scoped f, Prodl l f) := r

  private theorem foldl_const (f : A → B) :
    ∀ (l : list A) (b : B), foldl (mulf f) b l = b * foldl (mulf f) 1 l
  | []     b := by rewrite [*foldl_nil, mul_one]
  | (a::l) b := by rewrite [*foldl_cons, foldl_const, {foldl _ (mulf f 1 a) _}foldl_const, ↑mulf,
                             one_mul, mul.assoc]

  theorem Prodl_nil (f : A → B) : Prodl [] f = 1 := rfl

  theorem Prodl_cons (f : A → B) (a : A) (l : list A) : Prodl (a::l) f = f a * Prodl l f :=
  by rewrite [↑Prodl, foldl_cons, foldl_const, ↑mulf, one_mul]

  theorem Prodl_append :
    ∀ (l₁ l₂ : list A) (f : A → B), Prodl (l₁++l₂) f = Prodl l₁ f * Prodl l₂ f
  | []    l₂ f  := by rewrite [append_nil_left, Prodl_nil, one_mul]
  | (a::l) l₂ f := by rewrite [append_cons, *Prodl_cons, Prodl_append, mul.assoc]

  section deceqA
    include deceqA

    theorem Prodl_insert_of_mem (f : A → B) {a : A} {l : list A} : a ∈ l →
      Prodl (insert a l) f = Prodl l f :=
    assume ainl, by rewrite [insert_eq_of_mem ainl]

    theorem Prodl_insert_of_not_mem (f : A → B) {a : A} {l : list A} :
      a ∉ l → Prodl (insert a l) f = f a * Prodl l f :=
    assume nainl, by rewrite [insert_eq_of_not_mem nainl, Prodl_cons]

    theorem Prodl_union {l₁ l₂ : list A} (f : A → B) (d : disjoint l₁ l₂) :
      Prodl (union l₁ l₂) f = Prodl l₁ f * Prodl l₂ f :=
    by rewrite [union_eq_append d, Prodl_append]
  end deceqA

  theorem Prodl_one : ∀(l : list A), Prodl l (λ x, 1) = (1:B)
  | []     := rfl
  | (a::l) := by rewrite [Prodl_cons, Prodl_one, mul_one]

  lemma Prodl_singleton (a : A) (f : A → B) : Prodl [a] f = f a :=
  !one_mul

  lemma Prodl_map {f : A → B} :
    ∀ {l : list A}, Prodl l f = Prodl (map f l) id
  | nil    := by rewrite [map_nil]
  | (a::l) := begin rewrite [map_cons, Prodl_cons f, Prodl_cons id (f a), Prodl_map] end

  open nat
  lemma Prodl_eq_pow_of_const {f : A → B} :
    ∀ {l : list A} b, (∀ a, a ∈ l → f a = b) → Prodl l f = b ^ length l
  | nil    := take b, assume Pconst, by rewrite [length_nil, {b^0}pow_zero]
  | (a::l) := take b, assume Pconst,
    assert Pconstl : ∀ a', a' ∈ l → f a' = b,
      from take a' Pa'in, Pconst a' (mem_cons_of_mem a Pa'in),
    by rewrite [Prodl_cons f, Pconst a !mem_cons, Prodl_eq_pow_of_const b Pconstl, length_cons,
                add_one, pow_succ b]

end monoid

section comm_monoid
  variable [cmB : comm_monoid B]
  include cmB

  theorem Prodl_mul (l : list A) (f g : A → B) : Prodl l (λx, f x * g x) = Prodl l f * Prodl l g :=
  list.induction_on l
     (by rewrite [*Prodl_nil, mul_one])
     (take a l,
       assume IH,
       by rewrite [*Prodl_cons, IH, *mul.assoc, mul.left_comm (Prodl l f)])
end comm_monoid

/- Suml: sum indexed by a list -/

section add_monoid
  variable [amB : add_monoid B]
  include amB
  local attribute add_monoid.to_monoid [trans_instance]

  definition Suml (l : list A) (f : A → B) : B := Prodl l f

  -- ∑ x ← l, f x
  notation `∑` binders `←` l `, ` r:(scoped f, Suml l f) := r

  theorem Suml_nil (f : A → B) : Suml [] f = 0 := Prodl_nil f
  theorem Suml_cons (f : A → B) (a : A) (l : list A) : Suml (a::l) f = f a + Suml l f :=
    Prodl_cons f a l
  theorem Suml_append (l₁ l₂ : list A) (f : A → B) : Suml (l₁++l₂) f = Suml l₁ f + Suml l₂ f :=
    Prodl_append l₁ l₂ f

  section deceqA
    include deceqA
    theorem Suml_insert_of_mem (f : A → B) {a : A} {l : list A} (H : a ∈ l) :
      Suml (insert a l) f = Suml l f := Prodl_insert_of_mem f H
    theorem Suml_insert_of_not_mem (f : A → B) {a : A} {l : list A} (H : a ∉ l) :
      Suml (insert a l) f = f a + Suml l f := Prodl_insert_of_not_mem f H
    theorem Suml_union {l₁ l₂ : list A} (f : A → B) (d : disjoint l₁ l₂) :
      Suml (union l₁ l₂) f = Suml l₁ f + Suml l₂ f := Prodl_union f d
  end deceqA

  theorem Suml_zero (l : list A) : Suml l (λ x, 0) = (0:B) := Prodl_one l
  theorem Suml_singleton (a : A) (f : A → B) : Suml [a] f = f a := Prodl_singleton a f

end add_monoid

section add_comm_monoid
  variable [acmB : add_comm_monoid B]
  include acmB
  local attribute add_comm_monoid.to_comm_monoid [trans_instance]

  theorem Suml_add (l : list A) (f g : A → B) : Suml l (λx, f x + g x) = Suml l f + Suml l g :=
    Prodl_mul l f g
end add_comm_monoid

/-
-- finset versions
-/

/- Prod: product indexed by a finset -/

namespace finset
  variable [cmB : comm_monoid B]
  include cmB

  theorem mulf_rcomm (f : A → B) : right_commutative (mulf f) :=
  right_commutative_compose_right (@has_mul.mul B _) f (@mul.right_comm B _)

  theorem Prodl_eq_Prodl_of_perm (f : A → B) {l₁ l₂ : list A} :
    perm l₁ l₂ → Prodl l₁ f = Prodl l₂ f :=
  λ p, perm.foldl_eq_of_perm (mulf_rcomm f) p 1

  definition Prod (s : finset A) (f : A → B) : B :=
  quot.lift_on s
    (λ l, Prodl (elt_of l) f)
    (λ l₁ l₂ p, Prodl_eq_Prodl_of_perm f p)

  -- ∏ x ∈ s, f x
  notation `∏` binders `∈` s `, ` r:(scoped f, Prod s f) := r

  theorem Prod_empty (f : A → B) : Prod ∅ f = 1 :=
  Prodl_nil f

  theorem Prod_mul (s : finset A) (f g : A → B) : Prod s (λx, f x * g x) = Prod s f * Prod s g :=
  quot.induction_on s (take u, !Prodl_mul)

  theorem Prod_one (s : finset A) : Prod s (λ x, 1) = (1:B) :=
  quot.induction_on s (take u, !Prodl_one)

  section deceqA
    include deceqA

    theorem Prod_insert_of_mem (f : A → B) {a : A} {s : finset A} :
      a ∈ s → Prod (insert a s) f = Prod s f :=
    quot.induction_on s
      (λ l ainl, Prodl_insert_of_mem f ainl)

    theorem Prod_insert_of_not_mem (f : A → B) {a : A} {s : finset A} :
      a ∉ s → Prod (insert a s) f = f a * Prod s f :=
    quot.induction_on s
      (λ l nainl, Prodl_insert_of_not_mem f nainl)

    theorem Prod_union (f : A → B) {s₁ s₂ : finset A} (disj : s₁ ∩ s₂ = ∅) :
      Prod (s₁ ∪ s₂) f = Prod s₁ f * Prod s₂ f :=
    have H1 : disjoint s₁ s₂ → Prod (s₁ ∪ s₂) f = Prod s₁ f * Prod s₂ f, from
      quot.induction_on₂ s₁ s₂
        (λ l₁ l₂ d, Prodl_union f d),
    H1 (disjoint_of_inter_eq_empty disj)

    theorem Prod_ext {s : finset A} {f g : A → B} :
      (∀{x}, x ∈ s → f x = g x) → Prod s f = Prod s g :=
    finset.induction_on s
      (assume H, rfl)
      (take x s', assume H1 : x ∉ s',
        assume IH : (∀ {x : A}, x ∈ s' → f x = g x) → Prod s' f = Prod s' g,
        assume H2 : ∀{y}, y ∈ insert x s' → f y = g y,
        assert H3 : ∀y, y ∈ s' → f y = g y, from
          take y, assume H', H2 (mem_insert_of_mem _ H'),
        assert H4 : f x = g x, from H2 !mem_insert,
        by rewrite [Prod_insert_of_not_mem f H1, Prod_insert_of_not_mem g H1, IH H3, H4])

    theorem Prod_singleton (a : A) (f : A → B) : Prod '{a} f = f a :=
    have a ∉ ∅, from not_mem_empty a,
    by+ rewrite [Prod_insert_of_not_mem f this, Prod_empty, mul_one]

    theorem Prod_image {C : Type} [deceqC : decidable_eq C] {s : finset A} (f : C → B) {g : A → C}
                       (H : set.inj_on g (to_set s)) :
            (∏ j ∈ image g s, f j) = (∏ i ∈ s, f (g i)) :=
    begin
      induction s with a s anins ih,
        {rewrite [*Prod_empty]},
      have injg : set.inj_on g (to_set s),
        from set.inj_on_of_inj_on_of_subset H (λ x, mem_insert_of_mem a),
      have g a ∉ g '[s], from
        suppose g a ∈ g '[s],
        obtain b [(bs : b ∈ s) (gbeq : g b = g a)], from exists_of_mem_image this,
        have aias : set.mem a (to_set (insert a s)),
          by rewrite to_set_insert; apply set.mem_insert a s,
        have bias : set.mem b (to_set (insert a s)),
          by rewrite to_set_insert; apply set.mem_insert_of_mem; exact bs,
        have b = a, from H bias aias gbeq,
        show false, from anins (eq.subst this bs),
      rewrite [image_insert, Prod_insert_of_not_mem _ this, Prod_insert_of_not_mem _ anins, ih injg]
    end

    theorem Prod_eq_of_bij_on {C : Type} [deceqC : decidable_eq C] {s : finset A} {t : finset C}
                              (f : C → B) {g : A → C} (H : set.bij_on g (to_set s) (to_set t)) :
            (∏ j ∈ t, f j) = (∏ i ∈ s, f (g i)) :=
    have g '[s] = t,
      by apply eq_of_to_set_eq_to_set; rewrite to_set_image; exact set.image_eq_of_bij_on H,
    using this, by rewrite [-this, Prod_image f (and.left (and.right H))]
  end deceqA
end finset

/- Sum: sum indexed by a finset -/

namespace finset
  variable [acmB : add_comm_monoid B]
  include acmB
  local attribute add_comm_monoid.to_comm_monoid [trans_instance]

  definition Sum (s : finset A) (f : A → B) : B := Prod s f

  -- ∑ x ∈ s, f x
  notation `∑` binders `∈` s `, ` r:(scoped f, Sum s f) := r

  theorem Sum_empty (f : A → B) : Sum ∅ f = 0 := Prod_empty f
  theorem Sum_add (s : finset A) (f g : A → B) :
    Sum s (λx, f x + g x) = Sum s f + Sum s g := Prod_mul s f g
  theorem Sum_zero (s : finset A) : Sum s (λ x, 0) = (0:B) := Prod_one s

  section deceqA
    include deceqA
    theorem Sum_insert_of_mem (f : A → B) {a : A} {s : finset A} (H : a ∈ s) :
      Sum (insert a s) f = Sum s f := Prod_insert_of_mem f H
    theorem Sum_insert_of_not_mem (f : A → B) {a : A} {s : finset A} (H : a ∉ s) :
      Sum (insert a s) f = f a + Sum s f := Prod_insert_of_not_mem f H
    theorem Sum_union (f : A → B) {s₁ s₂ : finset A} (disj : s₁ ∩ s₂ = ∅) :
      Sum (s₁ ∪ s₂) f = Sum s₁ f + Sum s₂ f := Prod_union f disj
    theorem Sum_ext {s : finset A} {f g : A → B} (H : ∀x, x ∈ s → f x = g x) :
      Sum s f = Sum s g := Prod_ext H
    theorem Sum_singleton (a : A) (f : A → B) : Sum '{a} f = f a := Prod_singleton a f

    theorem Sum_image {C : Type} [deceqC : decidable_eq C] {s : finset A} (f : C → B) {g : A → C}
                      (H : set.inj_on g (to_set s)) :
            (∑ j ∈ image g s, f j) = (∑ i ∈ s, f (g i)) := Prod_image f H
    theorem Sum_eq_of_bij_on {C : Type} [deceqC : decidable_eq C] {s : finset A} {t : finset C}
                             (f : C → B) {g : A → C} (H : set.bij_on g (to_set s) (to_set t)) :
            (∑ j ∈ t, f j) = (∑ i ∈ s, f (g i)) := Prod_eq_of_bij_on f H
  end deceqA
end finset

/-
-- set versions
-/

namespace set
open classical

/- Prod: product indexed by a set -/

section Prod
  variable [cmB : comm_monoid B]
  include cmB

  noncomputable definition Prod (s : set A) (f : A → B) : B := finset.Prod (to_finset s) f

  -- ∏ x ∈ s, f x
  notation `∏` binders `∈` s `, ` r:(scoped f, Prod s f) := r

  theorem Prod_empty (f : A → B) : Prod ∅ f = 1 :=
  by rewrite [↑Prod, to_finset_empty]

  theorem Prod_of_not_finite {s : set A} (nfins : ¬ finite s) (f : A → B) : Prod s f = 1 :=
  by rewrite [↑Prod, to_finset_of_not_finite nfins]

  theorem Prod_mul (s : set A) (f g : A → B) : Prod s (λx, f x * g x) = Prod s f * Prod s g :=
  by rewrite [↑Prod, finset.Prod_mul]

  theorem Prod_one (s : set A) : Prod s (λ x, 1) = (1:B) :=
  by rewrite [↑Prod, finset.Prod_one]

  theorem Prod_insert_of_mem (f : A → B) {a : A} {s : set A} (H : a ∈ s) :
    Prod (insert a s) f = Prod s f :=
  by_cases
    (suppose finite s,
      assert (#finset a ∈ set.to_finset s), by rewrite mem_to_finset_eq; apply H,
      by rewrite [↑Prod, to_finset_insert, finset.Prod_insert_of_mem f this])
    (assume nfs : ¬ finite s,
      assert ¬ finite (insert a s), from assume H, nfs (finite_of_finite_insert H),
      by rewrite [Prod_of_not_finite nfs, Prod_of_not_finite this])

  theorem Prod_insert_of_not_mem (f : A → B) {a : A} {s : set A} [finite s] (H : a ∉ s) :
    Prod (insert a s) f = f a * Prod s f :=
  assert (#finset a ∉ set.to_finset s), by rewrite mem_to_finset_eq; apply H,
  by rewrite [↑Prod, to_finset_insert, finset.Prod_insert_of_not_mem f this]

  theorem Prod_union (f : A → B) {s₁ s₂ : set A} [finite s₁] [finite s₂]
      (disj : s₁ ∩ s₂ = ∅) :
    Prod (s₁ ∪ s₂) f = Prod s₁ f * Prod s₂ f :=
  begin
    rewrite [↑Prod, to_finset_union],
    apply finset.Prod_union,
    apply finset.eq_of_to_set_eq_to_set,
    rewrite [finset.to_set_inter, *to_set_to_finset, finset.to_set_empty, disj]
  end

  theorem Prod_ext {s : set A} {f g : A → B} (H : ∀{x}, x ∈ s → f x = g x) : Prod s f = Prod s g :=
  by_cases
    (suppose finite s,
      by esimp [Prod]; apply finset.Prod_ext; intro x; rewrite [mem_to_finset_eq]; apply H)
    (assume nfs : ¬ finite s,
      by rewrite [*Prod_of_not_finite nfs])

  theorem Prod_singleton (a : A) (f : A → B) : Prod '{a} f = f a :=
  by rewrite [↑Prod, to_finset_insert, to_finset_empty, finset.Prod_singleton]

  theorem Prod_image {C : Type} {s : set A} [fins : finite s] (f : C → B) {g : A → C}
                     (H : inj_on g s) :
          (∏ j ∈ image g s, f j) = (∏ i ∈ s, f (g i)) :=
  begin
    have H' : inj_on g (finset.to_set (set.to_finset s)), by rewrite to_set_to_finset; exact H,
    rewrite [↑Prod, to_finset_image g s, finset.Prod_image f H']
  end

  theorem Prod_eq_of_bij_on {C : Type} {s : set A} {t : set C} (f : C → B)
                            {g : A → C} (H : bij_on g s t) :
          (∏ j ∈ t, f j) = (∏ i ∈ s, f (g i)) :=
  by_cases
    (suppose finite s,
      have g '[s] = t, from image_eq_of_bij_on H,
      using this, by rewrite [-this, Prod_image f (and.left (and.right H))])
    (assume nfins : ¬ finite s,
      have nfint : ¬ finite t, from
        suppose finite t,
        have finite s, from finite_of_bij_on' H,
        show false, from nfins this,
      by+ rewrite [Prod_of_not_finite nfins, Prod_of_not_finite nfint])
end Prod

/- Sum: sum indexed by a set -/

section Sum
  variable [acmB : add_comm_monoid B]
  include acmB
  local attribute add_comm_monoid.to_comm_monoid [trans_instance]

  noncomputable definition Sum (s : set A) (f : A → B) : B := Prod s f

  proposition Sum_def (s : set A) (f : A → B) : Sum s f = finset.Sum (to_finset s) f := rfl

  -- ∑ x ∈ s, f x
  notation `∑` binders `∈` s `, ` r:(scoped f, Sum s f) := r

  theorem Sum_empty (f : A → B) : Sum ∅ f = 0 := Prod_empty f
  theorem Sum_of_not_finite {s : set A} (nfins : ¬ finite s) (f : A → B) : Sum s f = 0 :=
    Prod_of_not_finite nfins f
  theorem Sum_add (s : set A) (f g : A → B) :
    Sum s (λx, f x + g x) = Sum s f + Sum s g := Prod_mul s f g
  theorem Sum_zero (s : set A) : Sum s (λ x, 0) = (0:B) := Prod_one s

  theorem Sum_insert_of_mem (f : A → B) {a : A} {s : set A} (H : a ∈ s) :
    Sum (insert a s) f = Sum s f := Prod_insert_of_mem f H
  theorem Sum_insert_of_not_mem (f : A → B) {a : A} {s : set A} [finite s] (H : a ∉ s) :
    Sum (insert a s) f = f a + Sum s f := Prod_insert_of_not_mem f H
  theorem Sum_union (f : A → B) {s₁ s₂ : set A} [finite s₁] [finite s₂]
      (disj : s₁ ∩ s₂ = ∅) :
    Sum (s₁ ∪ s₂) f = Sum s₁ f + Sum s₂ f := Prod_union f disj
  theorem Sum_ext {s : set A} {f g : A → B} (H : ∀x, x ∈ s → f x = g x) :
    Sum s f = Sum s g := Prod_ext H

  theorem Sum_singleton (a : A) (f : A → B) : Sum '{a} f = f a :=
    Prod_singleton a f

  theorem Sum_image {C : Type} {s : set A} [fins : finite s] (f : C → B) {g : A → C}
                    (H : inj_on g s) :
          (∑ j ∈ image g s, f j) = (∑ i ∈ s, f (g i)) := Prod_image f H
  theorem Sum_eq_of_bij_on {C : Type} {s : set A} {t : set C} (f : C → B) {g : A → C}
                           (H : bij_on g s t) :
          (∑ j ∈ t, f j) = (∑ i ∈ s, f (g i)) := Prod_eq_of_bij_on f H
end Sum

end set
