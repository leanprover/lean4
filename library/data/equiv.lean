/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

In the standard library we cannot assume the univalence axiom.
We say two types are equivalent if they are isomorphic.

Two equivalent types have the same cardinality.
-/
import data.sum data.nat
open function

structure equiv [class] (A B : Type) :=
  (to_fun    : A → B)
  (inv       : B → A)
  (left_inv  : left_inverse inv to_fun)
  (right_inv : right_inverse inv to_fun)

namespace equiv
infix `≃`:50 := equiv

namespace ops
  attribute equiv.to_fun [coercion]
  definition inverse [reducible] {A B : Type} [h : A ≃ B] : B → A :=
  λ b, @equiv.inv A B h b
  postfix `⁻¹` := inverse
end ops

protected theorem refl [refl] (A : Type) : A ≃ A :=
mk (@id A) (@id A) (λ x, rfl) (λ x, rfl)

protected theorem symm [symm] {A B : Type} : A ≃ B → B ≃ A
| (mk f g h₁ h₂) := mk g f h₂ h₁

protected theorem trans [trans] {A B C : Type} : A ≃ B → B ≃ C → A ≃ C
| (mk f₁ g₁ l₁ r₁) (mk f₂ g₂ l₂ r₂) :=
  mk (f₂ ∘ f₁) (g₁ ∘ g₂)
   (show ∀ x, g₁ (g₂ (f₂ (f₁ x))) = x, by intros; rewrite [l₂, l₁])
   (show ∀ x, f₂ (f₁ (g₁ (g₂ x))) = x, by intros; rewrite [r₁, r₂])

lemma false_equiv_empty : empty ≃ false :=
mk (λ e, empty.rec _ e) (λ h, false.rec _ h) (λ e, empty.rec _ e) (λ h, false.rec _ h)

lemma arrow_congr [congr] {A₁ B₁ A₂ B₂ : Type} : A₁ ≃ A₂ → B₁ ≃ B₂ → (A₁ → B₁) ≃ (A₂ → B₂)
| (mk f₁ g₁ l₁ r₁) (mk f₂ g₂ l₂ r₂) :=
  mk
   (λ (h : A₁ → B₁) (a : A₂), f₂ (h (g₁ a)))
   (λ (h : A₂ → B₂) (a : A₁), g₂ (h (f₁ a)))
   (λ h, funext (λ a, by rewrite [l₁, l₂]))
   (λ h, funext (λ a, by rewrite [r₁, r₂]))

section
open unit
lemma arrow_unit_equiv_unit [simp] (A : Type) : (A → unit) ≃ unit :=
mk (λ f, star) (λ u, (λ f, star))
   (λ f, funext (λ x, by cases (f x); reflexivity))
   (λ u, by cases u; reflexivity)

lemma unit_arrow_equiv [simp] (A : Type) : (unit → A) ≃ A :=
mk (λ f, f star) (λ a, (λ u, a))
   (λ f, funext (λ x, by cases x; reflexivity))
   (λ u, rfl)

lemma empty_arrow_equiv_unit [simp] (A : Type) : (empty → A) ≃ unit :=
mk (λ f, star) (λ u, λ e, empty.rec _ e)
   (λ f, funext (λ x, empty.rec _ x))
   (λ u, by cases u; reflexivity)

lemma false_arrow_equiv_unit [simp] (A : Type) : (false → A) ≃ unit :=
calc (false → A) ≃ (empty → A) : arrow_congr false_equiv_empty !equiv.refl
             ... ≃ unit        : empty_arrow_equiv_unit
end

lemma prod_congr [congr] {A₁ B₁ A₂ B₂ : Type} : A₁ ≃ A₂ → B₁ ≃ B₂ → (A₁ × B₁) ≃ (A₂ × B₂)
| (mk f₁ g₁ l₁ r₁) (mk f₂ g₂ l₂ r₂) :=
  mk
    (λ p, match p with (a₁, b₁) := (f₁ a₁, f₂ b₁) end)
    (λ p, match p with (a₂, b₂) := (g₁ a₂, g₂ b₂) end)
    (λ p, begin cases p, esimp, rewrite [l₁, l₂] end)
    (λ p, begin cases p, esimp, rewrite [r₁, r₂] end)

lemma prod_comm [simp] (A B : Type) : (A × B) ≃ (B × A) :=
mk (λ p, match p with (a, b) := (b, a) end)
   (λ p, match p with (b, a) := (a, b) end)
   (λ p, begin cases p, esimp end)
   (λ p, begin cases p, esimp end)

lemma prod_assoc [simp] (A B C : Type) : ((A × B) × C) ≃ (A × (B × C)) :=
mk (λ t, match t with ((a, b), c) := (a, (b, c)) end)
   (λ t, match t with (a, (b, c)) := ((a, b), c) end)
   (λ t, begin cases t with ab c, cases ab, esimp end)
   (λ t, begin cases t with a bc, cases bc, esimp end)

section
open unit prod.ops
lemma prod_unit_right [simp] (A : Type) : (A × unit) ≃ A :=
mk (λ p, p.1)
   (λ a, (a, star))
   (λ p, begin cases p with a u, cases u, esimp end)
   (λ a, rfl)

lemma prod_unit_left [simp] (A : Type) : (unit × A) ≃ A :=
calc (unit × A) ≃ (A × unit) : prod_comm
            ... ≃ A          : prod_unit_right

lemma prod_empty_right [simp] (A : Type) : (A × empty) ≃ empty :=
mk (λ p, empty.rec _ p.2) (λ e, empty.rec _ e) (λ p, empty.rec _ p.2)  (λ e, empty.rec _ e)

lemma prod_empty_left [simp] (A : Type) : (empty × A) ≃ empty :=
calc (empty × A) ≃ (A × empty) : prod_comm
             ... ≃ empty       : prod_empty_right
end

section
open sum
lemma sum_congr [congr] {A₁ B₁ A₂ B₂ : Type} : A₁ ≃ A₂ → B₁ ≃ B₂ → (A₁ + B₁) ≃ (A₂ + B₂)
| (mk f₁ g₁ l₁ r₁) (mk f₂ g₂ l₂ r₂) :=
  mk
   (λ s, match s with inl a₁ := inl (f₁ a₁) | inr b₁ := inr (f₂ b₁) end)
   (λ s, match s with inl a₂ := inl (g₁ a₂) | inr b₂ := inr (g₂ b₂) end)
   (λ s, begin cases s, {esimp, rewrite l₁}, {esimp, rewrite l₂} end)
   (λ s, begin cases s, {esimp, rewrite r₁}, {esimp, rewrite r₂} end)

open bool unit
lemma bool_equiv_unit_sum_unit : bool ≃ (unit + unit) :=
mk (λ b, match b with tt := inl star | ff := inr star end)
   (λ s, match s with inl star := tt | inr star := ff end)
   (λ b, begin cases b, esimp, esimp end)
   (λ s, begin cases s with u u, {cases u, esimp}, {cases u, esimp} end)

lemma sum_comm [simp] (A B : Type) : (A + B) ≃ (B + A) :=
mk (λ s, match s with inl a := inr a | inr b := inl b end)
   (λ s, match s with inl b := inr b | inr a := inl a end)
   (λ s, begin cases s, esimp, esimp end)
   (λ s, begin cases s, esimp, esimp end)

lemma sum_assoc [simp] (A B C : Type) : ((A + B) + C) ≃ (A + (B + C)) :=
mk (λ s, match s with inl (inl a) := inl a | inl (inr b) := inr (inl b) | inr c := inr (inr c) end)
   (λ s, match s with inl a := inl (inl a) | inr (inl b) := inl (inr b) | inr (inr c) := inr c end)
   (λ s, begin cases s with ab c, cases ab, repeat esimp end)
   (λ s, begin cases s with a bc, esimp, cases bc, repeat esimp end)

lemma sum_empty_right [simp] (A : Type) : (A + empty) ≃ A :=
mk (λ s, match s with inl a := a | inr e := empty.rec _ e end)
   (λ a, inl a)
   (λ s, begin cases s with a e, esimp, exact empty.rec _ e end)
   (λ a, rfl)

lemma sum_empty_left [simp] (A : Type) : (empty + A) ≃ A :=
calc (empty + A) ≃ (A + empty) : sum_comm
          ...    ≃ A           : sum_empty_right
end

section
open prod.ops
lemma arrow_prod_equiv_prod_arrow (A B C : Type) : (C → A × B) ≃ ((C → A) × (C → B)) :=
mk (λ f, (λ c, (f c).1, λ c, (f c).2))
   (λ p, λ c, (p.1 c, p.2 c))
   (λ f, funext (λ c, begin esimp, cases f c, esimp end))
   (λ p, begin cases p, esimp end)

lemma arrow_arrow_equiv_prod_arrow (A B C : Type) : (A → B → C) ≃ (A × B → C) :=
mk (λ f, λ p, f p.1 p.2)
   (λ f, λ a b, f (a, b))
   (λ f, rfl)
   (λ f, funext (λ p, begin cases p, esimp end))

open sum
lemma sum_arrow_equiv_prod_arrow (A B C : Type) : ((A + B) → C) ≃ ((A → C) × (B → C)) :=
mk (λ f, (λ a, f (inl a), λ b, f (inr b)))
   (λ p, (λ s, match s with inl a := p.1 a | inr b := p.2 b end))
   (λ f, funext (λ s, begin cases s, esimp, esimp end))
   (λ p, begin cases p, esimp end)

lemma sum_prod_distrib (A B C : Type) : ((A + B) × C) ≃ ((A × C) + (B × C)) :=
mk (λ p, match p with (inl a, c) := inl (a, c) | (inr b, c) := inr (b, c) end)
   (λ s, match s with inl (a, c) := (inl a, c) | inr (b, c) := (inr b, c) end)
   (λ p, begin cases p with ab c, cases ab, repeat esimp end)
   (λ s, begin cases s with ac bc, cases ac, esimp, cases bc, esimp end)

lemma prod_sum_distrib (A B C : Type) : (A × (B + C)) ≃ ((A × B) + (A × C)) :=
calc (A × (B + C)) ≃ ((B + C) × A)       : prod_comm
             ...   ≃ ((B × A) + (C × A)) : sum_prod_distrib
             ...   ≃ ((A × B) + (A × C)) : sum_congr !prod_comm !prod_comm

lemma bool_prod_equiv_sum (A : Type) : (bool × A) ≃ (A + A) :=
calc (bool × A) ≃ ((unit + unit) × A)       : prod_congr bool_equiv_unit_sum_unit !equiv.refl
        ...     ≃ (A × (unit + unit))       : prod_comm
        ...     ≃ ((A × unit) + (A × unit)) : prod_sum_distrib
        ...     ≃ (A + A)                   : sum_congr !prod_unit_right !prod_unit_right
end

section
open sum nat unit prod.ops
lemma nat_equiv_nat_sum_unit : nat ≃ (nat + unit) :=
mk (λ n, match n with zero := inr star | succ a := inl a end)
   (λ s, match s with inl n := succ n | inr star := zero end)
   (λ n, begin cases n, repeat esimp end)
   (λ s, begin cases s with a u, esimp, {cases u, esimp} end)

lemma nat_sum_unit_equiv_nat [simp] : (nat + unit) ≃ nat :=
equiv.symm nat_equiv_nat_sum_unit

lemma nat_prod_nat_equiv_nat [simp] : (nat × nat) ≃ nat :=
mk (λ p, mkpair p.1 p.2)
   (λ n, unpair n)
   (λ p, begin cases p, apply unpair_mkpair end)
   (λ n, mkpair_unpair n)

lemma nat_sum_bool_equiv_nat [simp] : (nat + bool) ≃ nat :=
calc (nat + bool) ≃ (nat + (unit + unit)) : sum_congr !equiv.refl bool_equiv_unit_sum_unit
             ...  ≃ ((nat + unit) + unit) : sum_assoc
             ...  ≃ (nat + unit)          : sum_congr nat_sum_unit_equiv_nat !equiv.refl
             ...  ≃ nat                   : nat_sum_unit_equiv_nat

open decidable
lemma nat_sum_nat_equiv_nat [simp] : (nat + nat) ≃ nat :=
mk (λ s, match s with inl n := 2*n | inr n := 2*n+1 end)
   (λ n, if even n then inl (n div 2) else inr ((n - 1) div 2))
   (λ s, begin
           have two_gt_0 : 2 > zero, from dec_trivial,
           cases s,
             {esimp, rewrite [if_pos (even_two_mul _), mul_div_cancel_left _ two_gt_0]},
             {esimp, rewrite [if_neg (not_even_two_mul_plus_one _), add_sub_cancel, mul_div_cancel_left _ two_gt_0]}
         end)
   (λ n, by_cases
          (λ h : even n, begin rewrite [if_pos h], esimp, rewrite [mul_div_cancel' (dvd_of_even h)]  end)
          (λ h : ¬ even n,
            begin
              rewrite [if_neg h], esimp,
              cases n,
                {exact absurd even_zero h},
                {rewrite [-add_one, add_sub_cancel,
                          mul_div_cancel' (dvd_of_even (even_of_odd_succ (odd_of_not_even h)))]}
            end))

lemma prod_equiv_of_equiv_nat {A : Type} : A ≃ nat → (A × A) ≃ A :=
take e, calc
  (A × A) ≃ (nat × nat) : prod_congr e e
     ...  ≃ nat         : nat_prod_nat_equiv_nat
     ...  ≃ A           : equiv.symm e
end

section
open decidable
definition decidable_eq_of_equiv {A B : Type} [h : decidable_eq A] : A ≃ B → decidable_eq B
| (mk f g l r) :=
  take b₁ b₂, match h (g b₁) (g b₂) with
  | inl he := inl (assert aux : f (g b₁) = f (g b₂), from congr_arg f he,
                   begin rewrite *r at aux, exact aux end)
  | inr hn := inr (λ b₁eqb₂, by subst b₁eqb₂; exact absurd rfl hn)
  end
end

definition inhabited_of_equiv {A B : Type} [h : inhabited A] : A ≃ B → inhabited B
| (mk f g l r) := inhabited.mk (f (inhabited.value h))

section
open subtype
override equiv.ops
definition subtype_equiv_of_subtype {A B : Type} {p : A → Prop} : A ≃ B → {a : A | p a} ≃ {b : B | p (b⁻¹)}
| (mk f g l r) :=
  mk (λ s, match s with tag v h := tag (f v) (eq.rec_on (eq.symm (l v)) h) end)
     (λ s, match s with tag v h := tag (g v) (eq.rec_on (eq.symm (r v)) h) end)
     (λ s, begin cases s, esimp, congruence, rewrite l, reflexivity end)
     (λ s, begin cases s, esimp, congruence, rewrite r, reflexivity end)
end
end equiv
