/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/
import algebra.group data data.fintype.function

open nat list algebra function

namespace group
open fintype

section perm
variable {A : Type}
variable [finA : fintype A]
include finA
variable [deceqA : decidable_eq A]
include deceqA
variable {f : A → A}

lemma perm_surj : injective f → surjective f :=
      surj_of_inj_eq_card (eq.refl (card A))

variable (perm : injective f)

definition perm_inv : A → A :=
      right_inv (perm_surj perm)

lemma perm_inv_right : f ∘ (perm_inv perm) = id :=
      right_inv_of_surj (perm_surj perm)

lemma perm_inv_left : (perm_inv perm) ∘ f = id :=
      have H : left_inverse f (perm_inv perm), from congr_fun (perm_inv_right perm),
      funext (take x, right_inverse_of_injective_of_left_inverse perm H x)

lemma perm_inv_inj : injective (perm_inv perm) :=
      injective_of_has_left_inverse (exists.intro f (congr_fun (perm_inv_right perm)))

end perm

structure perm (A : Type) [h : fintype A] : Type :=
  (f : A → A) (inj : injective f)
local attribute perm.f [coercion]

section perm
variable {A : Type}
variable [finA : fintype A]
include finA

lemma eq_of_feq : ∀ {p₁ p₂ : perm A}, (perm.f p₁) = p₂ → p₁ = p₂
| (perm.mk f₁ P₁) (perm.mk f₂ P₂) := assume (feq : f₁ = f₂), by congruence; assumption

lemma feq_of_eq : ∀ {p₁ p₂ : perm A}, p₁ = p₂ → (perm.f p₁) = p₂
| (perm.mk f₁ P₁) (perm.mk f₂ P₂) := assume Peq,
  have feq : f₁ = f₂, from perm.no_confusion Peq (λ Pe Pqe, Pe), feq

lemma eq_iff_feq {p₁ p₂ : perm A} : (perm.f p₁) = p₂ ↔ p₁ = p₂ :=
iff.intro eq_of_feq feq_of_eq

lemma perm.f_mk {f : A → A} {Pinj : injective f} : perm.f (perm.mk f Pinj) = f := rfl

definition move_by [reducible] (a : A) (f : perm A) : A := f a

variable [deceqA : decidable_eq A]
include deceqA

lemma perm.has_decidable_eq [instance] : decidable_eq (perm A) :=
      take f g,
      perm.destruct f (λ ff finj, perm.destruct g (λ gf ginj,
      decidable.rec_on (decidable_eq_fun ff gf)
      (λ Peq, decidable.inl (by substvars))
      (λ Pne, decidable.inr begin intro P, injection P, contradiction end)))

lemma dinj_perm_mk : dinj (@injective A A) perm.mk :=
      take a₁ a₂ Pa₁ Pa₂ Pmkeq, perm.no_confusion Pmkeq (λ Pe Pqe, Pe)

definition all_perms : list (perm A) :=
           dmap injective perm.mk (all_injs A)

lemma nodup_all_perms : nodup (@all_perms A _ _) :=
      dmap_nodup_of_dinj dinj_perm_mk nodup_all_injs

lemma all_perms_complete : ∀ p : perm A, p ∈ all_perms :=
      take p, perm.destruct p (take f Pinj,
        assert Pin : f ∈ all_injs A, from all_injs_complete Pinj,
        mem_dmap Pinj Pin)

definition perm_is_fintype [instance] : fintype (perm A) :=
           fintype.mk all_perms nodup_all_perms all_perms_complete

definition perm.mul (f g : perm A) :=
           perm.mk (f∘g) (injective_compose (perm.inj f) (perm.inj g))
definition perm.one [reducible] : perm A := perm.mk id injective_id
definition perm.inv (f : perm A) := let inj := perm.inj f in
           perm.mk (perm_inv inj) (perm_inv_inj inj)

local infix `^` := perm.mul
lemma perm.assoc (f g h : perm A) : f ^ g ^ h = f ^ (g ^ h) := rfl
lemma perm.one_mul (p : perm A) : perm.one ^ p = p :=
      perm.cases_on p (λ f inj, rfl)
lemma perm.mul_one (p : perm A) : p ^ perm.one = p :=
      perm.cases_on p (λ f inj, rfl)
lemma perm.left_inv (p : perm A) : (perm.inv p) ^ p = perm.one :=
      begin rewrite [↑perm.one], generalize @injective_id A,
      rewrite [-perm_inv_left (perm.inj p)], intros, exact rfl
      end
lemma perm.right_inv (p : perm A) : p ^ (perm.inv p) = perm.one :=
      begin rewrite [↑perm.one], generalize @injective_id A,
      rewrite [-perm_inv_right (perm.inj p)], intros, exact rfl
      end

definition perm_group [instance] : group (perm A) :=
           group.mk perm.mul perm.assoc perm.one perm.one_mul perm.mul_one perm.inv perm.left_inv

lemma perm_one : (1 : perm A) = perm.one := rfl

end perm

end group
