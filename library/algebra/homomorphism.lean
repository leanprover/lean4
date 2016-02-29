/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Homomorphisms between structures:

  is_add_hom    : structures with has_add
  is_mul_hom    : structures with has_mul
  is_module_hom : structures with has_add, has_smul
  is_ring_hom   : structures with has_add, has_mul

If you are working with a one particular kind of homomorphism, e.g. multiplicative, we recommend

  local abbreviation is_hom := @is_mul_hom

These are all tentatively declared as type classes. The theorems which infer id and compose
as instances are *not*, however, declared as instances: the first is rarely useful and the
second makes class inference loop.

Type class inference is useful here because usually a hypothesis like  is_hom f  is in the context.
If you need an instance that the system does not infer, simply put it in the context, e.g.

  assert is_hom f, from ...,
  ...
-/
import algebra.module data.set
open function set

variables {A B C : Type}

/- additive structures -/

definition add_ker [has_zero B] (f : A → B) : set A := {a | f a = 0}

proposition add_ker_eq [has_zero B] (f : A → B) : add_ker f = f '- '{0} :=
ext (take x, iff.intro
  (assume H, mem_preimage (mem_singleton_of_eq H))
  (assume H, eq_of_mem_singleton (mem_of_mem_preimage H)))

structure is_add_hom [class] [has_add A] [has_add B] (f : A → B) : Prop :=
(hom_add : ∀ a₁ a₂, f (a₁ + a₂) = f a₁ + f a₂)

proposition hom_add [has_add A] [has_add B] (f : A → B) [H : is_add_hom f] (a₁ a₂ : A) :
  f (a₁ + a₂) = f a₁ + f a₂ := is_add_hom.hom_add _ _ f a₁ a₂

proposition is_add_hom_id [has_add A] : is_add_hom (@id A) :=
is_add_hom.mk (take a₁ a₂, rfl)

proposition is_add_hom_comp [has_add A] [has_add B] [has_add C]
  {f : B → C} {g : A → B} [is_add_hom f] [is_add_hom g] : is_add_hom (f ∘ g) :=
is_add_hom.mk (take a₁ a₂, by esimp; rewrite *hom_add)

section add_group_A_B
  variables [add_group A] [add_group B]

  proposition hom_zero (f : A → B) [is_add_hom f] :
    f (0 : A) = 0 :=
  have f 0 + f 0 = f 0 + 0, by rewrite [-hom_add f, +add_zero],
  eq_of_add_eq_add_left this

  proposition hom_neg (f : A → B) [is_add_hom f] (a : A) :
    f (- a) = - f a :=
  have f (- a) + f a = 0, by rewrite [-hom_add f, add.left_inv, hom_zero],
  eq_neg_of_add_eq_zero this

  proposition hom_sub (f : A → B) [is_add_hom f] (a₁ a₂ : A) :
    f (a₁ - a₂) = f a₁ - f a₂ :=
  by rewrite [*sub_eq_add_neg, *hom_add, hom_neg]

  proposition injective_hom_add [add_group B] {f : A → B} [is_add_hom f]
      (H : ∀ x, f x = 0 → x = 0) :
    injective f :=
  take x₁ x₂,
  suppose f x₁ = f x₂,
  have f (x₁ - x₂) = 0, by rewrite [hom_sub, this, sub_self],
  have x₁ - x₂ = 0, from H _ this,
  eq_of_sub_eq_zero this

  proposition eq_zero_of_injective_hom [add_group B] {f : A → B} [is_add_hom f]
      (injf : injective f) {a : A} (fa0 : f a = 0) :
    a = 0 :=
  have f a = f 0, by rewrite [fa0, hom_zero],
  show a = 0, from injf this
end add_group_A_B

/- multiplicative structures -/

definition mul_ker [has_one B] (f : A → B) : set A := {a | f a = 1}

proposition mul_ker_eq [has_one B] (f : A → B) : mul_ker f = f '- '{1} :=
ext (take x, iff.intro
  (assume H, mem_preimage (mem_singleton_of_eq H))
  (assume H, eq_of_mem_singleton (mem_of_mem_preimage H)))

structure is_mul_hom [class] [has_mul A] [has_mul B] (f : A → B) : Prop :=
(hom_mul : ∀ a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂)

proposition hom_mul [has_mul A] [has_mul B] (f : A → B) [H : is_mul_hom f] (a₁ a₂ : A) :
  f (a₁ * a₂) = f a₁ * f a₂ := is_mul_hom.hom_mul _ _ f a₁ a₂

proposition is_mul_hom_id [has_mul A] : is_mul_hom (@id A) :=
is_mul_hom.mk (take a₁ a₂, rfl)

proposition is_mul_hom_comp [has_mul A] [has_mul B] [has_mul C]
  {f : B → C} {g : A → B} [is_mul_hom f] [is_mul_hom g] : is_mul_hom (f ∘ g) :=
is_mul_hom.mk (take a₁ a₂, by esimp; rewrite *hom_mul)

section group_A_B
  variables [group A] [group B]

  proposition hom_one (f : A → B) [is_mul_hom f] :
    f (1 : A) = 1 :=
  have f 1 * f 1 = f 1 * 1, by rewrite [-hom_mul f, *mul_one],
  eq_of_mul_eq_mul_left' this

  proposition hom_inv (f : A → B) [is_mul_hom f] (a : A) :
    f (a⁻¹) = (f a)⁻¹ :=
  have f (a⁻¹) * f a = 1, by rewrite [-hom_mul f, mul.left_inv, hom_one],
  eq_inv_of_mul_eq_one this

  proposition injective_hom_mul [group B] {f : A → B} [is_mul_hom f]
      (H : ∀ x, f x = 1 → x = 1) :
    injective f :=
  take x₁ x₂,
  suppose f x₁ = f x₂,
  have f (x₁ * x₂⁻¹) = 1, by rewrite [hom_mul, hom_inv, this, mul.right_inv],
  have x₁ * x₂⁻¹ = 1, from H _ this,
  eq_of_mul_inv_eq_one this

  proposition eq_one_of_injective_hom [group B] {f : A → B} [is_mul_hom f]
      (injf : injective f) {a : A} (fa1 : f a = 1) :
    a = 1 :=
  have f a = f 1, by rewrite [fa1, hom_one],
  show a = 1, from injf this
end group_A_B

/- modules -/

structure is_module_hom [class] (R : Type) {M₁ M₂ : Type}
  [has_scalar R M₁] [has_scalar R M₂] [has_add M₁] [has_add M₂]
  (f : M₁ → M₂) extends is_add_hom f :=
(hom_smul : ∀ r : R, ∀ a : M₁, f (r • a) = r • f a)

section module_hom
  variables {R : Type} {M₁ M₂ M₃ : Type}
  variables [has_scalar R M₁] [has_scalar R M₂] [has_scalar R M₃]
  variables [has_add M₁] [has_add M₂] [has_add M₃]
  variables (g : M₂ → M₃) (f : M₁ → M₂) [is_module_hom R g] [is_module_hom R f]

  proposition hom_smul (r : R) (a : M₁) : f (r • a) = r • f a :=
  is_module_hom.hom_smul _ _ _ _ f r a

  proposition is_module_hom_id : is_module_hom R (@id M₁) :=
  is_module_hom.mk (λ a₁ a₂, rfl) (λ r a, rfl)

  proposition is_module_hom_comp : is_module_hom R (g ∘ f) :=
  is_module_hom.mk
    (take a₁ a₂, by esimp; rewrite *hom_add)
    (take r a, by esimp; rewrite [hom_smul f, hom_smul g])

  proposition hom_smul_add_smul (a b : R) (u v : M₁) : f (a • u + b • v) = a • f u + b • f v :=
  by rewrite [hom_add, +hom_smul f]
end module_hom

/- rings -/

structure is_ring_hom [class] {R₁ R₂ : Type} [has_mul R₁] [has_mul R₂] [has_add R₁] [has_add R₂]
    (f : R₁ → R₂) extends is_add_hom f, is_mul_hom f

section semiring
  variables {R₁ R₂ R₃ : Type} [semiring R₁] [semiring R₂] [semiring R₃]
  variables (g : R₂ → R₃) (f : R₁ → R₂) [is_ring_hom g] [is_ring_hom f]

  proposition is_ring_hom_id : is_ring_hom (@id R₁) :=
  is_ring_hom.mk (λ a₁ a₂, rfl) (λ a₁ a₂, rfl)

  proposition is_ring_hom_comp : is_ring_hom (g ∘ f) :=
  is_ring_hom.mk
    (take a₁ a₂, by esimp; rewrite *hom_add)
    (take r a, by esimp; rewrite [hom_mul f, hom_mul g])

  proposition hom_mul_add_mul (a b c d : R₁) : f (a * b + c * d) = f a * f b + f c * f d :=
  by rewrite [hom_add, +hom_mul]
end semiring
