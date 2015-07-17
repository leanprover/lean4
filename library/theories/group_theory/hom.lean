/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/
import algebra.group data.set .subgroup

namespace group

open algebra
-- ⁻¹ in eq.ops conflicts with group ⁻¹
-- open eq.ops
notation H1 ▸ H2 := eq.subst H1 H2
open set
open function
open group.ops
open quot
local attribute set [reducible]

section defs

variables {A B : Type}
variable [s1 : group A]
variable [s2 : group B]
include s1
include s2

-- the Prop of being hom
definition homomorphic [reducible] (f : A → B) : Prop := ∀ a b, f (a*b) = (f a)*(f b)
-- type class for inference
structure is_hom_class [class] (f : A → B) : Type :=
          (is_hom : homomorphic f)
-- the proof of hom_prop if the class can be inferred
definition is_hom (f : A → B) [h : is_hom_class f] : homomorphic f :=
           @is_hom_class.is_hom A B s1 s2 f h

definition ker (f : A → B) [h : is_hom_class f] : set A := {a : A | f a = 1}

definition isomorphic (f : A → B) := injective f ∧ homomorphic f
structure is_iso_class [class] (f : A → B) extends is_hom_class f : Type :=
          (inj : injective f)
lemma iso_is_inj (f : A → B) [h : is_iso_class f] : injective f:=
      @is_iso_class.inj A B s1 s2 f h
lemma iso_is_iso (f : A → B) [h : is_iso_class f] : isomorphic f:=
      and.intro (iso_is_inj f) (is_hom f)

end defs

section
variables {A B : Type}
variable [s1 : group A]

definition id_is_iso [instance] : @is_hom_class A A s1 s1 (@id A) :=
is_iso_class.mk (take a b, rfl) injective_id

variable [s2 : group B]
include s1
include s2

variable f : A → B

variable [h : is_hom_class f]
include h

theorem hom_map_one : f 1 = 1 :=
        have P : f 1 = (f 1) * (f 1), from
        calc f 1 = f (1*1) : mul_one
        ... = (f 1) * (f 1) : is_hom f,
        eq.symm (mul.right_inv (f 1) ▸ (mul_inv_eq_of_eq_mul P))

theorem hom_map_inv (a : A) : f a⁻¹ = (f a)⁻¹ :=
        assert P : f 1 = 1, from hom_map_one f,
        assert P1 : f (a⁻¹ * a) = 1, from (eq.symm (mul.left_inv a)) ▸ P,
        assert P2 : (f a⁻¹) * (f a) = 1, from (is_hom f a⁻¹ a) ▸ P1,
        assert P3 : (f a⁻¹) * (f a) = (f a)⁻¹ * (f a), from eq.symm (mul.left_inv (f a)) ▸ P2,
        mul_right_cancel P3

theorem hom_map_mul_closed (H : set A) : mul_closed_on H → mul_closed_on (f '[H]) :=
        assume Pclosed, assume b1, assume b2,
        assume Pb1 : b1 ∈ f '[ H], assume Pb2 : b2 ∈ f '[ H],
        obtain a1 (Pa1 : a1 ∈ H ∧ f a1 = b1), from Pb1,
        obtain a2 (Pa2 : a2 ∈ H ∧ f a2 = b2), from Pb2,
        assert Pa1a2 : a1 * a2 ∈ H, from Pclosed a1 a2 (and.left Pa1) (and.left Pa2),
        assert Pb1b2 : f (a1 * a2) = b1 * b2, from calc
        f (a1 * a2) = f a1 * f a2 : is_hom f a1 a2
        ... = b1 * f a2 : {and.right Pa1}
        ... = b1 * b2 : {and.right Pa2},
        mem_image Pa1a2 Pb1b2

lemma ker.has_one : 1 ∈ ker f := hom_map_one f

lemma ker.has_inv : subgroup.has_inv (ker f) :=
      take a, assume Pa : f a = 1, calc
      f a⁻¹ = (f a)⁻¹ : by rewrite (hom_map_inv f)
      ... = 1⁻¹ : by rewrite Pa
      ... = 1 : by rewrite one_inv

lemma ker.mul_closed : mul_closed_on (ker f) :=
      take x y, assume (Px : f x = 1) (Py : f y = 1), calc
      f (x*y) = (f x) * (f y) : by rewrite [is_hom f]
      ... = 1 : by rewrite [Px, Py, mul_one]

lemma ker.normal : same_left_right_coset (ker f) :=
      take a, funext (assume x, begin
      esimp [ker, set_of, glcoset, grcoset],
      rewrite [*(is_hom f), mul_eq_one_iff_mul_eq_one (f a⁻¹) (f x)]
      end)

definition ker_is_normal_subgroup : is_normal_subgroup (ker f) :=
  is_normal_subgroup.mk (ker.has_one f) (ker.mul_closed f) (ker.has_inv f)
    (ker.normal f)

-- additional subgroup variable
variable {H : set A}
variable [is_subgH : is_subgroup H]
include is_subgH

theorem hom_map_subgroup : is_subgroup (f '[H]) :=
        have Pone : 1 ∈ f '[H], from mem_image subg_has_one (hom_map_one f),
        have Pclosed : mul_closed_on (f '[H]), from hom_map_mul_closed f H subg_mul_closed,
        assert Pinv : ∀ b, b ∈ f '[H] → b⁻¹ ∈ f '[H], from
          assume b, assume Pimg,
          obtain a (Pa : a ∈ H ∧ f a = b), from Pimg,
          assert Painv : a⁻¹ ∈ H, from subg_has_inv a (and.left Pa),
          assert Pfainv : (f a)⁻¹ ∈ f '[H], from mem_image Painv (hom_map_inv f a),
          and.right Pa ▸ Pfainv,
        is_subgroup.mk Pone Pclosed Pinv

end

section hom_theorem

variables {A B : Type}
variable [s1 : group A]
variable [s2 : group B]
include s1
include s2

variable {f : A → B}

variable [h : is_hom_class f]
include h

definition ker_nsubg [instance] : is_normal_subgroup (ker f) :=
           is_normal_subgroup.mk (ker.has_one f) (ker.mul_closed f)
           (ker.has_inv f) (ker.normal f)

definition quot_over_ker [instance] : group (coset_of (ker f)) := mk_quotient_group (ker f)
-- under the wrap the tower of concepts collapse to a simple condition
example (a x : A) : (x ∈ a ∘> ker f) = (f (a⁻¹*x) = 1) := rfl
lemma ker_coset_same_val (a b : A): same_lcoset (ker f) a b → f a = f b :=
      assume Psame,
      assert Pin : f (b⁻¹*a) = 1, from subg_same_lcoset_in_lcoset a b Psame,
      assert P : (f b)⁻¹ * (f a) = 1, from calc
      (f b)⁻¹ * (f a) = (f b⁻¹) * (f a) :  (hom_map_inv f)
      ... = f (b⁻¹*a) : by rewrite [is_hom f]
      ... = 1 : by rewrite Pin,
      eq.symm (inv_inv (f b) ▸ inv_eq_of_mul_eq_one P)

definition ker_natural_map : (coset_of (ker f)) → B :=
           quot.lift f ker_coset_same_val

example (a : A) : ker_natural_map ⟦a⟧ = f a := rfl
lemma ker_coset_hom (a b : A) :
      ker_natural_map (⟦a⟧*⟦b⟧) = (ker_natural_map ⟦a⟧) * (ker_natural_map ⟦b⟧) := calc
      ker_natural_map (⟦a⟧*⟦b⟧) = ker_natural_map ⟦a*b⟧ : rfl
      ... = f (a*b) : rfl
      ... = (f a) * (f b) : by rewrite [is_hom f]
      ... = (ker_natural_map ⟦a⟧) * (ker_natural_map ⟦b⟧) : rfl

lemma ker_map_is_hom : homomorphic (ker_natural_map : coset_of (ker f) → B) :=
  take aK bK,
      quot.ind (λ a, quot.ind (λ b, ker_coset_hom a b) bK) aK

lemma ker_coset_inj (a b : A) : (ker_natural_map ⟦a⟧ = ker_natural_map ⟦b⟧) → ⟦a⟧ = ⟦b⟧ :=
      assume Pfeq : f a = f b,
      assert Painb : a ∈ b ∘> ker f, from calc
      f (b⁻¹*a) = (f b⁻¹) * (f a) : by rewrite [is_hom f]
      ... = (f b)⁻¹ * (f a)       : by rewrite (hom_map_inv f)
      ... = (f a)⁻¹ * (f a)       : by rewrite Pfeq
      ... = 1                     : by rewrite (mul.left_inv (f a)),
      quot.sound (@subg_in_lcoset_same_lcoset _ _ (ker f) _ a b Painb)

lemma ker_map_is_inj : injective (ker_natural_map : coset_of (ker f) → B) :=
      take aK bK,
      quot.ind (λ a, quot.ind (λ b, ker_coset_inj a b) bK) aK

-- a special case of the fundamental homomorphism theorem or the first isomorphism theorem
theorem first_isomorphism_theorem : isomorphic (ker_natural_map : coset_of (ker f) → B) :=
        and.intro ker_map_is_inj ker_map_is_hom

end hom_theorem
end group
