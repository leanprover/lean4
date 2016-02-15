/-
Copyright (c) 2014 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Ported from Coq HoTT
-/


import .equiv

open eq is_equiv equiv equiv.ops pointed is_trunc

-- structure pequiv (A B : Type*) :=
--   (to_pmap : A →* B)
--   (is_equiv_to_pmap : is_equiv to_pmap)

structure pequiv (A B : Type*) extends equiv A B, pmap A B

section
  universe variable u
  structure ptrunctype (n : trunc_index) extends trunctype.{u} n, pType.{u}
end

namespace pointed

  variables {A B C : Type*}

  /- pointed equivalences -/

  infix ` ≃* `:25 := pequiv
  attribute pequiv.to_pmap [coercion]
  attribute pequiv.to_is_equiv [instance]

  definition pequiv_of_pmap [constructor] (f : A →* B) (H : is_equiv f) : A ≃* B :=
  pequiv.mk f _ (respect_pt f)

  definition pequiv_of_equiv [constructor] (f : A ≃ B) (H : f pt = pt) : A ≃* B :=
  pequiv.mk f _ H

  definition equiv_of_pequiv [constructor] (f : A ≃* B) : A ≃ B :=
  equiv.mk f _

  definition to_pinv [constructor] (f : A ≃* B) : B →* A :=
  pmap.mk f⁻¹ (ap f⁻¹ (respect_pt f)⁻¹ ⬝ !left_inv)

  definition pua {A B : Type*} (f : A ≃* B) : A = B :=
  pType_eq (equiv_of_pequiv f) !respect_pt

  protected definition pequiv.refl [refl] [constructor] (A : Type*) : A ≃* A :=
  pequiv_of_pmap !pid !is_equiv_id

  protected definition pequiv.rfl [constructor] : A ≃* A :=
  pequiv.refl A

  protected definition pequiv.symm [symm] (f : A ≃* B) : B ≃* A :=
  pequiv_of_pmap (to_pinv f) !is_equiv_inv

  protected definition pequiv.trans [trans] (f : A ≃* B) (g : B ≃* C) : A ≃* C :=
  pequiv_of_pmap (pcompose g f) !is_equiv_compose

  postfix `⁻¹ᵉ*`:(max + 1) := pequiv.symm
  infix ` ⬝e* `:75 := pequiv.trans

  definition pequiv_rect' (f : A ≃* B) (P : A → B → Type)
    (g : Πb, P (f⁻¹ b) b) (a : A) : P a (f a) :=
  left_inv f a ▸ g (f a)

  definition pequiv_of_eq [constructor] {A B : Type*} (p : A = B) : A ≃* B :=
  pequiv_of_pmap (pcast p) !is_equiv_tr

  definition peconcat_eq {A B C : Type*} (p : A ≃* B) (q : B = C) : A ≃* C :=
  p ⬝e* pequiv_of_eq q

  definition eq_peconcat {A B C : Type*} (p : A = B) (q : B ≃* C) : A ≃* C :=
  pequiv_of_eq p ⬝e* q

  definition eq_of_pequiv {A B : Type*} (p : A ≃* B) : A = B :=
  pType_eq (equiv_of_pequiv p) !respect_pt

  definition peap {A B : Type*} (F : Type* → Type*) (p : A ≃* B) : F A ≃* F B :=
  pequiv_of_pmap (pcast (ap F (eq_of_pequiv p))) begin cases eq_of_pequiv p, apply is_equiv_id end

  definition loop_space_pequiv [constructor] (p : A ≃* B) : Ω A ≃* Ω B :=
  pequiv_of_pmap (ap1 p) (is_equiv_ap1 p)

  definition pequiv_eq {p q : A ≃* B} (H : p = q :> (A →* B)) : p = q :=
  begin
    cases p with f Hf, cases q with g Hg, esimp at *,
    exact apd011 pequiv_of_pmap H !is_prop.elim
  end

  definition loop_space_pequiv_rfl
    : loop_space_pequiv (@pequiv.refl A) = @pequiv.refl (Ω A) :=
  begin
    apply pequiv_eq, fapply pmap_eq: esimp,
    { intro p, exact !idp_con ⬝ !ap_id},
    { reflexivity}
  end

  infix ` ⬝e*p `:75 := peconcat_eq
  infix ` ⬝pe* `:75 := eq_peconcat

end pointed
