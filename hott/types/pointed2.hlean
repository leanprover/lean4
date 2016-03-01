/-
Copyright (c) 2014 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Ported from Coq HoTT
-/


import .equiv cubical.square

open eq is_equiv equiv equiv.ops pointed is_trunc

-- structure pequiv (A B : Type*) :=
--   (to_pmap : A →* B)
--   (is_equiv_to_pmap : is_equiv to_pmap)

structure pequiv (A B : Type*) extends equiv A B, pmap A B

namespace pointed

  attribute pequiv._trans_of_to_pmap pequiv._trans_of_to_equiv pequiv.to_pmap pequiv.to_equiv
            [unfold 3]

  variables {A B C : Type*}

  /- pointed equivalences -/

  infix ` ≃* `:25 := pequiv
  attribute pequiv.to_pmap [coercion]
  attribute pequiv.to_is_equiv [instance]

  definition pequiv_of_pmap [constructor] (f : A →* B) (H : is_equiv f) : A ≃* B :=
  pequiv.mk f _ (respect_pt f)

  definition pequiv_of_equiv [constructor] (f : A ≃ B) (H : f pt = pt) : A ≃* B :=
  pequiv.mk f _ H

  protected definition pequiv.MK [constructor] (f : A →* B) (g : B →* A)
    (gf : Πa, g (f a) = a) (fg : Πb, f (g b) = b) : A ≃* B :=
  pequiv.mk f (adjointify f g fg gf) (respect_pt f)

  definition equiv_of_pequiv [constructor] (f : A ≃* B) : A ≃ B :=
  equiv.mk f _

  definition to_pinv [constructor] (f : A ≃* B) : B →* A :=
  pmap.mk f⁻¹ ((ap f⁻¹ (respect_pt f))⁻¹ ⬝ !left_inv)

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

  definition iterated_loop_space_pequiv [constructor] (n : ℕ) (p : A ≃* B) : Ω[n] A ≃* Ω[n] B :=
  pequiv_of_pmap (apn n p) (is_equiv_apn n p)

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

  local attribute pequiv.symm [constructor]
  definition pleft_inv (f : A ≃* B) : f⁻¹ᵉ* ∘* f ~* pid A :=
  phomotopy.mk (left_inv f)
    abstract begin
      esimp, symmetry, apply con_inv_cancel_left
    end end

  definition pright_inv (f : A ≃* B) : f ∘* f⁻¹ᵉ* ~* pid B :=
  phomotopy.mk (right_inv f)
    abstract begin
      induction f with f H p, esimp,
      rewrite [ap_con, +ap_inv, -adj f, -ap_compose],
      note q := natural_square (right_inv f) p,
      rewrite [ap_id at q],
      apply eq_bot_of_square,
      exact transpose q
    end end

  definition pcancel_left (f : B ≃* C) {g h : A →* B} (p : f ∘* g ~* f ∘* h) : g ~* h :=
  begin
    refine _⁻¹* ⬝* pwhisker_left f⁻¹ᵉ* p ⬝* _:
    refine !passoc⁻¹* ⬝* _:
    refine pwhisker_right _ (pleft_inv f) ⬝* _:
    apply pid_comp
  end


  definition pcancel_right (f : A ≃* B) {g h : B →* C} (p : g ∘* f ~* h ∘* f) : g ~* h :=
  begin
    refine _⁻¹* ⬝* pwhisker_right f⁻¹ᵉ* p ⬝* _:
    refine !passoc ⬝* _:
    refine pwhisker_left _ (pright_inv f) ⬝* _:
    apply comp_pid
  end

  definition phomotopy_pinv_right_of_phomotopy {f : A ≃* B} {g : B →* C} {h : A →* C}
    (p : g ∘* f ~* h) : g ~* h ∘* f⁻¹ᵉ* :=
  begin
    refine _ ⬝* pwhisker_right _ p, symmetry,
    refine !passoc ⬝* _,
    refine pwhisker_left _ (pright_inv f) ⬝* _,
    apply comp_pid
  end

  definition phomotopy_of_pinv_right_phomotopy {f : B ≃* A} {g : B →* C} {h : A →* C}
    (p : g ∘* f⁻¹ᵉ* ~* h) : g ~* h ∘* f :=
  begin
    refine _ ⬝* pwhisker_right _ p, symmetry,
    refine !passoc ⬝* _,
    refine pwhisker_left _ (pleft_inv f) ⬝* _,
    apply comp_pid
  end

  definition pinv_right_phomotopy_of_phomotopy {f : A ≃* B} {g : B →* C} {h : A →* C}
    (p : h ~* g ∘* f) : h ∘* f⁻¹ᵉ* ~* g :=
  (phomotopy_pinv_right_of_phomotopy p⁻¹*)⁻¹*

  definition phomotopy_of_phomotopy_pinv_right {f : B ≃* A} {g : B →* C} {h : A →* C}
    (p : h ~* g ∘* f⁻¹ᵉ*) : h ∘* f ~* g :=
  (phomotopy_of_pinv_right_phomotopy p⁻¹*)⁻¹*

  definition phomotopy_pinv_left_of_phomotopy {f : B ≃* C} {g : A →* B} {h : A →* C}
    (p : f ∘* g ~* h) : g ~* f⁻¹ᵉ* ∘* h :=
  begin
    refine _ ⬝* pwhisker_left _ p, symmetry,
    refine !passoc⁻¹* ⬝* _,
    refine pwhisker_right _ (pleft_inv f) ⬝* _,
    apply pid_comp
  end

  definition phomotopy_of_pinv_left_phomotopy {f : C ≃* B} {g : A →* B} {h : A →* C}
    (p : f⁻¹ᵉ* ∘* g ~* h) : g ~* f ∘* h :=
  begin
    refine _ ⬝* pwhisker_left _ p, symmetry,
    refine !passoc⁻¹* ⬝* _,
    refine pwhisker_right _ (pright_inv f) ⬝* _,
    apply pid_comp
  end

  definition pinv_left_phomotopy_of_phomotopy {f : B ≃* C} {g : A →* B} {h : A →* C}
    (p : h ~* f ∘* g) : f⁻¹ᵉ* ∘* h ~* g :=
  (phomotopy_pinv_left_of_phomotopy p⁻¹*)⁻¹*

  definition phomotopy_of_phomotopy_pinv_left {f : C ≃* B} {g : A →* B} {h : A →* C}
    (p : h ~* f⁻¹ᵉ* ∘* g) : f ∘* h ~* g :=
  (phomotopy_of_pinv_left_phomotopy p⁻¹*)⁻¹*

  /- pointed equivalences between particular pointed types -/

  definition loop_pequiv_loop [constructor] (f : A ≃* B) : Ω A ≃* Ω B :=
  pequiv.MK (ap1 f) (ap1 f⁻¹ᵉ*)
  abstract begin
    intro p,
    refine ((ap1_compose f⁻¹ᵉ* f) p)⁻¹ ⬝ _,
    refine ap1_phomotopy (pleft_inv f) p ⬝ _,
    exact ap1_id p
  end end
  abstract begin
    intro p,
    refine ((ap1_compose f f⁻¹ᵉ*) p)⁻¹ ⬝ _,
    refine ap1_phomotopy (pright_inv f) p ⬝ _,
    exact ap1_id p
  end end

  definition loopn_pequiv_loopn (n : ℕ) (f : A ≃* B) : Ω[n] A ≃* Ω[n] B :=
  begin
    induction n with n IH,
    { exact f},
    { exact loop_pequiv_loop IH}
  end

  definition pmap_functor [constructor] {A A' B B' : Type*} (f : A' →* A) (g : B →* B') :
    ppmap A B →* ppmap A' B' :=
  pmap.mk (λh, g ∘* h ∘* f)
    abstract begin
      fapply pmap_eq,
      { esimp, intro a, exact respect_pt g},
      { rewrite [▸*, ap_constant], apply idp_con}
    end end

/-
  definition pmap_pequiv_pmap {A A' B B' : Type*} (f : A ≃* A') (g : B ≃* B') :
    ppmap A B ≃* ppmap A' B' :=
  pequiv.MK (pmap_functor f⁻¹ᵉ* g) (pmap_functor f g⁻¹ᵉ*)
    abstract begin
      intro a, esimp, apply pmap_eq,
      { esimp, },
      { }
    end end
    abstract begin

    end end
-/

end pointed
