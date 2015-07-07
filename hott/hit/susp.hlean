/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of suspension
-/

import .pushout types.pointed types.cubical.square

open pushout unit eq equiv equiv.ops

definition susp (A : Type) : Type := pushout (λ(a : A), star) (λ(a : A), star)

namespace susp
  variable {A : Type}

  definition north {A : Type} : susp A :=
  inl _ _ star

  definition south {A : Type} : susp A :=
  inr _ _ star

  definition merid (a : A) : @north A = @south A :=
  glue _ _ a

  protected definition rec {P : susp A → Type} (PN : P north) (PS : P south)
    (Pm : Π(a : A), PN =[merid a] PS) (x : susp A) : P x :=
  begin
    induction x with u u,
    { cases u, exact PN},
    { cases u, exact PS},
    { apply Pm},
  end

  protected definition rec_on [reducible] {P : susp A → Type} (y : susp A)
    (PN : P north) (PS : P south) (Pm : Π(a : A), PN =[merid a] PS) : P y :=
  susp.rec PN PS Pm y

  theorem rec_merid {P : susp A → Type} (PN : P north) (PS : P south)
    (Pm : Π(a : A), PN =[merid a] PS) (a : A)
      : apdo (susp.rec PN PS Pm) (merid a) = Pm a :=
  !rec_glue

  protected definition elim {P : Type} (PN : P) (PS : P) (Pm : A → PN = PS)
    (x : susp A) : P :=
  susp.rec PN PS (λa, pathover_of_eq (Pm a)) x

  protected definition elim_on [reducible] {P : Type} (x : susp A)
    (PN : P) (PS : P)  (Pm : A → PN = PS) : P :=
  susp.elim PN PS Pm x

  theorem elim_merid {P : Type} {PN PS : P} (Pm : A → PN = PS) (a : A)
    : ap (susp.elim PN PS Pm) (merid a) = Pm a :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (merid a)),
    rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑susp.elim,rec_merid],
  end

  protected definition elim_type (PN : Type) (PS : Type) (Pm : A → PN ≃ PS)
    (x : susp A) : Type :=
  susp.elim PN PS (λa, ua (Pm a)) x

  protected definition elim_type_on [reducible] (x : susp A)
    (PN : Type) (PS : Type)  (Pm : A → PN ≃ PS) : Type :=
  susp.elim_type PN PS Pm x

  theorem elim_type_merid (PN : Type) (PS : Type) (Pm : A → PN ≃ PS)
    (a : A) : transport (susp.elim_type PN PS Pm) (merid a) = Pm a :=
  by rewrite [tr_eq_cast_ap_fn,↑susp.elim_type,elim_merid];apply cast_ua_fn

end susp

attribute susp.north susp.south [constructor]
attribute susp.rec susp.elim [unfold 6] [recursor 6]
attribute susp.elim_type [unfold 5]
attribute susp.rec_on susp.elim_on [unfold 3]
attribute susp.elim_type_on [unfold 2]

namespace susp
  open pointed

  variables {X Y Z : Pointed}

  definition pointed_susp [instance] [constructor] (X : Type) : pointed (susp X) :=
  pointed.mk north

  definition Susp [constructor] (X : Type) : Pointed :=
  pointed.mk' (susp X)

  definition Susp_functor (f : X →* Y) : Susp X →* Susp Y :=
  begin
    fconstructor,
    { intro x, induction x,
        apply north,
        apply south,
        exact merid (f a)},
    { reflexivity}
  end

  definition Susp_functor_compose (g : Y →* Z) (f : X →* Y)
    : Susp_functor (g ∘* f) ~* Susp_functor g ∘* Susp_functor f :=
  begin
    fconstructor,
    { intro a, induction a,
      { reflexivity},
      { reflexivity},
      { apply pathover_eq, apply hdeg_square,
        rewrite [▸*,ap_compose' _ (Susp_functor f),↑Susp_functor,+elim_merid]}},
    { reflexivity}
  end

  -- adjunction from Coq-HoTT

  definition loop_susp_unit [constructor] (X : Pointed) : X →* Ω(Susp X) :=
  begin
    fconstructor,
    { intro x, exact merid x ⬝ (merid pt)⁻¹},
    { apply con.right_inv},
  end

  definition loop_susp_unit_natural (f : X →* Y)
    : loop_susp_unit Y ∘* f ~* ap1 (Susp_functor f) ∘* loop_susp_unit X :=
  begin
    induction X with X x, induction Y with Y y, induction f with f pf, esimp at *, induction pf,
    fconstructor,
    { intro x', esimp [Susp_functor], symmetry,
      exact
        !idp_con ⬝
        (!ap_con ⬝
        whisker_left _ !ap_inv) ⬝
        (!elim_merid ◾ (inverse2 !elim_merid))
        },
    { rewrite [▸*,idp_con (con.right_inv _)],
      apply inv_con_eq_of_eq_con,
      refine _ ⬝ !con.assoc',
      rewrite inverse2_right_inv,
      refine _ ⬝ !con.assoc',
      rewrite [ap_con_right_inv,↑Susp_functor,idp_con_idp,-ap_compose]},
  end

  definition loop_susp_counit [constructor] (X : Pointed) : Susp (Ω X) →* X :=
  begin
    fconstructor,
    { intro x, induction x, exact pt, exact pt, exact a},
    { reflexivity},
  end

  definition loop_susp_counit_natural (f : X →* Y)
    : f ∘* loop_susp_counit X ~* loop_susp_counit Y ∘* (Susp_functor (ap1 f)) :=
  begin
    induction X with X x, induction Y with Y y, induction f with f pf, esimp at *, induction pf,
    fconstructor,
    { intro x', induction x' with p,
      { reflexivity},
      { reflexivity},
      { esimp, apply pathover_eq, apply hdeg_square,
        xrewrite [ap_compose f,ap_compose (susp.elim (f x) (f x) (λ (a : f x = f x), a)),▸*,
                  +elim_merid,▸*,idp_con]}},
    { reflexivity}
  end

  definition loop_susp_counit_unit (X : Pointed)
    : ap1 (loop_susp_counit X) ∘* loop_susp_unit (Ω X) ~* pid (Ω X) :=
  begin
    induction X with X x, fconstructor,
    { intro p, esimp,
      refine !idp_con ⬝
             (!ap_con ⬝
             whisker_left _ !ap_inv) ⬝
             (!elim_merid ◾ inverse2 !elim_merid)},
    { rewrite [▸*,inverse2_right_inv (elim_merid function.id idp)],
      refine !con.assoc ⬝ _,
      xrewrite [ap_con_right_inv (susp.elim x x (λa, a)) (merid idp),idp_con_idp,-ap_compose]}
  end

  definition loop_susp_unit_counit (X : Pointed)
    : loop_susp_counit (Susp X) ∘* Susp_functor (loop_susp_unit X) ~* pid (Susp X) :=
  begin
    induction X with X x, fconstructor,
    { intro x', induction x',
      { reflexivity},
      { exact merid pt},
      { apply pathover_eq,
        xrewrite [▸*, ap_id, ap_compose (susp.elim north north (λa, a)), +elim_merid,▸*],
        apply square_of_eq, exact !idp_con ⬝ !inv_con_cancel_right⁻¹}},
    { reflexivity}
  end

  definition susp_adjoint_loop (X Y : Pointed) : map₊ (pointed.mk' (susp X)) Y ≃ map₊ X (Ω Y) :=
  begin
    fapply equiv.MK,
    { intro f, exact ap1 f ∘* loop_susp_unit X},
    { intro g, exact loop_susp_counit Y ∘* Susp_functor g},
    { intro g, apply eq_of_phomotopy, esimp,
      refine !pwhisker_right !ap1_compose ⬝* _,
      refine !passoc ⬝* _,
      refine !pwhisker_left !loop_susp_unit_natural⁻¹* ⬝* _,
      refine !passoc⁻¹* ⬝* _,
      refine !pwhisker_right !loop_susp_counit_unit ⬝* _,
      apply pid_comp},
    { intro f, apply eq_of_phomotopy, esimp,
      refine !pwhisker_left !Susp_functor_compose ⬝* _,
      refine !passoc⁻¹* ⬝* _,
      refine !pwhisker_right !loop_susp_counit_natural⁻¹* ⬝* _,
      refine !passoc ⬝* _,
      refine !pwhisker_left !loop_susp_unit_counit ⬝* _,
      apply comp_pid},
  end

  definition susp_adjoint_loop_nat_right (f : Susp X →* Y) (g : Y →* Z)
    : susp_adjoint_loop X Z (g ∘* f) ~* ap1 g ∘* susp_adjoint_loop X Y f :=
  begin
    esimp [susp_adjoint_loop],
    refine _ ⬝* !passoc,
    apply pwhisker_right,
    apply ap1_compose
  end

  definition susp_adjoint_loop_nat_left (f : Y →* Ω Z) (g : X →* Y)
    : (susp_adjoint_loop X Z)⁻¹ (f ∘* g) ~* (susp_adjoint_loop Y Z)⁻¹ f ∘* Susp_functor g :=
  begin
    esimp [susp_adjoint_loop],
    refine _ ⬝* !passoc⁻¹*,
    apply pwhisker_left,
    apply Susp_functor_compose
  end

end susp
