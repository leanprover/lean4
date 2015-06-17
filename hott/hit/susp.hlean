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
    fapply pushout.rec_on _ _ x,
    { intro u, cases u, exact PN},
    { intro u, cases u, exact PS},
    { exact Pm},
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
attribute susp.rec susp.elim [unfold-c 6] [recursor 6]
attribute susp.elim_type [unfold-c 5]
attribute susp.rec_on susp.elim_on [unfold-c 3]
attribute susp.elim_type_on [unfold-c 2]

namespace susp
  open pointed

  definition pointed_susp [instance] [constructor] (A : Type) : pointed (susp A) :=
  pointed.mk north

  definition Susp [constructor] (A : Type) : Pointed :=
  pointed.mk' (susp A)

  definition Susp_functor {X Y : Pointed} (f : X →* Y) : Susp X →* Susp Y :=
  begin
    fapply pmap.mk,
    { intro x, induction x,
        apply north,
        apply south,
        exact merid (f a)},
    { reflexivity}
  end

  definition Susp_functor_compose {X Y Z : Pointed} (g : Y →* Z) (f : X →* Y)
    : Susp_functor (g ∘* f) ~* Susp_functor g ∘* Susp_functor f :=
  begin
    fapply phomotopy.mk,
    { intro a, induction a,
      { reflexivity},
      { reflexivity},
      { apply pathover_eq, apply hdeg_square,
        rewrite [▸*,ap_compose' (Susp_functor f),↑Susp_functor,+elim_merid]}},
    { reflexivity}
  end

  -- adjunction from Coq-HoTT

  definition loop_susp_unit [constructor] (X : Pointed) : X →* Ω(Susp X) :=
  begin
    fapply pmap.mk,
    { intro x, exact merid x ⬝ (merid pt)⁻¹},
    { apply con.right_inv},
  end

  definition loop_susp_unit_natural {X Y : Pointed} (f : X →* Y)
    : loop_susp_unit Y ∘* f ~* ap1 (Susp_functor f) ∘* loop_susp_unit X :=
  begin
    induction X with X x, induction Y with Y y, induction f with f pf, esimp at *, induction pf,
    fapply phomotopy.mk,
    { intro x', esimp [Susp_functor],
      refine _ ⬝ !idp_con⁻¹,
      refine _ ⬝ !ap_con⁻¹,
      exact (!elim_merid ◾ (!ap_inv ⬝ inverse2 !elim_merid))⁻¹},
    { rewrite [▸*,idp_con (con.right_inv _)],
      exact sorry}, --apply inv_con_eq_of_eq_con,
  end

-- p ⬝ q ⬝ r means (p ⬝ q) ⬝ r

  definition susp_adjoint_loop (A B : Pointed)
    : map₊ (pointed.mk' (susp A)) B ≃ map₊ A (Ω B) := sorry

exit

Definition loop_susp_unit_natural {X Y : pType} (f : X ->* Y)
: loop_susp_unit Y o* f
  ==* loops_functor (psusp_functor f) o* loop_susp_unit X.
Proof.
  pointed_reduce.
  refine (Build_pHomotopy _ _); cbn.
  - intros x; symmetry.
    refine (concat_1p _@ (concat_p1 _ @ _)).
    refine (ap_pp (Susp_rec North South (merid o f))
                  (merid x) (merid (point X))^ @ _).
    refine ((1 @@ ap_V _ _) @ _).
    refine (Susp_comp_nd_merid _ @@ inverse2 (Susp_comp_nd_merid _)).
  - cbn. rewrite !inv_pp, !concat_pp_p, concat_1p; symmetry.
    apply moveL_Vp.
    refine (concat_pV_inverse2 _ _ (Susp_comp_nd_merid (point X)) @ _).
    do 2 apply moveL_Vp.
    refine (ap_pp_concat_pV _ _ @ _).
    do 2 apply moveL_Vp.
    rewrite concat_p1_1, concat_1p_1.
    cbn; symmetry.
    refine (concat_p1 _ @ _).
    refine (ap_compose (fun p' => (ap (Susp_rec North South (merid o f))) p' @ 1)
                       (fun p' => 1 @ p')
                       (concat_pV (merid (point X))) @ _).
    apply ap.
    refine (ap_compose (ap (Susp_rec North South (merid o f)))
                       (fun p' => p' @ 1) _).
Qed.

Definition loop_susp_counit (X : pType) : psusp (loops X) ->* X.
Proof.
  refine (Build_pMap (psusp (loops X)) X
                     (Susp_rec (point X) (point X) idmap) 1).
Defined.

Definition loop_susp_counit_natural {X Y : pType} (f : X ->* Y)
: f o* loop_susp_counit X
  ==* loop_susp_counit Y o* psusp_functor (loops_functor f).
Proof.
  pointed_reduce.
  refine (Build_pHomotopy _ _); simpl.
  - refine (Susp_ind _ _ _ _); cbn; try reflexivity; intros p.
    rewrite transport_paths_FlFr, ap_compose, concat_p1.
    apply moveR_Vp.
    refine (ap_compose
              (Susp_rec North South (fun x0 => merid (1 @ (ap f x0 @ 1))))
              (Susp_rec (point Y) (point Y) idmap) (merid p) @ _).
    do 2 rewrite Susp_comp_nd_merid.
    refine (Susp_comp_nd_merid _ @ _). (** Not sure why [rewrite] fails here *)
    apply concat_1p.
  - reflexivity.
Qed.

(** Now the triangle identities *)

Definition loop_susp_triangle1 (X : pType)
: loops_functor (loop_susp_counit X) o* loop_susp_unit (loops X)
  ==* pmap_idmap (loops X).
Proof.
  refine (Build_pHomotopy _ _).
  - intros p; cbn.
    refine (concat_1p _ @ (concat_p1 _ @ _)).
    refine (ap_pp (Susp_rec (point X) (point X) idmap)
                  (merid p) (merid (point (point X = point X)))^ @ _).
    refine ((1 @@ ap_V _ _) @ _).
    refine ((Susp_comp_nd_merid p @@ inverse2 (Susp_comp_nd_merid (point (loops X)))) @ _).
    exact (concat_p1 _).
  - destruct X as [X x]; cbn; unfold point.
    apply whiskerR.
    rewrite (concat_pV_inverse2
               (ap (Susp_rec x x idmap) (merid 1))
               1 (Susp_comp_nd_merid 1)).
    rewrite (ap_pp_concat_pV (Susp_rec x x idmap) (merid 1)).
    rewrite ap_compose, (ap_compose _ (fun p => p @ 1)).
    rewrite concat_1p_1; apply ap.
    apply concat_p1_1.
Qed.

Definition loop_susp_triangle2 (X : pType)
: loop_susp_counit (psusp X) o* psusp_functor (loop_susp_unit X)
  ==* pmap_idmap (psusp X).
Proof.
  refine (Build_pHomotopy _ _);
  [ refine (Susp_ind _ _ _ _) | ]; try reflexivity; cbn.
  - exact (merid (point X)).
  - intros x.
    rewrite transport_paths_FlFr, ap_idmap, ap_compose.
    rewrite Susp_comp_nd_merid.
    apply moveR_pM; rewrite concat_p1.
    refine (inverse2 (Susp_comp_nd_merid _) @ _).
    rewrite inv_pp, inv_V; reflexivity.
Qed.

(** Now we can finally construct the adjunction equivalence. *)

Definition loop_susp_adjoint `{Funext} (A B : pType)
: (psusp A ->* B) <~> (A ->* loops B).
Proof.
  refine (equiv_adjointify
            (fun f => loops_functor f o* loop_susp_unit A)
            (fun g => loop_susp_counit B o* psusp_functor g) _ _).
  - intros g. apply path_pmap.
    refine (pmap_prewhisker _ (loops_functor_compose _ _) @* _).
    refine (pmap_compose_assoc _ _ _ @* _).
    refine (pmap_postwhisker _ (loop_susp_unit_natural g)^* @* _).
    refine ((pmap_compose_assoc _ _ _)^* @* _).
    refine (pmap_prewhisker g (loop_susp_triangle1 B) @* _).
    apply pmap_postcompose_idmap.
  - intros f. apply path_pmap.
    refine (pmap_postwhisker _ (psusp_functor_compose _ _) @* _).
    refine ((pmap_compose_assoc _ _ _)^* @* _).
    refine (pmap_prewhisker _ (loop_susp_counit_natural f)^* @* _).
    refine (pmap_compose_assoc _ _ _ @* _).
    refine (pmap_postwhisker f (loop_susp_triangle2 A) @* _).
    apply pmap_precompose_idmap.
Defined.

(** And its naturality is easy. *)

Definition loop_susp_adjoint_nat_r `{Funext} (A B B' : pType)
           (f : psusp A ->* B) (g : B ->* B')
: loop_susp_adjoint A B' (g o* f)
  ==* loops_functor g o* loop_susp_adjoint A B f.
Proof.
  cbn.
  refine (_ @* pmap_compose_assoc _ _ _).
  apply pmap_prewhisker.
  refine (loops_functor_compose g f).
Defined.

Definition loop_susp_adjoint_nat_l `{Funext} (A A' B : pType)
           (f : A ->* loops B) (g : A' ->* A)
: (loop_susp_adjoint A' B)^-1 (f o* g)
  ==* (loop_susp_adjoint A B)^-1 f o* psusp_functor g.
Proof.
  cbn.
  refine (_ @* (pmap_compose_assoc _ _ _)^*).
  apply pmap_postwhisker.
  refine (psusp_functor_compose f g).
Defined.



  definition susp_adjoint_loop (A B : Pointed)
    : map₊ (pointed.mk' (susp A)) B ≃ map₊ A (Ω B) :=
  begin
    fapply equiv.MK,
    { intro f, fapply pointed_map.mk,
       intro a, refine !respect_pt⁻¹ ⬝ ap f (merid a ⬝ (merid pt)⁻¹) ⬝ !respect_pt,
       refine ap _ !con.right_inv ⬝ !con.left_inv},
    { intro g, fapply pointed_map.mk,
      { esimp, intro a, induction a,
          exact pt,
          exact pt,
          exact g a} ,
      { reflexivity}},
    { intro g, fapply pointed_map_eq,
        intro a, esimp [respect_pt], refine !idp_con ⬝ !ap_con ⬝ ap _ !ap_inv
           ⬝ ap _ !elim_merid ⬝ ap _ !elim_merid ⬝ ap _ (respect_pt g) ⬝ _, exact idp,
        -- rewrite [ap_con,ap_inv,+elim_merid,idp_con,respect_pt],
       esimp, exact sorry},
    { intro f, fapply pointed_map_eq,
      { esimp, intro a, induction a; all_goals esimp,
          exact !respect_pt⁻¹,
          exact !respect_pt⁻¹ ⬝ ap f (merid pt),
          apply pathover_eq, exact sorry},
      { esimp, exact !con.left_inv⁻¹}},
  end

end susp
