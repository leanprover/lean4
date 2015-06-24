/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of suspension
-/

import .pushout types.pointed

open pushout unit eq equiv equiv.ops pointed

definition suspension (A : Type) : Type := pushout (λ(a : A), star) (λ(a : A), star)

namespace suspension
  variable {A : Type}

  definition north (A : Type) : suspension A :=
  inl _ _ star

  definition south (A : Type) : suspension A :=
  inr _ _ star

  definition merid (a : A) : north A = south A :=
  glue _ _ a

  protected definition rec {P : suspension A → Type} (PN : P !north) (PS : P !south)
    (Pm : Π(a : A), PN =[merid a] PS) (x : suspension A) : P x :=
  begin
    fapply pushout.rec_on _ _ x,
    { intro u, cases u, exact PN},
    { intro u, cases u, exact PS},
    { exact Pm},
  end

  protected definition rec_on [reducible] {P : suspension A → Type} (y : suspension A)
    (PN : P !north) (PS : P !south) (Pm : Π(a : A), PN =[merid a] PS) : P y :=
  suspension.rec PN PS Pm y

  theorem rec_merid {P : suspension A → Type} (PN : P !north) (PS : P !south)
    (Pm : Π(a : A), PN =[merid a] PS) (a : A)
      : apdo (suspension.rec PN PS Pm) (merid a) = Pm a :=
  !rec_glue

  protected definition elim {P : Type} (PN : P) (PS : P) (Pm : A → PN = PS)
    (x : suspension A) : P :=
  suspension.rec PN PS (λa, pathover_of_eq (Pm a)) x

  protected definition elim_on [reducible] {P : Type} (x : suspension A)
    (PN : P) (PS : P)  (Pm : A → PN = PS) : P :=
  suspension.elim PN PS Pm x

  theorem elim_merid {P : Type} (PN : P) (PS : P) (Pm : A → PN = PS) (a : A)
    : ap (suspension.elim PN PS Pm) (merid a) = Pm a :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (merid a)),
    rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑suspension.elim,rec_merid],
  end

  protected definition elim_type (PN : Type) (PS : Type) (Pm : A → PN ≃ PS)
    (x : suspension A) : Type :=
  suspension.elim PN PS (λa, ua (Pm a)) x

  protected definition elim_type_on [reducible] (x : suspension A)
    (PN : Type) (PS : Type)  (Pm : A → PN ≃ PS) : Type :=
  suspension.elim_type PN PS Pm x

  theorem elim_type_merid (PN : Type) (PS : Type) (Pm : A → PN ≃ PS)
    (a : A) : transport (suspension.elim_type PN PS Pm) (merid a) = Pm a :=
  by rewrite [tr_eq_cast_ap_fn,↑suspension.elim_type,elim_merid];apply cast_ua_fn

end suspension

attribute suspension.north suspension.south [constructor]
attribute suspension.rec suspension.elim [unfold-c 6] [recursor 6]
attribute suspension.elim_type [unfold-c 5]
attribute suspension.rec_on suspension.elim_on [unfold-c 3]
attribute suspension.elim_type_on [unfold-c 2]

namespace suspension

  definition pointed_suspension [instance] [constructor] (A : Type) : pointed (suspension A) :=
  pointed.mk !north

  definition suspension_adjoint_loop (A B : Pointed)
    : map₊ (pointed.mk' (suspension A)) B ≃ map₊ A (Ω B) :=
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

end suspension
