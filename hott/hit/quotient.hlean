/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Quotients. This is a quotient without truncation for an arbitrary type-valued binary relation.
See also .set_quotient
-/

/-
  The hit quotient is primitive, declared in init.hit.
  The constructors are, given {A : Type} (R : A → A → Type),
  * class_of : A → quotient R (A implicit, R explicit)
  * eq_of_rel : Π{a a' : A}, R a a' → class_of a = class_of a' (R explicit)
-/

import arity cubical.squareover types.arrow cubical.pathover2

open eq equiv sigma sigma.ops equiv.ops pi is_trunc

namespace quotient

  variables {A : Type} {R : A → A → Type}

  protected definition elim {P : Type} (Pc : A → P) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a')
    (x : quotient R) : P :=
  quotient.rec Pc (λa a' H, pathover_of_eq (Pp H)) x

  protected definition elim_on [reducible] {P : Type} (x : quotient R)
    (Pc : A → P) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') : P :=
  quotient.elim Pc Pp x

  theorem elim_eq_of_rel {P : Type} (Pc : A → P)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') {a a' : A} (H : R a a')
    : ap (quotient.elim Pc Pp) (eq_of_rel R H) = Pp H :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (eq_of_rel R H)),
    rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑quotient.elim,rec_eq_of_rel],
  end

  protected definition rec_prop {A : Type} {R : A → A → Type} {P : quotient R → Type}
    [H : Πx, is_prop (P x)] (Pc : Π(a : A), P (class_of R a)) (x : quotient R) : P x :=
  quotient.rec Pc (λa a' H, !is_prop.elimo) x

  protected definition elim_prop {P : Type} [H : is_prop P] (Pc : A → P) (x : quotient R) : P :=
  quotient.elim Pc (λa a' H, !is_prop.elim) x

  protected definition elim_type (Pc : A → Type)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') : quotient R → Type :=
  quotient.elim Pc (λa a' H, ua (Pp H))

  protected definition elim_type_on [reducible] (x : quotient R) (Pc : A → Type)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') : Type :=
  quotient.elim_type Pc Pp x

  theorem elim_type_eq_of_rel_fn (Pc : A → Type)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') {a a' : A} (H : R a a')
    : transport (quotient.elim_type Pc Pp) (eq_of_rel R H) = to_fun (Pp H) :=
  by rewrite [tr_eq_cast_ap_fn, ↑quotient.elim_type, elim_eq_of_rel];apply cast_ua_fn

  theorem elim_type_eq_of_rel.{u} (Pc : A → Type.{u})
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') {a a' : A} (H : R a a') (p : Pc a)
    : transport (quotient.elim_type Pc Pp) (eq_of_rel R H) p = to_fun (Pp H) p :=
  ap10 (elim_type_eq_of_rel_fn Pc Pp H) p

  definition elim_type_eq_of_rel' (Pc : A → Type)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') {a a' : A} (H : R a a') (p : Pc a)
    : pathover (quotient.elim_type Pc Pp) p (eq_of_rel R H) (to_fun (Pp H) p) :=
  pathover_of_tr_eq (elim_type_eq_of_rel Pc Pp H p)

  definition elim_type_uncurried (H : Σ(Pc : A → Type),  Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a')
    : quotient R → Type :=
  quotient.elim_type H.1 H.2
end quotient

attribute quotient.rec [recursor]
attribute quotient.elim [unfold 6] [recursor 6]
attribute quotient.elim_type [unfold 5]
attribute quotient.elim_on [unfold 4]
attribute quotient.elim_type_on [unfold 3]

namespace quotient

  section
    variables {A : Type} (R : A → A → Type)

    /- The dependent universal property -/
    definition quotient_pi_equiv (C : quotient R → Type) : (Πx, C x) ≃
      (Σ(f : Π(a : A), C (class_of R a)),  Π⦃a a' : A⦄ (H : R a a'), f a =[eq_of_rel R H] f a') :=
    begin
      fapply equiv.MK,
      { intro f, exact ⟨λa, f (class_of R a), λa a' H, apdo f (eq_of_rel R H)⟩},
      { intro v x, induction v with i p, induction x,
          exact (i a),
          exact (p H)},
      { intro v, induction v with i p, esimp,
        apply ap (sigma.mk i), apply eq_of_homotopy3, intro a a' H, apply rec_eq_of_rel},
      { intro f, apply eq_of_homotopy, intro x, induction x: esimp,
        apply eq_pathover_dep, esimp, rewrite rec_eq_of_rel, exact hrflo},
    end
  end

  /- the flattening lemma -/

  namespace flattening
  section

    parameters {A : Type} (R : A → A → Type) (C : A → Type) (f : Π⦃a a'⦄, R a a' → C a ≃ C a')
    include f
    variables {a a' : A} {r : R a a'}

    local abbreviation P [unfold 5] := quotient.elim_type C f

    definition flattening_type : Type := Σa, C a
    local abbreviation X := flattening_type
    inductive flattening_rel : X → X → Type :=
    | mk : Π⦃a a' : A⦄ (r : R a a') (c : C a), flattening_rel ⟨a, c⟩ ⟨a', f r c⟩

    definition Ppt [constructor] (c : C a) : sigma P :=
    ⟨class_of R a, c⟩

    definition Peq (r : R a a') (c : C a) : Ppt c = Ppt (f r c) :=
    begin
      fapply sigma_eq: esimp,
      { apply eq_of_rel R r},
      { refine elim_type_eq_of_rel' C f r c}
    end

    definition rec {Q : sigma P → Type} (Qpt : Π{a : A} (x : C a), Q (Ppt x))
      (Qeq : Π⦃a a' : A⦄ (r : R a a') (c : C a), Qpt c =[Peq r c] Qpt (f r c))
      (v : sigma P) : Q v :=
    begin
      induction v with q p,
      induction q,
      { exact Qpt p},
      { apply pi_pathover_left', esimp, intro c,
        refine _ ⬝op apd Qpt (elim_type_eq_of_rel C f H c)⁻¹ᵖ,
        refine _ ⬝op (tr_compose Q Ppt _ _)⁻¹ ,
        rewrite ap_inv,
        refine pathover_cancel_right _ !tr_pathover⁻¹ᵒ,
        refine change_path _ (Qeq H c),
        symmetry, rewrite [↑[Ppt, Peq]],
        refine whisker_left _ !ap_dpair ⬝ _,
        refine !dpair_eq_dpair_con⁻¹ ⬝ _, esimp,
        apply ap (dpair_eq_dpair _),
        esimp [elim_type_eq_of_rel',pathover_idp_of_eq],
        exact !pathover_of_tr_eq_eq_concato⁻¹},
    end

    definition elim {Q : Type} (Qpt : Π{a : A}, C a → Q)
      (Qeq : Π⦃a a' : A⦄ (r : R a a') (c : C a), Qpt c = Qpt (f r c))
      (v : sigma P) : Q :=
    begin
      induction v with q p,
      induction q,
      { exact Qpt p},
      { apply arrow_pathover_constant_right, esimp,
        intro c, exact Qeq H c ⬝ ap Qpt (elim_type_eq_of_rel C f H c)⁻¹},
    end

    theorem elim_Peq {Q : Type} (Qpt : Π{a : A}, C a → Q)
      (Qeq : Π⦃a a' : A⦄ (r : R a a') (c : C a), Qpt c = Qpt (f r c)) {a a' : A} (r : R a a')
      (c : C a) : ap (elim @Qpt Qeq) (Peq r c) = Qeq r c :=
    begin
      refine !ap_dpair_eq_dpair ⬝ _,
      rewrite [apo011_eq_apo11_apdo, rec_eq_of_rel, ▸*, apo011_arrow_pathover_constant_right,
               ↑elim_type_eq_of_rel', to_right_inv !pathover_equiv_tr_eq, ap_inv],
      apply inv_con_cancel_right
    end

    open flattening_rel
    definition flattening_lemma : sigma P ≃ quotient flattening_rel :=
    begin
      fapply equiv.MK,
      { refine elim _ _,
        { intro a c, exact class_of _ ⟨a, c⟩},
        { intro a a' r c, apply eq_of_rel, constructor}},
      { intro q, induction q with x x x' H,
        { exact Ppt x.2},
        { induction H, esimp, apply Peq}},
      { intro q, induction q with x x x' H: esimp,
        { induction x with a c, reflexivity},
        { induction H, esimp, apply eq_pathover, apply hdeg_square,
          refine ap_compose (elim _ _) (quotient.elim _ _) _ ⬝ _,
          rewrite [elim_eq_of_rel, ap_id, ▸*],
          apply elim_Peq}},
      { refine rec (λa x, idp) _, intros,
        apply eq_pathover, apply hdeg_square,
          refine ap_compose (quotient.elim _ _) (elim _ _) _ ⬝ _,
          rewrite [elim_Peq, ap_id, ▸*],
          apply elim_eq_of_rel}
    end

  end
  end flattening

end quotient
