/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: types.path
Author: Floris van Doorn

Ported from Coq HoTT
Theorems about path types (identity types)
-/

open eq sigma sigma.ops equiv is_equiv

namespace eq
  /- Path spaces -/

  /- The path spaces of a path space are not, of course, determined; they are just the
      higher-dimensional structure of the original space. -/

  /- Transporting in path spaces.

     There are potentially a lot of these lemmas, so we adopt a uniform naming scheme:

     - `l` means the left endpoint varies
     - `r` means the right endpoint varies
     - `F` means application of a function to that (varying) endpoint.
  -/

  variables {A B : Type} {a a1 a2 a3 a4 : A} {b b1 b2 : B} {f g : A → B} {h : B → A}

  definition transport_paths_l (p : a1 = a2) (q : a1 = a3)
    : transport (λx, x = a3) p q = p⁻¹ ⬝ q :=
  by cases p; cases q; apply idp

  definition transport_paths_r (p : a2 = a3) (q : a1 = a2)
    : transport (λx, a1 = x) p q = q ⬝ p :=
  by cases p; cases q; apply idp

  definition transport_paths_lr (p : a1 = a2) (q : a1 = a1)
    : transport (λx, x = x) p q = p⁻¹ ⬝ q ⬝ p :=
  begin
  apply (eq.rec_on p),
  apply inverse, apply concat,
    apply con_idp,
  apply idp_con
  end

  definition transport_paths_Fl (p : a1 = a2) (q : f a1 = b)
    : transport (λx, f x = b) p q = (ap f p)⁻¹ ⬝ q :=
  by cases p; cases q; apply idp

  definition transport_paths_Fr (p : a1 = a2) (q : b = f a1)
    : transport (λx, b = f x) p q = q ⬝ (ap f p) :=
  by cases p; apply idp

  definition transport_paths_FlFr (p : a1 = a2) (q : f a1 = g a1)
    : transport (λx, f x = g x) p q = (ap f p)⁻¹ ⬝ q ⬝ (ap g p) :=
  begin
  apply (eq.rec_on p),
  apply inverse, apply concat,
    apply con_idp,
  apply idp_con
  end

  definition transport_paths_FlFr_D {B : A → Type} {f g : Πa, B a}
    (p : a1 = a2) (q : f a1 = g a1)
      : transport (λx, f x = g x) p q = (apD f p)⁻¹ ⬝ ap (transport B p) q ⬝ (apD g p) :=
  begin
  apply (eq.rec_on p),
  apply inverse,
  apply concat, apply con_idp,
  apply concat, apply idp_con,
  apply ap_id
  end

  definition transport_paths_FFlr (p : a1 = a2) (q : h (f a1) = a1)
    : transport (λx, h (f x) = x) p q = (ap h (ap f p))⁻¹ ⬝ q ⬝ p :=
  begin
  apply (eq.rec_on p),
  apply inverse,
  apply concat, apply con_idp,
  apply idp_con,
  end

  definition transport_paths_lFFr (p : a1 = a2) (q : a1 = h (f a1))
    : transport (λx, x = h (f x)) p q = p⁻¹ ⬝ q ⬝ (ap h (ap f p)) :=
  begin
  apply (eq.rec_on p),
  apply inverse,
  apply concat, apply con_idp,
  apply idp_con,
  end


  -- The Functorial action of paths is [ap].

  /- Equivalences between path spaces -/

  /- [ap_closed] is in init.equiv  -/

  definition equiv_ap (f : A → B) [H : is_equiv f] (a1 a2 : A)
    : (a1 = a2) ≃ (f a1 = f a2) :=
  equiv.mk _ _

  /- Path operations are equivalences -/

  definition isequiv_path_inverse [instance] (a1 a2 : A) : is_equiv (@inverse A a1 a2) :=
  is_equiv.mk inverse inv_inv inv_inv (λp, eq.rec_on p idp)

  definition equiv_path_inverse (a1 a2 : A) : (a1 = a2) ≃ (a2 = a1) :=
  equiv.mk inverse _

  definition isequiv_concat_l [instance] (p : a1 = a2) (a3 : A)
    : is_equiv (@concat _ a1 a2 a3 p) :=
  is_equiv.mk (concat p⁻¹)
              (con_inv_cancel_left p)
              (inv_con_cancel_left p)
              (eq.rec_on p (λq, eq.rec_on q idp))

  definition equiv_concat_l (p : a1 = a2) (a3 : A) : (a1 = a3) ≃ (a2 = a3) :=
  equiv.mk (concat p⁻¹) _

  definition isequiv_concat_r [instance] (p : a2 = a3) (a1 : A)
    : is_equiv (λq : a1 = a2, q ⬝ p) :=
  is_equiv.mk (λq, q ⬝ p⁻¹)
              (λq, inv_con_cancel_right q p)
              (λq, con_inv_cancel_right q p)
              (eq.rec_on p (λq, eq.rec_on q idp))

  definition equiv_concat_r (p : a2 = a3) (a1 : A) : (a1 = a2) ≃ (a1 = a3) :=
  equiv.mk (λq, q ⬝ p) _

  definition equiv_concat_lr (p : a1 = a2) (q : a3 = a4) : (a1 = a3) ≃ (a2 = a4) :=
  equiv.trans (equiv_concat_l p a3) (equiv_concat_r q a2)


  -- a lot of this library still needs to be ported from Coq HoTT

--   set_option pp.beta true
--   check @cancel_left
--   set_option pp.full_names true
--   definition isequiv_whiskerL [instance] (p : a1 = a2) (q r : a2 = a3)
--   : is_equiv (@whisker_left A a1 a2 a3 p q r) :=
--   begin
--   fapply adjointify,
--     {intro H, apply (!cancel_left H)},
--     {intro s, }
-- --  reverts (q,r,a),  apply (eq.rec_on p), esimp {whisker_left,concat2, idp, cancel_left, eq.rec_on}, intros, esimp,
--   end
--  check @whisker_right_con_whisker_left
--   end
  /-begin
    refine (isequiv_adjointify _ _ _ _).
    - apply cancelL.
    - intros k. unfold cancelL.
      rewrite !whiskerL_pp.
      refine ((_ @@ 1 @@ _) ⬝ whiskerL_pVL p k).
      + destruct p, q; reflexivity.
      + destruct p, r; reflexivity.
    - intros k. unfold cancelL.
      refine ((_ @@ 1 @@ _) ⬝ whiskerL_VpL p k).
      + destruct p, q; reflexivity.
      + destruct p, r; reflexivity.
  end-/


  definition is_equiv_con_eq_of_eq_inv_con (p : a1 = a3) (q : a2 = a3) (r : a2 = a1)
  : is_equiv (con_eq_of_eq_inv_con p q r) :=
  begin
   cases r,
   apply (is_equiv_compose (λx, idp_con _ ⬝ x) (λx, x ⬝ idp_con _)),
  end


  definition equiv_moveR_Mp (p : a1 = a3) (q : a2 = a3) (r : a2 = a1)
    : (p = r⁻¹ ⬝ q) ≃ (r ⬝ p = q) :=
  calc
    (p = r⁻¹ ⬝ q) ≃ (r ⬝ p = r ⬝ (r⁻¹ ⬝ q)) : equiv_concat_l r
      ... ≃ (r ⬝ p = q) : sorry

  definition equiv_moveR_Mp (p : a1 = a3) (q : a2 = a3) (r : a2 = a1)
    : (p = r⁻¹ ⬝ q) ≃ (r ⬝ p = q) :=
  equiv. _ _ (con_eq_of_eq_inv_con p q r) _.

  Global Instance isequiv_moveR_pM
    {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
  : is_equiv (con_eq_of_eq_con_inv p q r).
  /-begin
    destruct p.
    apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
  end-/

  definition equiv_moveR_pM
    {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
  : (r = q ⬝ p⁻¹) ≃ (r ⬝ p = q) :=
     equiv.mk _ _ (con_eq_of_eq_con_inv p q r) _.

  Global Instance isequiv_moveR_Vp
    {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
  : is_equiv (inv_con_eq_of_eq_con p q r).
  /-begin
    destruct r.
    apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
  end-/

  definition equiv_moveR_Vp
    {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
  : (p = r ⬝ q) ≃ (r⁻¹ ⬝ p = q) :=
     equiv.mk _ _ (inv_con_eq_of_eq_con p q r) _.

  Global Instance isequiv_moveR_pV
    {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
  : is_equiv (con_inv_eq_of_eq_con p q r).
  /-begin
    destruct p.
    apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
  end-/

  definition equiv_moveR_pV
    {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
  : (r = q ⬝ p) ≃ (r ⬝ p⁻¹ = q) :=
     equiv.mk _ _ (con_inv_eq_of_eq_con p q r) _.

  Global Instance isequiv_moveL_Mp
    {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
  : is_equiv (eq_con_of_inv_con_eq p q r).
  /-begin
    destruct r.
    apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
  end-/

  definition equiv_moveL_Mp
    {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
  : (r⁻¹ ⬝ q = p) ≃ (q = r ⬝ p) :=
     equiv.mk _ _ (eq_con_of_inv_con_eq p q r) _.

  definition isequiv_moveL_pM
    {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
  : is_equiv (eq_con_of_con_inv_eq p q r).
  /-begin
    destruct p.
    apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
  end-/

  definition equiv_moveL_pM
    {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
    q ⬝ p⁻¹ = r ≃ q = r ⬝ p :=
       equiv.mk _ _ _ (isequiv_moveL_pM p q r).

  Global Instance isequiv_moveL_Vp
    {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
  : is_equiv (eq_inv_con_of_con_eq p q r).
  /-begin
    destruct r.
    apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
  end-/

  definition equiv_moveL_Vp
    {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
  : r ⬝ q = p ≃ q = r⁻¹ ⬝ p :=
     equiv.mk _ _ (eq_inv_con_of_con_eq p q r) _.

  Global Instance isequiv_moveL_pV
    {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
  : is_equiv (eq_con_inv_of_con_eq p q r).
  /-begin
    destruct p.
    apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
  end-/

  definition equiv_moveL_pV
    {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
  : q ⬝ p = r ≃ q = r ⬝ p⁻¹ :=
     equiv.mk _ _ (eq_con_inv_of_con_eq p q r) _.


end eq
