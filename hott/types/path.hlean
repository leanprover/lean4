/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn
Ported from Coq HoTT

Theorems about path types (identity types)
-/

open eq sigma sigma.ops equiv is_equiv

namespace path
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
  begin
  apply (eq.rec_on p), apply (eq.rec_on q), apply idp
  end

  definition transport_paths_r (p : a2 = a3) (q : a1 = a2)
    : transport (λx, a1 = x) p q = q ⬝ p :=
  begin
  apply (eq.rec_on p), apply (eq.rec_on q), apply idp
  end

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
  begin
  apply (eq.rec_on p), apply (eq.rec_on q), apply idp
  end

  definition transport_paths_Fr (p : a1 = a2) (q : b = f a1)
    : transport (λx, b = f x) p q = q ⬝ (ap f p) :=
  begin
  apply (eq.rec_on p), apply idp
  end

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


  /- The Functorial action of paths is [ap]. -/

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
  is_equiv.mk (concat (p⁻¹))
              (con_inv_cancel_left p)
              (inv_con_cancel_left p)
              (eq.rec_on p (λq, eq.rec_on q idp))

  definition equiv_concat_l (p : a1 = a2) (a3 : A) : (a1 = a3) ≃ (a2 = a3) :=
  equiv.mk (concat (p⁻¹)) _

  definition isequiv_concat_r [instance] (p : a2 = a3) (a1 : A)
    : is_equiv (λq : a1 = a2, q ⬝ p) :=
  is_equiv.mk (λq, q ⬝ p⁻¹)
              (λq, inv_con_cancel_right q p)
              (λq, con_inv_cancel_right q p)
              (eq.rec_on p (λq, eq.rec_on q idp))

  definition equiv_concat_r (p : a2 = a3) (a1 : A) : (a1 = a2) ≃ (a1 = a3) :=
  equiv.mk (λq, q ⬝ p) _

  definition equiv_concat_lr {a1 a2 a3 a4 : A} (p : a1 = a2) (q : a3 = a4)
    : (a1 = a3) ≃ (a2 = a4) :=
  equiv.trans (equiv_concat_l p a3) (equiv_concat_r q a2)

/- BELOW STILL NEEDS TO BE PORTED FROM COQ HOTT -/

  -- definition isequiv_whiskerL [instance] (p : a1 = a2) (q r : a2 = a3)
  -- : is_equiv (@whisker_left A a1 a2 a3 p q r) :=
  -- begin

  -- end
  -- /-begin
  --   refine (isequiv_adjointify _ _ _ _).
  --   - apply cancelL.
  --   - intros k. unfold cancelL.
  --     rewrite !whiskerL_pp.
  --     refine ((_ @@ 1 @@ _) ⬝ whiskerL_pVL p k).
  --     + destruct p, q; reflexivity.
  --     + destruct p, r; reflexivity.
  --   - intros k. unfold cancelL.
  --     refine ((_ @@ 1 @@ _) ⬝ whiskerL_VpL p k).
  --     + destruct p, q; reflexivity.
  --     + destruct p, r; reflexivity.
  -- end-/

  -- definition equiv_whiskerL {A} {x y z : A} (p : x = y) (q r : y = z)
  -- : (q = r) ≃ (p ⬝ q = p ⬝ r) :=
  --      equiv.mk _ _ (whisker_left p) _.

  -- definition equiv_cancelL {A} {x y z : A} (p : x = y) (q r : y = z)
  -- : (p ⬝ q = p ⬝ r) ≃ (q = r) :=
  --      equiv_inverse (equiv_whiskerL p q r).

  -- definition isequiv_cancelL {A} {x y z : A} (p : x = y) (q r : y = z)
  --   : is_equiv (cancel_left p q r).
  -- /-begin
  --   change (is_equiv (equiv_cancelL p q r)); exact _.
  -- end-/

  -- definition isequiv_whiskerR [instance] {A} {x y z : A} {p q : x = y} (r : y = z)
  -- : is_equiv (λh, @whisker_right A x y z p q h r).
  -- /-begin
  --   refine (isequiv_adjointify _ _ _ _).
  --   - apply cancelR.
  --   - intros k. unfold cancelR.
  --     rewrite !whiskerR_pp.
  --     refine ((_ @@ 1 @@ _) ⬝ whiskerR_VpR k r).
  --     + destruct p, r; reflexivity.
  --     + destruct q, r; reflexivity.
  --   - intros k. unfold cancelR.
  --     refine ((_ @@ 1 @@ _) ⬝ whiskerR_pVR k r).
  --     + destruct p, r; reflexivity.
  --     + destruct q, r; reflexivity.
  -- end-/

  -- definition equiv_whiskerR {A} {x y z : A} (p q : x = y) (r : y = z)
  -- : (p = q) ≃ (p ⬝ r = q ⬝ r) :=
  --      equiv.mk _ _ (λh, whisker_right h r) _.

  -- definition equiv_cancelR {A} {x y z : A} (p q : x = y) (r : y = z)
  -- : (p ⬝ r = q ⬝ r) ≃ (p = q) :=
  --      equiv_inverse (equiv_whiskerR p q r).

  -- definition isequiv_cancelR {A} {x y z : A} (p q : x = y) (r : y = z)
  --   : is_equiv (cancel_right p q r).
  -- /-begin
  --   change (is_equiv (equiv_cancelR p q r)); exact _.
  -- end-/

  -- /- We can use these to build up more complicated equivalences.

  -- In particular, all of the [move] family are equivalences.

  -- (Note: currently, some but not all of these [isequiv_] lemmas have corresponding [equiv_] lemmas.  Also, they do *not* currently contain the computational content that e.g. the inverse of [moveR_Mp] is [moveL_Vp]; perhaps it would be useful if they did? -/

  -- Global Instance isequiv_moveR_Mp
  --  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
  -- : is_equiv (con_eq_of_eq_inv_con p q r).
  -- /-begin
  --   destruct r.
  --   apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
  -- end-/

  -- definition equiv_moveR_Mp
  --   {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
  -- : (p = r⁻¹ ⬝ q) ≃ (r ⬝ p = q) :=
  --    equiv.mk _ _ (con_eq_of_eq_inv_con p q r) _.

  -- Global Instance isequiv_moveR_pM
  --   {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
  -- : is_equiv (con_eq_of_eq_con_inv p q r).
  -- /-begin
  --   destruct p.
  --   apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
  -- end-/

  -- definition equiv_moveR_pM
  --   {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
  -- : (r = q ⬝ p⁻¹) ≃ (r ⬝ p = q) :=
  --    equiv.mk _ _ (con_eq_of_eq_con_inv p q r) _.

  -- Global Instance isequiv_moveR_Vp
  --   {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
  -- : is_equiv (inv_con_eq_of_eq_con p q r).
  -- /-begin
  --   destruct r.
  --   apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
  -- end-/

  -- definition equiv_moveR_Vp
  --   {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
  -- : (p = r ⬝ q) ≃ (r⁻¹ ⬝ p = q) :=
  --    equiv.mk _ _ (inv_con_eq_of_eq_con p q r) _.

  -- Global Instance isequiv_moveR_pV
  --   {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
  -- : is_equiv (con_inv_eq_of_eq_con p q r).
  -- /-begin
  --   destruct p.
  --   apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
  -- end-/

  -- definition equiv_moveR_pV
  --   {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
  -- : (r = q ⬝ p) ≃ (r ⬝ p⁻¹ = q) :=
  --    equiv.mk _ _ (con_inv_eq_of_eq_con p q r) _.

  -- Global Instance isequiv_moveL_Mp
  --   {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
  -- : is_equiv (eq_con_of_inv_con_eq p q r).
  -- /-begin
  --   destruct r.
  --   apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
  -- end-/

  -- definition equiv_moveL_Mp
  --   {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
  -- : (r⁻¹ ⬝ q = p) ≃ (q = r ⬝ p) :=
  --    equiv.mk _ _ (eq_con_of_inv_con_eq p q r) _.

  -- definition isequiv_moveL_pM
  --   {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
  -- : is_equiv (eq_con_of_con_inv_eq p q r).
  -- /-begin
  --   destruct p.
  --   apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
  -- end-/

  -- definition equiv_moveL_pM
  --   {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  --   q ⬝ p⁻¹ = r ≃ q = r ⬝ p :=
  --      equiv.mk _ _ _ (isequiv_moveL_pM p q r).

  -- Global Instance isequiv_moveL_Vp
  --   {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
  -- : is_equiv (eq_inv_con_of_con_eq p q r).
  -- /-begin
  --   destruct r.
  --   apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
  -- end-/

  -- definition equiv_moveL_Vp
  --   {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
  -- : r ⬝ q = p ≃ q = r⁻¹ ⬝ p :=
  --    equiv.mk _ _ (eq_inv_con_of_con_eq p q r) _.

  -- Global Instance isequiv_moveL_pV
  --   {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
  -- : is_equiv (eq_con_inv_of_con_eq p q r).
  -- /-begin
  --   destruct p.
  --   apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
  -- end-/

  -- definition equiv_moveL_pV
  --   {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
  -- : q ⬝ p = r ≃ q = r ⬝ p⁻¹ :=
  --    equiv.mk _ _ (eq_con_inv_of_con_eq p q r) _.

  -- definition isequiv_moveL_1M {A : Type} {x y : A} (p q : x = y)
  -- : is_equiv (eq_of_con_inv_eq_idp p q).
  -- /-begin
  --   destruct q. apply isequiv_concat_l.
  -- end-/

  -- definition isequiv_moveL_M1 {A : Type} {x y : A} (p q : x = y)
  -- : is_equiv (eq_of_inv_con_eq_idp p q).
  -- /-begin
  --   destruct q. apply isequiv_concat_l.
  -- end-/

  -- definition isequiv_moveL_1V {A : Type} {x y : A} (p : x = y) (q : y = x)
  -- : is_equiv (eq_inv_of_con_eq_idp' p q).
  -- /-begin
  --   destruct q. apply isequiv_concat_l.
  -- end-/

  -- definition isequiv_moveL_V1 {A : Type} {x y : A} (p : x = y) (q : y = x)
  -- : is_equiv (eq_inv_of_con_eq_idp p q).
  -- /-begin
  --   destruct q. apply isequiv_concat_l.
  -- end-/

  -- definition isequiv_moveR_M1 {A : Type} {x y : A} (p q : x = y)
  -- : is_equiv (eq_of_idp_eq_inv_con p q).
  -- /-begin
  --   destruct p. apply isequiv_concat_r.
  -- end-/

  -- definition isequiv_moveR_1M {A : Type} {x y : A} (p q : x = y)
  -- : is_equiv (eq_of_idp_eq_con_inv p q).
  -- /-begin
  --   destruct p. apply isequiv_concat_r.
  -- end-/

  -- definition isequiv_moveR_1V {A : Type} {x y : A} (p : x = y) (q : y = x)
  -- : is_equiv (inv_eq_of_idp_eq_con p q).
  -- /-begin
  --   destruct p. apply isequiv_concat_r.
  -- end-/

  -- definition isequiv_moveR_V1 {A : Type} {x y : A} (p : x = y) (q : y = x)
  -- : is_equiv (inv_eq_of_idp_eq_con' p q).
  -- /-begin
  --   destruct p. apply isequiv_concat_r.
  -- end-/

  -- definition isequiv_moveR_transport_p [instance] {A : Type} (P : A → Type) {x y : A}
  --   (p : x = y) (u : P x) (v : P y)
  -- : is_equiv (tr_eq_of_eq_inv_tr P p u v).
  -- /-begin
  --   destruct p. apply isequiv_idmap.
  -- end-/

  -- definition equiv_moveR_transport_p {A : Type} (P : A → Type) {x y : A}
  --   (p : x = y) (u : P x) (v : P y)
  -- : u = transport P p⁻¹ v ≃ transport P p u = v :=
  --    equiv.mk _ _ (tr_eq_of_eq_inv_tr P p u v) _.

  -- definition isequiv_moveR_transport_V [instance] {A : Type} (P : A → Type) {x y : A}
  --   (p : y = x) (u : P x) (v : P y)
  -- : is_equiv (inv_tr_eq_of_eq_tr P p u v).
  -- /-begin
  --   destruct p. apply isequiv_idmap.
  -- end-/

  -- definition equiv_moveR_transport_V {A : Type} (P : A → Type) {x y : A}
  --   (p : y = x) (u : P x) (v : P y)
  -- : u = transport P p v ≃ transport P p⁻¹ u = v :=
  --    equiv.mk _ _ (inv_tr_eq_of_eq_tr P p u v) _.

  -- definition isequiv_moveL_transport_V [instance] {A : Type} (P : A → Type) {x y : A}
  --   (p : x = y) (u : P x) (v : P y)
  -- : is_equiv (eq_inv_tr_of_tr_eq P p u v).
  -- /-begin
  --   destruct p. apply isequiv_idmap.
  -- end-/

  -- definition equiv_moveL_transport_V {A : Type} (P : A → Type) {x y : A}
  --   (p : x = y) (u : P x) (v : P y)
  -- : transport P p u = v ≃ u = transport P p⁻¹ v :=
  --    equiv.mk _ _ (eq_inv_tr_of_tr_eq P p u v) _.

  -- definition isequiv_moveL_transport_p [instance] {A : Type} (P : A → Type) {x y : A}
  --   (p : y = x) (u : P x) (v : P y)
  -- : is_equiv (eq_tr_of_inv_tr_eq P p u v).
  -- /-begin
  --   destruct p. apply isequiv_idmap.
  -- end-/

  -- definition equiv_moveL_transport_p {A : Type} (P : A → Type) {x y : A}
  --   (p : y = x) (u : P x) (v : P y)
  -- : transport P p⁻¹ u = v ≃ u = transport P p v :=
  --    equiv.mk _ _ (eq_tr_of_inv_tr_eq P p u v) _.

  -- definition isequiv_moveR_equiv_M [instance] [H : is_equiv A B f] (x : A) (y : B)
  -- : is_equiv (@moveR_equiv_M A B f _ x y).
  -- /-begin
  --   unfold moveR_equiv_M.
  --   refine (@isequiv_compose _ _ (ap f) _ _ (λq, q ⬝ retr f y) _).
  -- end-/

  -- definition equiv_moveR_equiv_M [H : is_equiv A B f] (x : A) (y : B)
  --   : (x = f⁻¹ y) ≃ (f x = y) :=
  --      equiv.mk _ _ (@moveR_equiv_M A B f _ x y) _.

  -- definition isequiv_moveR_equiv_V [instance] [H : is_equiv A B f] (x : B) (y : A)
  -- : is_equiv (@moveR_equiv_V A B f _ x y).
  -- /-begin
  --   unfold moveR_equiv_V.
  --   refine (@isequiv_compose _ _ (ap f⁻¹) _ _ (λq, q ⬝ sect f y) _).
  -- end-/

  -- definition equiv_moveR_equiv_V [H : is_equiv A B f] (x : B) (y : A)
  --   : (x = f y) ≃ (f⁻¹ x = y) :=
  --      equiv.mk _ _ (@moveR_equiv_V A B f _ x y) _.

  -- definition isequiv_moveL_equiv_M [instance] [H : is_equiv A B f] (x : A) (y : B)
  -- : is_equiv (@moveL_equiv_M A B f _ x y).
  -- /-begin
  --   unfold moveL_equiv_M.
  --   refine (@isequiv_compose _ _ (ap f) _ _ (λq, (retr f y)⁻¹ ⬝ q) _).
  -- end-/

  -- definition equiv_moveL_equiv_M [H : is_equiv A B f] (x : A) (y : B)
  --   : (f⁻¹ y = x) ≃ (y = f x) :=
  --      equiv.mk _ _ (@moveL_equiv_M A B f _ x y) _.

  -- definition isequiv_moveL_equiv_V [instance] [H : is_equiv A B f] (x : B) (y : A)
  -- : is_equiv (@moveL_equiv_V A B f _ x y).
  -- /-begin
  --   unfold moveL_equiv_V.
  --   refine (@isequiv_compose _ _ (ap f⁻¹) _ _ (λq, (sect f y)⁻¹ ⬝ q) _).
  -- end-/

  -- definition equiv_moveL_equiv_V [H : is_equiv A B f] (x : B) (y : A)
  --   : (f y = x) ≃ (y = f⁻¹ x) :=
  --      equiv.mk _ _ (@moveL_equiv_V A B f _ x y) _.

  -- /- Dependent paths -/

  -- /- Usually, a dependent path over [p:x1=x2] in [P:A->Type] between [y1:P x1] and [y2:P x2] is a path [transport P p y1 = y2] in [P x2].  However, when [P] is a path space, these dependent paths have a more convenient description: rather than transporting the left side both forwards and backwards, we transport both sides of the equation forwards, forming a sort of "naturality square".

  --    We use the same naming scheme as for the transport lemmas. -/

  -- definition dpath_path_l {A : Type} {x1 x2 y : A}
  --   (p : x1 = x2) (q : x1 = y) (r : x2 = y)
  --   : q = p ⬝ r
  --   ≃
  --   transport (λx, x = y) p q = r.
  -- /-begin
  --   destruct p; simpl.
  --   exact (equiv_concat_r (idp_con r) q).
  -- end-/

  -- definition dpath_path_r {A : Type} {x y1 y2 : A}
  --   (p : y1 = y2) (q : x = y1) (r : x = y2)
  --   : q ⬝ p = r
  --   ≃
  --   transport (λy, x = y) p q = r.
  -- /-begin
  --   destruct p; simpl.
  --   exact (equiv_concat_l (con_idp q)⁻¹ r).
  -- end-/

  -- definition dpath_path_lr {A : Type} {x1 x2 : A}
  --   (p : x1 = x2) (q : x1 = x1) (r : x2 = x2)
  --   : q ⬝ p = p ⬝ r
  --   ≃
  --   transport (λx, x = x) p q = r.
  -- /-begin
  --   destruct p; simpl.
  --   refine (equiv_compose' (B := (q ⬝ 1 = r)) _ _).
  --   exact (equiv_concat_l (con_idp q)⁻¹ r).
  --   exact (equiv_concat_r (idp_con r) (q ⬝ 1)).
  -- end-/

  -- definition dpath_path_Fl {A B : Type} {f : A → B} {x1 x2 : A} {y : B}
  --   (p : x1 = x2) (q : f x1 = y) (r : f x2 = y)
  --   : q = ap f p ⬝ r
  --   ≃
  --   transport (λx, f x = y) p q = r.
  -- /-begin
  --   destruct p; simpl.
  --   exact (equiv_concat_r (idp_con r) q).
  -- end-/

  -- definition dpath_path_Fr {A B : Type} {g : A → B} {x : B} {y1 y2 : A}
  --   (p : y1 = y2) (q : x = g y1) (r : x = g y2)
  --   : q ⬝ ap g p = r
  --   ≃
  --   transport (λy, x = g y) p q = r.
  -- /-begin
  --   destruct p; simpl.
  --   exact (equiv_concat_l (con_idp q)⁻¹ r).
  -- end-/

  -- definition dpath_path_FlFr {A B : Type} {f g : A → B} {x1 x2 : A}
  --   (p : x1 = x2) (q : f x1 = g x1) (r : f x2 = g x2)
  --   : q ⬝ ap g p = ap f p ⬝ r
  --   ≃
  --   transport (λx, f x = g x) p q = r.
  -- /-begin
  --   destruct p; simpl.
  --   refine (equiv_compose' (B := (q ⬝ 1 = r)) _ _).
  --   exact (equiv_concat_l (con_idp q)⁻¹ r).
  --   exact (equiv_concat_r (idp_con r) (q ⬝ 1)).
  -- end-/

  -- definition dpath_path_FFlr {A B : Type} {f : A → B} {g : B → A}
  --   {x1 x2 : A} (p : x1 = x2) (q : g (f x1) = x1) (r : g (f x2) = x2)
  --   : q ⬝ p = ap g (ap f p) ⬝ r
  --   ≃
  --   transport (λx, g (f x) = x) p q = r.
  -- /-begin
  --   destruct p; simpl.
  --   refine (equiv_compose' (B := (q ⬝ 1 = r)) _ _).
  --   exact (equiv_concat_l (con_idp q)⁻¹ r).
  --   exact (equiv_concat_r (idp_con r) (q ⬝ 1)).
  -- end-/

  -- definition dpath_path_lFFr {A B : Type} {f : A → B} {g : B → A}
  --   {x1 x2 : A} (p : x1 = x2) (q : x1 = g (f x1)) (r : x2 = g (f x2))
  --   : q ⬝ ap g (ap f p) = p ⬝ r
  --   ≃
  --   transport (λx, x = g (f x)) p q = r.
  -- /-begin
  --   destruct p; simpl.
  --   refine (equiv_compose' (B := (q ⬝ 1 = r)) _ _).
  --   exact (equiv_concat_l (con_idp q)⁻¹ r).
  --   exact (equiv_concat_r (idp_con r) (q ⬝ 1)).
  -- end-/


  -- /- Universal mapping property -/

  -- definition isequiv_paths_ind [instance] [H : funext] {A : Type} (a : A)
  --   (P : Πx, (a = x) → Type)
  --   : is_equiv (paths_ind a P) | 0 :=
  --      isequiv_adjointify (paths_ind a P) (λf, f a 1) _ _.
  -- /-begin
  --   - intros f.
  --     apply path_forall; intros x.
  --     apply path_forall; intros p.
  --     destruct p; reflexivity.
  --   - intros u. reflexivity.
  -- end-/

  -- definition equiv_paths_ind [H : funext] {A : Type} (a : A)
  --   (P : Πx, (a = x) → Type)
  --   : P a 1 ≃ Πx p, P x p :=
  --      equiv.mk _ _ (paths_ind a P) _.

end path
