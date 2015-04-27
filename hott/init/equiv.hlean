/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: init.equiv
Author: Jeremy Avigad, Jakob von Raumer

Ported from Coq HoTT
-/

prelude
import .path .function
open eq function

/- Equivalences -/

-- This is our definition of equivalence. In the HoTT-book it's called
-- ihae (half-adjoint equivalence).
structure is_equiv [class] {A B : Type} (f : A → B) :=
mk' ::
  (inv : B → A)
  (right_inv : (f ∘ inv) ∼ id)
  (left_inv : (inv ∘ f) ∼ id)
  (adj : Πx, right_inv (f x) = ap f (left_inv x))

attribute is_equiv.inv [quasireducible]

-- A more bundled version of equivalence
structure equiv (A B : Type) :=
  (to_fun : A → B)
  (to_is_equiv : is_equiv to_fun)


namespace is_equiv
  /- Some instances and closure properties of equivalences -/
  postfix `⁻¹` := inv
  /- a second notation for the inverse, which is not overloaded -/
  postfix [parsing-only] `⁻¹ᵉ`:std.prec.max_plus := inv

  section
  variables {A B C : Type} (f : A → B) (g : B → C) {f' : A → B}

  -- The variant of mk' where f is explicit.
  protected abbreviation mk := @is_equiv.mk' A B f

  -- The identity function is an equivalence.
  definition is_equiv_id (A : Type) : (@is_equiv A A id) :=
  is_equiv.mk id id (λa, idp) (λa, idp) (λa, idp)

  -- The composition of two equivalences is, again, an equivalence.
  definition is_equiv_compose [Hf : is_equiv f] [Hg : is_equiv g] : is_equiv (g ∘ f) :=
    is_equiv.mk (g ∘ f) (f⁻¹ ∘ g⁻¹)
               (λc, ap g (right_inv f (g⁻¹ c)) ⬝ right_inv g c)
               (λa, ap (inv f) (left_inv g (f a)) ⬝ left_inv f a)
               (λa, (whisker_left _ (adj g (f a))) ⬝
                    (ap_con g _ _)⁻¹ ⬝
                    ap02 g ((ap_con_eq_con (right_inv f) (left_inv g (f a)))⁻¹ ⬝
                            (ap_compose (inv f) f _ ◾  adj f a) ⬝
                            (ap_con f _ _)⁻¹
                           ) ⬝
                    (ap_compose f g _)⁻¹
               )

  -- Any function equal to an equivalence is an equivlance as well.
  definition is_equiv_eq_closed [Hf : is_equiv f] (Heq : f = f') : (is_equiv f') :=
     eq.rec_on Heq Hf

  -- Any function pointwise equal to an equivalence is an equivalence as well.
  definition homotopy_closed [Hf : is_equiv f] (Hty : f ∼ f') : (is_equiv f') :=
    let sect' := (λ b, (Hty (inv f b))⁻¹ ⬝ right_inv f b) in
    let retr' := (λ a, (ap (inv f) (Hty a))⁻¹ ⬝ left_inv f a) in
    let adj' := (λ (a : A),
      let ff'a := Hty a in
      let invf := inv f in
      let secta := left_inv f a in
      let retrfa := right_inv f (f a) in
      let retrf'a := right_inv f (f' a) in
      have eq1 : _ = _,
        from calc ap f secta ⬝ ff'a
              = retrfa ⬝ ff'a                 : by rewrite adj
          ... = ap (f ∘ invf) ff'a ⬝ retrf'a  : by rewrite ap_con_eq_con
          ... = ap f (ap invf ff'a) ⬝ retrf'a : by rewrite ap_compose,
      have eq2 : _ = _,
        from calc retrf'a
              = (ap f (ap invf ff'a))⁻¹ ⬝ (ap f secta ⬝ ff'a)   : eq_inv_con_of_con_eq eq1⁻¹
          ... = (ap f (ap invf ff'a))⁻¹ ⬝ (ap f secta ⬝ Hty a) : ap_inv invf ff'a
          ... = (ap f (ap invf ff'a))⁻¹ ⬝ (Hty (invf (f a)) ⬝ ap f' secta) : by rewrite ap_con_eq_con_ap
          ... = ((ap f (ap invf ff'a))⁻¹ ⬝ Hty (invf (f a))) ⬝ ap f' secta : by rewrite con.assoc
          ... = (ap f (ap invf ff'a)⁻¹ ⬝ Hty (invf (f a))) ⬝ ap f' secta   : by rewrite ap_inv
          ... = (Hty (invf (f' a)) ⬝ ap f' (ap invf ff'a)⁻¹) ⬝ ap f' secta : by rewrite ap_con_eq_con_ap
          ... = (Hty (invf (f' a)) ⬝ (ap f' (ap invf ff'a))⁻¹) ⬝ ap f' secta : by rewrite ap_inv
          ... = Hty (invf (f' a)) ⬝ ((ap f' (ap invf ff'a))⁻¹ ⬝ ap f' secta) : by rewrite con.assoc,
      have eq3 : _ = _,
        from calc (Hty (invf (f' a)))⁻¹ ⬝ retrf'a
              = (ap f' (ap invf ff'a))⁻¹ ⬝ ap f' secta : inv_con_eq_of_eq_con eq2
          ... = (ap f' (ap invf ff'a)⁻¹) ⬝ ap f' secta : by rewrite ap_inv
          ... = ap f' ((ap invf ff'a)⁻¹ ⬝ secta)       : by rewrite ap_con,
    eq3) in
  is_equiv.mk f' (inv f) sect' retr' adj'
  end

  section
  parameters {A B : Type} (f : A → B) (g : B → A)
            (ret : f ∘ g ∼ id) (sec : g ∘ f ∼ id)

  private definition adjointify_sect' : g ∘ f ∼ id :=
    (λx, ap g (ap f (inverse (sec x))) ⬝ ap g (ret (f x)) ⬝ sec x)

  private definition adjointify_adj' : Π (x : A), ret (f x) = ap f (adjointify_sect' x) :=
    (λ (a : A),
      let fgretrfa := ap f (ap g (ret (f a))) in
      let fgfinvsect := ap f (ap g (ap f (sec a)⁻¹)) in
      let fgfa := f (g (f a)) in
      let retrfa := ret (f a) in
      have eq1 : ap f (sec a) = _,
        from calc ap f (sec a)
              = idp ⬝ ap f (sec a)                                     : by rewrite idp_con
          ... = (ret (f a) ⬝ (ret (f a))⁻¹) ⬝ ap f (sec a)             : by rewrite con.right_inv
          ... = ((ret fgfa)⁻¹ ⬝ ap (f ∘ g) (ret (f a))) ⬝ ap f (sec a) : by rewrite con_ap_eq_con
          ... = ((ret fgfa)⁻¹ ⬝ fgretrfa) ⬝ ap f (sec a)               : by rewrite ap_compose
          ... = (ret fgfa)⁻¹ ⬝ (fgretrfa ⬝ ap f (sec a))               : by rewrite con.assoc,
      have eq2 : ap f (sec a) ⬝ idp = (ret fgfa)⁻¹ ⬝ (fgretrfa ⬝ ap f (sec a)),
        from !con_idp ⬝ eq1,
      have eq3 : idp = _,
        from calc idp
              = (ap f (sec a))⁻¹ ⬝ ((ret fgfa)⁻¹ ⬝ (fgretrfa ⬝ ap f (sec a))) : eq_inv_con_of_con_eq eq2
          ... = ((ap f (sec a))⁻¹ ⬝ (ret fgfa)⁻¹) ⬝ (fgretrfa ⬝ ap f (sec a)) : by rewrite con.assoc'
          ... = (ap f (sec a)⁻¹ ⬝ (ret fgfa)⁻¹) ⬝ (fgretrfa ⬝ ap f (sec a))   : by rewrite ap_inv
          ... = ((ap f (sec a)⁻¹ ⬝ (ret fgfa)⁻¹) ⬝ fgretrfa) ⬝ ap f (sec a)   : by rewrite con.assoc'
          ... = ((retrfa⁻¹ ⬝ ap (f ∘ g) (ap f (sec a)⁻¹)) ⬝ fgretrfa) ⬝ ap f (sec a) : by rewrite con_ap_eq_con
          ... = ((retrfa⁻¹ ⬝ fgfinvsect) ⬝ fgretrfa) ⬝ ap f (sec a)           : by rewrite ap_compose
          ... = (retrfa⁻¹ ⬝ (fgfinvsect ⬝ fgretrfa)) ⬝ ap f (sec a)           : by rewrite con.assoc'
          ... = retrfa⁻¹ ⬝ ap f (ap g (ap f (sec a)⁻¹) ⬝ ap g (ret (f a))) ⬝ ap f (sec a)   : by rewrite ap_con
          ... = retrfa⁻¹ ⬝ (ap f (ap g (ap f (sec a)⁻¹) ⬝ ap g (ret (f a))) ⬝ ap f (sec a)) : by rewrite con.assoc'
          ... = retrfa⁻¹ ⬝ ap f ((ap g (ap f (sec a)⁻¹) ⬝ ap g (ret (f a))) ⬝ sec a)        : by rewrite -ap_con,
      have eq4 : ret (f a) = ap f ((ap g (ap f (sec a)⁻¹) ⬝ ap g (ret (f a))) ⬝ sec a),
        from eq_of_idp_eq_inv_con eq3,
      eq4)

  definition adjointify : is_equiv f := is_equiv.mk f g ret adjointify_sect' adjointify_adj'

  end

  section
  variables {A B C : Type} (f : A → B) {f' : A → B} [Hf : is_equiv f] (g : B → C)
  include Hf

  --The inverse of an equivalence is, again, an equivalence.
  definition is_equiv_inv [instance] : (is_equiv f⁻¹) :=
  adjointify f⁻¹ f (left_inv f) (right_inv f)

  definition cancel_right (g : B → C) [Hgf : is_equiv (g ∘ f)] : (is_equiv g) :=
  have Hfinv [visible] : is_equiv f⁻¹, from is_equiv_inv f,
  @homotopy_closed _ _ _ _ (is_equiv_compose f⁻¹ (g ∘ f)) (λb, ap g (@right_inv _ _ f _ b))

  definition cancel_left (g : C → A) [Hgf : is_equiv (f ∘ g)] : (is_equiv g) :=
  have Hfinv [visible] : is_equiv f⁻¹, from is_equiv_inv f,
  @homotopy_closed _ _ _ _ (is_equiv_compose (f ∘ g) f⁻¹) (λa, left_inv f (g a))

  definition is_equiv_ap [instance] (x y : A) : is_equiv (ap f) :=
    adjointify (ap f)
      (λq, (inverse (left_inv f x)) ⬝ ap f⁻¹ q ⬝ left_inv f y)
      (λq, !ap_con
        ⬝ whisker_right !ap_con _
        ⬝ ((!ap_inv ⬝ inverse2 (adj f _)⁻¹)
          ◾ (inverse (ap_compose f⁻¹ f _))
          ◾ (adj f _)⁻¹)
        ⬝ con_ap_con_eq_con_con (right_inv f) _ _
        ⬝ whisker_right !con.left_inv _
        ⬝ !idp_con)
      (λp, whisker_right (whisker_left _ (ap_compose f f⁻¹ _)⁻¹) _
        ⬝ con_ap_con_eq_con_con (left_inv f) _ _
        ⬝ whisker_right !con.left_inv _
        ⬝ !idp_con)

  -- The function equiv_rect says that given an equivalence f : A → B,
  -- and a hypothesis from B, one may always assume that the hypothesis
  -- is in the image of e.

  -- In fibrational terms, if we have a fibration over B which has a section
  -- once pulled back along an equivalence f : A → B, then it has a section
  -- over all of B.

  definition equiv_rect (P : B → Type) :
      (Πx, P (f x)) → (Πy, P y) :=
    (λg y, eq.transport _ (right_inv f y) (g (f⁻¹ y)))

  definition equiv_rect_comp (P : B → Type)
      (df : Π (x : A), P (f x)) (x : A) : equiv_rect f P df (f x) = df x :=
    calc equiv_rect f P df (f x)
          = transport P (right_inv f (f x)) (df (f⁻¹ (f x)))       : by esimp
      ... = transport P (eq.ap f (left_inv f x)) (df (f⁻¹ (f x))) : by rewrite adj
      ... = transport (P ∘ f) (left_inv f x) (df (f⁻¹ (f x)))     : by rewrite -transport_compose
      ... = df x                                              : by rewrite (apd df (left_inv f x))

  end

  section
  variables {A B : Type} {f : A → B} [Hf : is_equiv f] {a : A} {b : B}
  include Hf

  --Rewrite rules
  definition eq_of_eq_inv (p : a = f⁻¹ b) : f a = b :=
  ap f p ⬝ right_inv f b

  definition eq_of_inv_eq (p : f⁻¹ b = a) : b = f a :=
  (eq_of_eq_inv p⁻¹)⁻¹

  definition inv_eq_of_eq (p : b = f a) : f⁻¹ b = a :=
  ap f⁻¹ p ⬝ left_inv f a

  definition eq_inv_of_eq (p : f a = b) : a = f⁻¹ b :=
  (inv_eq_of_eq p⁻¹)⁻¹

  end

  --Transporting is an equivalence
  definition is_equiv_tr [instance] {A : Type} (P : A → Type) {x y : A} (p : x = y) : (is_equiv (transport P p)) :=
    is_equiv.mk _ (transport P p⁻¹) (tr_inv_tr P p) (inv_tr_tr P p) (tr_inv_tr_lemma P p)


end is_equiv

open is_equiv
namespace equiv
  namespace ops
    attribute to_fun [coercion]
  end ops
  open equiv.ops
  attribute to_is_equiv [instance]

  infix `≃`:25 := equiv

  variables {A B C : Type}

  protected definition MK [reducible] (f : A → B) (g : B → A)
    (right_inv : f ∘ g ∼ id) (left_inv : g ∘ f ∼ id) : A ≃ B :=
  equiv.mk f (adjointify f g right_inv left_inv)

  definition to_inv [reducible] (f : A ≃ B) : B → A :=
  f⁻¹

  protected definition refl : A ≃ A :=
  equiv.mk id !is_equiv_id

  protected definition symm (f : A ≃ B) : B ≃ A :=
  equiv.mk f⁻¹ !is_equiv_inv

  protected definition trans (f : A ≃ B) (g: B ≃ C) : A ≃ C :=
  equiv.mk (g ∘ f) !is_equiv_compose

  definition equiv_of_eq_fn_of_equiv (f : A ≃ B) (f' : A → B) (Heq : f = f') : A ≃ B :=
  equiv.mk f' (is_equiv_eq_closed f Heq)

  definition eq_equiv_fn_eq (f : A → B) [H : is_equiv f] (a b : A) : (a = b) ≃ (f a = f b) :=
  equiv.mk (ap f) !is_equiv_ap

  definition eq_equiv_fn_eq_of_equiv (f : A ≃ B) (a b : A) : (a = b) ≃ (f a = f b) :=
  equiv.mk (ap f) !is_equiv_ap

  definition equiv_ap (P : A → Type) {a b : A} (p : a = b) : (P a) ≃ (P b) :=
  equiv.mk (transport P p) !is_equiv_tr

  --we need this theorem for the funext_of_ua proof
  theorem inv_eq {A B : Type} (eqf eqg : A ≃ B) (p : eqf = eqg) : (to_fun eqf)⁻¹ = (to_fun eqg)⁻¹ :=
  eq.rec_on p idp

  -- calc enviroment
  -- Note: Calculating with substitutions needs univalence
  definition equiv_of_equiv_of_eq {A B C : Type} (p : A = B) (q : B ≃ C) : A ≃ C := p⁻¹ ▹ q
  definition equiv_of_eq_of_equiv {A B C : Type} (p : A ≃ B) (q : B = C) : A ≃ C := q   ▹ p

  calc_trans equiv.trans
  calc_refl equiv.refl
  calc_symm equiv.symm
  calc_trans equiv_of_equiv_of_eq
  calc_trans equiv_of_eq_of_equiv

end equiv
