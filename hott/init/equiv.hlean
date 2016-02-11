/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Jakob von Raumer, Floris van Doorn

Ported from Coq HoTT
-/

prelude
import .path .function
open eq function lift

/- Equivalences -/

-- This is our definition of equivalence. In the HoTT-book it's called
-- ihae (half-adjoint equivalence).
structure is_equiv [class] {A B : Type} (f : A → B) :=
mk' ::
  (inv : B → A)
  (right_inv : Πb, f (inv b) = b)
  (left_inv : Πa, inv (f a) = a)
  (adj : Πx, right_inv (f x) = ap f (left_inv x))

attribute is_equiv.inv [quasireducible]

-- A more bundled version of equivalence
structure equiv (A B : Type) :=
  (to_fun : A → B)
  (to_is_equiv : is_equiv to_fun)

namespace is_equiv
  /- Some instances and closure properties of equivalences -/
  postfix ⁻¹ := inv
  /- a second notation for the inverse, which is not overloaded -/
  postfix [parsing_only] `⁻¹ᶠ`:std.prec.max_plus := inv

  section
  variables {A B C : Type} (f : A → B) (g : B → C) {f' : A → B}

  -- The variant of mk' where f is explicit.
  protected abbreviation mk [constructor] := @is_equiv.mk' A B f

  -- The identity function is an equivalence.
  definition is_equiv_id [instance] [constructor] (A : Type) : (is_equiv (id : A → A)) :=
  is_equiv.mk id id (λa, idp) (λa, idp) (λa, idp)

  -- The composition of two equivalences is, again, an equivalence.
  definition is_equiv_compose [constructor] [Hf : is_equiv f] [Hg : is_equiv g]
    : is_equiv (g ∘ f) :=
  is_equiv.mk (g ∘ f) (f⁻¹ ∘ g⁻¹)
             abstract (λc, ap g (right_inv f (g⁻¹ c)) ⬝ right_inv g c) end
             abstract (λa, ap (inv f) (left_inv g (f a)) ⬝ left_inv f a) end
             abstract (λa, (whisker_left _ (adj g (f a))) ⬝
                  (ap_con g _ _)⁻¹ ⬝
                  ap02 g ((ap_con_eq_con (right_inv f) (left_inv g (f a)))⁻¹ ⬝
                          (ap_compose f (inv f) _ ◾  adj f a) ⬝
                          (ap_con f _ _)⁻¹
                         ) ⬝
                  (ap_compose g f _)⁻¹) end

  -- Any function equal to an equivalence is an equivlance as well.
  variable {f}
  definition is_equiv_eq_closed [Hf : is_equiv f] (Heq : f = f') : is_equiv f' :=
  eq.rec_on Heq Hf
  end

  section
  parameters {A B : Type} (f : A → B) (g : B → A)
            (ret : Πb, f (g b) = b) (sec : Πa, g (f a) = a)

  private abbreviation adjointify_left_inv' (a : A) : g (f a) = a :=
  ap g (ap f (inverse (sec a))) ⬝ ap g (ret (f a)) ⬝ sec a

  private theorem adjointify_adj' (a : A) : ret (f a) = ap f (adjointify_left_inv' a) :=
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
  eq4

  definition adjointify [constructor] : is_equiv f :=
  is_equiv.mk f g ret abstract adjointify_left_inv' end adjointify_adj'
  end

  -- Any function pointwise equal to an equivalence is an equivalence as well.
  definition homotopy_closed [constructor] {A B : Type} (f : A → B) {f' : A → B} [Hf : is_equiv f]
    (Hty : f ~ f') : is_equiv f' :=
  adjointify f'
             (inv f)
             (λ b, (Hty (inv f b))⁻¹ ⬝ right_inv f b)
             (λ a, (ap (inv f) (Hty a))⁻¹ ⬝ left_inv f a)

  definition inv_homotopy_closed [constructor] {A B : Type} {f : A → B} {f' : B → A}
    [Hf : is_equiv f] (Hty : f⁻¹ ~ f') : is_equiv f :=
  adjointify f
             f'
             (λ b, ap f !Hty⁻¹ ⬝ right_inv f b)
             (λ a, !Hty⁻¹ ⬝ left_inv f a)

  definition is_equiv_up [instance] [constructor] (A : Type)
    : is_equiv (up : A → lift A) :=
  adjointify up down (λa, by induction a;reflexivity) (λa, idp)

  section
  variables {A B C : Type} (f : A → B) {f' : A → B} [Hf : is_equiv f] (g : B → C)
  include Hf

  --The inverse of an equivalence is, again, an equivalence.
  definition is_equiv_inv [instance] [constructor] : is_equiv f⁻¹ :=
  adjointify f⁻¹ f (left_inv f) (right_inv f)

  definition cancel_right (g : B → C) [Hgf : is_equiv (g ∘ f)] : (is_equiv g) :=
  have Hfinv [visible] : is_equiv f⁻¹, from is_equiv_inv f,
  @homotopy_closed _ _ _ _ (is_equiv_compose f⁻¹ (g ∘ f)) (λb, ap g (@right_inv _ _ f _ b))

  definition cancel_left (g : C → A) [Hgf : is_equiv (f ∘ g)] : (is_equiv g) :=
  have Hfinv [visible] : is_equiv f⁻¹, from is_equiv_inv f,
  @homotopy_closed _ _ _ _ (is_equiv_compose (f ∘ g) f⁻¹) (λa, left_inv f (g a))

  definition eq_of_fn_eq_fn' {x y : A} (q : f x = f y) : x = y :=
  (left_inv f x)⁻¹ ⬝ ap f⁻¹ q ⬝ left_inv f y

  theorem ap_eq_of_fn_eq_fn' {x y : A} (q : f x = f y) : ap f (eq_of_fn_eq_fn' f q) = q :=
  begin
    rewrite [↑eq_of_fn_eq_fn',+ap_con,ap_inv,-+adj,-ap_compose,con.assoc,
             ap_con_eq_con_ap (right_inv f) q,inv_con_cancel_left,ap_id],
  end

  definition is_equiv_ap [instance] (x y : A) : is_equiv (ap f : x = y → f x = f y) :=
    adjointify
      (ap f)
      (eq_of_fn_eq_fn' f)
      (λq, !ap_con
        ⬝ whisker_right !ap_con _
        ⬝ ((!ap_inv ⬝ inverse2 (adj f _)⁻¹)
          ◾ (inverse (ap_compose f f⁻¹ _))
          ◾ (adj f _)⁻¹)
        ⬝ con_ap_con_eq_con_con (right_inv f) _ _
        ⬝ whisker_right !con.left_inv _
        ⬝ !idp_con)
      (λp, whisker_right (whisker_left _ (ap_compose f⁻¹ f _)⁻¹) _
        ⬝ con_ap_con_eq_con_con (left_inv f) _ _
        ⬝ whisker_right !con.left_inv _
        ⬝ !idp_con)

  -- The function equiv_rect says that given an equivalence f : A → B,
  -- and a hypothesis from B, one may always assume that the hypothesis
  -- is in the image of e.

  -- In fibrational terms, if we have a fibration over B which has a section
  -- once pulled back along an equivalence f : A → B, then it has a section
  -- over all of B.

  definition is_equiv_rect (P : B → Type) (g : Πa, P (f a)) (b : B) : P b :=
  right_inv f b ▸ g (f⁻¹ b)

  definition is_equiv_rect' (P : A → B → Type) (g : Πb, P (f⁻¹ b) b) (a : A) : P a (f a) :=
  left_inv f a ▸ g (f a)

  definition is_equiv_rect_comp (P : B → Type)
      (df : Π (x : A), P (f x)) (x : A) : is_equiv_rect f P df (f x) = df x :=
    calc
      is_equiv_rect f P df (f x)
            = right_inv f (f x) ▸ df (f⁻¹ (f x))   : by esimp
        ... = ap f (left_inv f x) ▸ df (f⁻¹ (f x)) : by rewrite -adj
        ... = left_inv f x ▸ df (f⁻¹ (f x))        : by rewrite -tr_compose
        ... = df x                                 : by rewrite (apd df (left_inv f x))

  theorem adj_inv (b : B) : left_inv f (f⁻¹ b) = ap f⁻¹ (right_inv f b) :=
  is_equiv_rect f _
    (λa,
      eq.cancel_right (whisker_left _ !ap_id⁻¹ ⬝ (ap_con_eq_con_ap (left_inv f) (left_inv f a))⁻¹) ⬝
      !ap_compose ⬝ ap02 f⁻¹ (adj f a)⁻¹)
    b

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
  definition is_equiv_tr [constructor] {A : Type} (P : A → Type) {x y : A}
    (p : x = y) : (is_equiv (transport P p)) :=
  is_equiv.mk _ (transport P p⁻¹) (tr_inv_tr p) (inv_tr_tr p) (tr_inv_tr_lemma p)

  section
  variables {A : Type} {B C : A → Type} (f : Π{a}, B a → C a) [H : Πa, is_equiv (@f a)]
    {g : A → A} (h : Π{a}, B a → B (g a)) (h' : Π{a}, C a → C (g a))
  include H
  definition inv_commute' (p : Π⦃a : A⦄ (b : B a), f (h b) = h' (f b)) {a : A} (c : C a) :
    f⁻¹ (h' c) = h (f⁻¹ c) :=
  eq_of_fn_eq_fn' f (right_inv f (h' c) ⬝ ap h' (right_inv f c)⁻¹ ⬝ (p (f⁻¹ c))⁻¹)

  definition fun_commute_of_inv_commute' (p : Π⦃a : A⦄ (c : C a), f⁻¹ (h' c) = h (f⁻¹ c))
    {a : A} (b : B a) : f (h b) = h' (f b) :=
  eq_of_fn_eq_fn' f⁻¹ (left_inv f (h b) ⬝ ap h (left_inv f b)⁻¹ ⬝ (p (f b))⁻¹)

  definition ap_inv_commute' (p : Π⦃a : A⦄ (b : B a), f (h b) = h' (f b)) {a : A} (c : C a) :
    ap f (inv_commute' @f @h @h' p c)
      = right_inv f (h' c) ⬝ ap h' (right_inv f c)⁻¹ ⬝ (p (f⁻¹ c))⁻¹ :=
  !ap_eq_of_fn_eq_fn'

  end

end is_equiv
open is_equiv

namespace eq
  local attribute is_equiv_tr [instance]

  definition tr_inv_fn {A : Type} {B : A → Type} {a a' : A} (p : a = a') :
    transport B p⁻¹ = (transport B p)⁻¹ := idp
  definition tr_inv {A : Type} {B : A → Type} {a a' : A} (p : a = a') (b : B a') :
    p⁻¹ ▸ b = (transport B p)⁻¹ b := idp

  definition cast_inv_fn {A B : Type} (p : A = B) : cast p⁻¹ = (cast p)⁻¹ := idp
  definition cast_inv {A B : Type} (p : A = B) (b : B) : cast p⁻¹ b = (cast p)⁻¹ b := idp
end eq

namespace equiv
  namespace ops
    attribute to_fun [coercion]
  end ops
  open equiv.ops
  attribute to_is_equiv [instance]

  infix ` ≃ `:25 := equiv

  section
  variables {A B C : Type}

  protected definition MK [reducible] [constructor] (f : A → B) (g : B → A)
    (right_inv : Πb, f (g b) = b) (left_inv : Πa, g (f a) = a) : A ≃ B :=
  equiv.mk f (adjointify f g right_inv left_inv)

  definition to_inv [reducible] [unfold 3] (f : A ≃ B) : B → A := f⁻¹
  definition to_right_inv [reducible] [unfold 3] (f : A ≃ B) (b : B) : f (f⁻¹ b) = b :=
  right_inv f b
  definition to_left_inv [reducible] [unfold 3] (f : A ≃ B) (a : A) : f⁻¹ (f a) = a :=
  left_inv f a

  protected definition refl [refl] [constructor] : A ≃ A :=
  equiv.mk id !is_equiv_id

  protected definition symm [symm] (f : A ≃ B) : B ≃ A :=
  equiv.mk f⁻¹ !is_equiv_inv

  protected definition trans [trans] (f : A ≃ B) (g : B ≃ C) : A ≃ C :=
  equiv.mk (g ∘ f) !is_equiv_compose

  infixl ` ⬝e `:75 := equiv.trans
  postfix [parsing_only] `⁻¹ᵉ`:(max + 1) := equiv.symm
    -- notation for inverse which is not overloaded
  abbreviation erfl [constructor] := @equiv.refl

  definition to_inv_trans [reducible] [unfold_full] (f : A ≃ B) (g : B ≃ C)
    : to_inv (f ⬝e g) = to_fun (g⁻¹ᵉ ⬝e f⁻¹ᵉ) :=
  idp

  definition equiv_change_fun [constructor] (f : A ≃ B) {f' : A → B} (Heq : f ~ f') : A ≃ B :=
  equiv.mk f' (is_equiv.homotopy_closed f Heq)

  definition equiv_change_inv [constructor] (f : A ≃ B) {f' : B → A} (Heq : f⁻¹ ~ f')
    : A ≃ B :=
  equiv.mk f (inv_homotopy_closed Heq)

  --rename: eq_equiv_fn_eq_of_is_equiv
  definition eq_equiv_fn_eq [constructor] (f : A → B) [H : is_equiv f] (a b : A) : (a = b) ≃ (f a = f b) :=
  equiv.mk (ap f) !is_equiv_ap

  --rename: eq_equiv_fn_eq
  definition eq_equiv_fn_eq_of_equiv [constructor] (f : A ≃ B) (a b : A) : (a = b) ≃ (f a = f b) :=
  equiv.mk (ap f) !is_equiv_ap

  definition equiv_ap [constructor] (P : A → Type) {a b : A} (p : a = b) : (P a) ≃ (P b) :=
  equiv.mk (transport P p) !is_equiv_tr

  definition eq_of_fn_eq_fn (f : A ≃ B) {x y : A} (q : f x = f y) : x = y :=
  (left_inv f x)⁻¹ ⬝ ap f⁻¹ q ⬝ left_inv f y

  definition eq_of_fn_eq_fn_inv (f : A ≃ B) {x y : B} (q : f⁻¹ x = f⁻¹ y) : x = y :=
  (right_inv f x)⁻¹ ⬝ ap f q ⬝ right_inv f y

  --we need this theorem for the funext_of_ua proof
  theorem inv_eq {A B : Type} (eqf eqg : A ≃ B) (p : eqf = eqg) : (to_fun eqf)⁻¹ = (to_fun eqg)⁻¹ :=
  eq.rec_on p idp

  definition equiv_of_equiv_of_eq [trans] {A B C : Type} (p : A = B) (q : B ≃ C) : A ≃ C := p⁻¹ ▸ q
  definition equiv_of_eq_of_equiv [trans] {A B C : Type} (p : A ≃ B) (q : B = C) : A ≃ C := q   ▸ p

  definition equiv_lift [constructor] (A : Type) : A ≃ lift A := equiv.mk up _

  definition equiv_rect (f : A ≃ B) (P : B → Type) (g : Πa, P (f a)) (b : B) : P b :=
  right_inv f b ▸ g (f⁻¹ b)

  definition equiv_rect' (f : A ≃ B) (P : A → B → Type) (g : Πb, P (f⁻¹ b) b) (a : A) : P a (f a) :=
  left_inv f a ▸ g (f a)

  definition equiv_rect_comp (f : A ≃ B) (P : B → Type)
      (df : Π (x : A), P (f x)) (x : A) : equiv_rect f P df (f x) = df x :=
    calc
      equiv_rect f P df (f x)
            = right_inv f (f x) ▸ df (f⁻¹ (f x))   : by esimp
        ... = ap f (left_inv f x) ▸ df (f⁻¹ (f x)) : by rewrite -adj
        ... = left_inv f x ▸ df (f⁻¹ (f x))        : by rewrite -tr_compose
        ... = df x                                 : by rewrite (apd df (left_inv f x))
  end

  section
  variables {A : Type} {B C : A → Type} (f : Π{a}, B a ≃ C a)
            {g : A → A} (h : Π{a}, B a → B (g a)) (h' : Π{a}, C a → C (g a))

  definition inv_commute (p : Π⦃a : A⦄ (b : B a), f (h b) = h' (f b)) {a : A} (c : C a) :
    f⁻¹ (h' c) = h (f⁻¹ c) :=
  inv_commute' @f @h @h' p c

  definition fun_commute_of_inv_commute (p : Π⦃a : A⦄ (c : C a), f⁻¹ (h' c) = h (f⁻¹ c))
    {a : A} (b : B a) : f (h b) = h' (f b) :=
  fun_commute_of_inv_commute' @f @h @h' p b
  end


  namespace ops
    postfix ⁻¹ := equiv.symm -- overloaded notation for inverse
  end ops
end equiv

open equiv equiv.ops
namespace is_equiv

  definition is_equiv_of_equiv_of_homotopy [constructor] {A B : Type} (f : A ≃ B)
    {f' : A → B} (Hty : f ~ f') : is_equiv f' :=
  homotopy_closed f Hty

end is_equiv

export [unfold] equiv
export [unfold] is_equiv
