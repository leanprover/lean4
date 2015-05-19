/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: types.equiv
Author: Floris van Doorn

Ported from Coq HoTT
Theorems about the types equiv and is_equiv
-/

import .fiber .arrow arity .hprop_trunc

open eq is_trunc sigma sigma.ops arrow pi fiber function equiv

namespace is_equiv
  variables {A B : Type} (f : A → B) [H : is_equiv f]
  include H
  /- is_equiv f is a mere proposition -/
  definition is_contr_fiber_of_is_equiv [instance] (b : B) : is_contr (fiber f b) :=
  is_contr.mk
    (fiber.mk (f⁻¹ b) (right_inv f b))
    (λz, fiber.rec_on z (λa p, fiber_eq ((ap f⁻¹ p)⁻¹ ⬝ left_inv f a) (calc
      right_inv f b = (ap (f ∘ f⁻¹) p)⁻¹ ⬝ ((ap (f ∘ f⁻¹) p) ⬝ right_inv f b) : by rewrite inv_con_cancel_left
           ... = (ap (f ∘ f⁻¹) p)⁻¹ ⬝ (right_inv f (f a) ⬝ p)       : by rewrite ap_con_eq_con
           ... = (ap (f ∘ f⁻¹) p)⁻¹ ⬝ (ap f (left_inv f a) ⬝ p)    : by rewrite adj
           ... = (ap (f ∘ f⁻¹) p)⁻¹ ⬝ ap f (left_inv f a) ⬝ p      : by rewrite con.assoc
           ... = (ap f (ap f⁻¹ p))⁻¹ ⬝ ap f (left_inv f a) ⬝ p     : by rewrite ap_compose
           ... = ap f (ap f⁻¹ p)⁻¹ ⬝ ap f (left_inv f a) ⬝ p       : by rewrite ap_inv
           ... = ap f ((ap f⁻¹ p)⁻¹ ⬝ left_inv f a) ⬝ p            : by rewrite ap_con)))

  definition is_contr_right_inverse : is_contr (Σ(g : B → A), f ∘ g ∼ id) :=
  begin
    fapply is_trunc_equiv_closed,
      {apply sigma_equiv_sigma_id, intro g, apply eq_equiv_homotopy},
    fapply is_trunc_equiv_closed,
      {apply fiber.sigma_char},
    fapply is_contr_fiber_of_is_equiv,
    apply (to_is_equiv (arrow_equiv_arrow_right (equiv.mk f H))),
  end

  definition is_contr_right_coherence (u : Σ(g : B → A), f ∘ g ∼ id)
    : is_contr (Σ(η : u.1 ∘ f ∼ id), Π(a : A), u.2 (f a) = ap f (η a)) :=
  begin
    fapply is_trunc_equiv_closed,
      {apply equiv.symm, apply sigma_pi_equiv_pi_sigma},
    fapply is_trunc_equiv_closed,
      {apply pi_equiv_pi_id, intro a,
        apply (fiber_eq_equiv (fiber.mk (u.1 (f a)) (u.2 (f a))) (fiber.mk a idp))},
  end

  omit H

  protected definition sigma_char : (is_equiv f) ≃
  (Σ(g : B → A) (ε : f ∘ g ∼ id) (η : g ∘ f ∼ id), Π(a : A), ε (f a) = ap f (η a)) :=
  equiv.MK (λH, ⟨inv f, right_inv f, left_inv f, adj f⟩)
           (λp, is_equiv.mk f p.1 p.2.1 p.2.2.1 p.2.2.2)
           (λp, begin
                  cases p with p1 p2,
                  cases p2 with p21 p22,
                  cases p22 with p221 p222,
                  apply idp
                end)
           (λH, is_equiv.rec_on H (λH1 H2 H3 H4, idp))

  protected definition sigma_char' : (is_equiv f) ≃
  (Σ(u : Σ(g : B → A), f ∘ g ∼ id), Σ(η : u.1 ∘ f ∼ id), Π(a : A), u.2 (f a) = ap f (η a)) :=
  calc
    (is_equiv f) ≃
      (Σ(g : B → A) (ε : f ∘ g ∼ id) (η : g ∘ f ∼ id), Π(a : A), ε (f a) = ap f (η a))
          : is_equiv.sigma_char
    ... ≃ (Σ(u : Σ(g : B → A), f ∘ g ∼ id), Σ(η : u.1 ∘ f ∼ id), Π(a : A), u.2 (f a) = ap f (η a))
          : {sigma_assoc_equiv (λu, Σ(η : u.1 ∘ f ∼ id), Π(a : A), u.2 (f a) = ap f (η a))}

  local attribute is_contr_right_inverse [instance] [priority 1600]
  local attribute is_contr_right_coherence [instance] [priority 1600]

  theorem is_hprop_is_equiv [instance] : is_hprop (is_equiv f) :=
  is_hprop_of_imp_is_contr (λ(H : is_equiv f), is_trunc_equiv_closed -2 (equiv.symm !is_equiv.sigma_char'))

  definition inv_eq_inv {A B : Type} {f f' : A → B} {Hf : is_equiv f} {Hf' : is_equiv f'}
    (p : f = f') : f⁻¹ = f'⁻¹ :=
  apd011 inv p !is_hprop.elim

  /- contractible fibers -/
  definition is_contr_fun [reducible] (f : A → B) := Π(b : B), is_contr (fiber f b)

  definition is_contr_fun_of_is_equiv [H : is_equiv f] : is_contr_fun f :=
  is_contr_fiber_of_is_equiv f

  definition is_hprop_is_contr_fun (f : A → B) : is_hprop (is_contr_fun f) := _

  /-
    we cannot make the next theorem an instance, because it loops together with
    is_contr_fiber_of_is_equiv
  -/
  definition is_equiv_of_is_contr_fun [H : is_contr_fun f] : is_equiv f :=
  adjointify _ (λb, point (center (fiber f b)))
               (λb, point_eq (center (fiber f b)))
               (λa, ap point (center_eq (fiber.mk a idp)))

  definition is_equiv_of_imp_is_equiv (H : B → is_equiv f) : is_equiv f :=
  @is_equiv_of_is_contr_fun _ _ f (λb, @is_contr_fiber_of_is_equiv _ _ _ (H b) _)

  definition is_equiv_equiv_is_contr_fun : is_equiv f ≃ is_contr_fun f :=
  equiv_of_is_hprop _ (λH, !is_equiv_of_is_contr_fun)

end is_equiv

namespace equiv
  open is_equiv
  variables {A B : Type}

  definition equiv_mk_eq {f f' : A → B} [H : is_equiv f] [H' : is_equiv f'] (p : f = f')
      : equiv.mk f H = equiv.mk f' H' :=
  apd011 equiv.mk p !is_hprop.elim

  definition equiv_eq {f f' : A ≃ B} (p : to_fun f = to_fun f') : f = f' :=
  by (cases f; cases f'; apply (equiv_mk_eq p))

  protected definition equiv.sigma_char (A B : Type) : (A ≃ B) ≃ Σ(f : A → B), is_equiv f :=
  begin
    fapply equiv.MK,
      {intro F, exact ⟨to_fun F, to_is_equiv F⟩},
      {intro p, cases p with f H, exact (equiv.mk f H)},
      {intro p, cases p, exact idp},
      {intro F, cases F, exact idp},
  end

  definition equiv_eq_char (f f' : A ≃ B) : (f = f') ≃ (to_fun f = to_fun f') :=
  calc
    (f = f') ≃ (to_fun !equiv.sigma_char f = to_fun !equiv.sigma_char f')
                : eq_equiv_fn_eq (to_fun !equiv.sigma_char)
         ... ≃ ((to_fun !equiv.sigma_char f).1 = (to_fun !equiv.sigma_char f').1 ) : equiv_subtype
         ... ≃ (to_fun f = to_fun f') : equiv.refl

  definition is_equiv_ap_to_fun (f f' : A ≃ B)
    : is_equiv (ap to_fun : f = f' → to_fun f = to_fun f') :=
  begin
    fapply adjointify,
      {intro p, cases f with f H, cases f' with f' H', cases p, apply ap (mk f'), apply is_hprop.elim},
      {intro p, cases f with f H, cases f' with f' H', cases p,
        apply @concat _ _ (ap to_fun (ap (equiv.mk f') (is_hprop.elim H H'))), {apply idp},
        generalize is_hprop.elim H H', intro q, cases q, apply idp},
      {intro p, cases p, cases f with f H, apply ap (ap (equiv.mk f)), apply is_hset.elim}
  end

end equiv
