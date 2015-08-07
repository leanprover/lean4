/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about lift
-/

import ..function
open eq equiv equiv.ops is_equiv is_trunc

namespace lift

  universe variables u v
  variables {A : Type.{u}} (z z' : lift.{u v} A)

  protected definition eta : up (down z) = z :=
  by induction z; reflexivity

  protected definition code [unfold 2 3] : lift A → lift A → Type
  | code (up a) (up a') := a = a'

  protected definition decode [unfold 2 3] : Π(z z' : lift A), lift.code z z' → z = z'
  | decode (up a) (up a') := λc, ap up c

  variables {z z'}
  protected definition encode [unfold 3 4 5] (p : z = z') : lift.code z z' :=
  by induction p; induction z; esimp

  variables (z z')
  definition lift_eq_equiv : (z = z') ≃ lift.code z z' :=
  equiv.MK lift.encode
           !lift.decode
           abstract begin
             intro c, induction z with a, induction z' with a', esimp at *, induction c,
             reflexivity
           end end
           abstract begin
             intro p, induction p, induction z, reflexivity
           end end


  section
  variables {a a' : A}
  definition eq_of_up_eq_up [unfold 4] (p : up a = up a') : a = a' :=
  lift.encode p

  definition lift_transport {P : A → Type} (p : a = a') (z : lift (P a))
    : p ▸ z = up (p ▸ down z) :=
  by induction p; induction z; reflexivity
  end

  variables {A' : Type} (f : A → A') (g : lift A → lift A')
  definition lift_functor [unfold 4] : lift A → lift A'
  | lift_functor (up a) := up (f a)

  definition is_equiv_lift_functor [constructor] [Hf : is_equiv f] : is_equiv (lift_functor f) :=
  adjointify (lift_functor f)
             (lift_functor f⁻¹)
             abstract begin
               intro z', induction z' with a',
               esimp, exact ap up !right_inv
             end end
             abstract begin
               intro z, induction z with a,
               esimp, exact ap up !left_inv
             end end

  definition lift_equiv_lift_of_is_equiv [constructor] [Hf : is_equiv f] : lift A ≃ lift A' :=
  equiv.mk _ (is_equiv_lift_functor f)

  definition lift_equiv_lift [constructor] (f : A ≃ A') : lift A ≃ lift A' :=
  equiv.mk _ (is_equiv_lift_functor f)

  definition lift_equiv_lift_refl (A : Type) : lift_equiv_lift (erfl : A ≃ A) = erfl :=
  by apply equiv_eq'; intro z; induction z with a; reflexivity

  definition lift_inv_functor [unfold-full] (a : A) : A' :=
  down (g (up a))

  definition is_equiv_lift_inv_functor [constructor] [Hf : is_equiv g]
    : is_equiv (lift_inv_functor g) :=
  adjointify (lift_inv_functor g)
             (lift_inv_functor g⁻¹)
             abstract begin
               intro z', rewrite [▸*,lift.eta,right_inv g],
             end end
             abstract begin
               intro z', rewrite [▸*,lift.eta,left_inv g],
             end end

  definition equiv_of_lift_equiv_lift [constructor] (g : lift A ≃ lift A') : A ≃ A' :=
  equiv.mk _ (is_equiv_lift_inv_functor g)

  definition lift_functor_left_inv  : lift_inv_functor (lift_functor f) = f :=
  eq_of_homotopy (λa, idp)

  definition lift_functor_right_inv : lift_functor (lift_inv_functor g) = g :=
  begin
    apply eq_of_homotopy, intro z, induction z with a, esimp, apply lift.eta
  end

  variables (A A')
  definition is_equiv_lift_functor_fn [constructor]
    : is_equiv (lift_functor : (A → A') → (lift A → lift A')) :=
  adjointify lift_functor
             lift_inv_functor
             lift_functor_right_inv
             lift_functor_left_inv

  definition lift_imp_lift_equiv [constructor] : (lift A → lift A') ≃ (A → A') :=
  (equiv.mk _ (is_equiv_lift_functor_fn A A'))⁻¹ᵉ

  -- can we deduce this from lift_imp_lift_equiv?
  definition lift_equiv_lift_equiv [constructor] : (lift A ≃ lift A') ≃ (A ≃ A') :=
  equiv.MK equiv_of_lift_equiv_lift
           lift_equiv_lift
           abstract begin
             intro f, apply equiv_eq, reflexivity
           end end
           abstract begin
             intro g, apply equiv_eq, esimp, apply eq_of_homotopy, intro z,
             induction z with a, esimp, apply lift.eta
           end end

  definition lift_eq_lift_equiv.{u1 u2} (A A' : Type.{u1})
    : (lift.{u1 u2} A = lift.{u1 u2} A') ≃ (A = A') :=
  !eq_equiv_equiv ⬝e !lift_equiv_lift_equiv ⬝e !eq_equiv_equiv⁻¹ᵉ

  definition is_embedding_lift [instance] : is_embedding lift :=
  begin
    apply is_embedding.mk, intro A A', fapply is_equiv.homotopy_closed,
      exact to_inv !lift_eq_lift_equiv,
      exact _,
    { intro p, induction p,
      esimp [lift_eq_lift_equiv,equiv.trans,equiv.symm,eq_equiv_equiv],
      rewrite [equiv_of_eq_refl,lift_equiv_lift_refl],
      apply ua_refl}
  end

end lift
