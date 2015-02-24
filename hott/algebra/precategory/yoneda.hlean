/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.precategory.yoneda
Author: Floris van Doorn
-/

--note: modify definition in category.set
import .constructions .morphism

open eq precategory equiv is_equiv is_trunc
open is_trunc.trunctype funext precategory.ops prod.ops

set_option pp.beta true

namespace yoneda
  set_option class.conservative false

  definition representable_functor_assoc [C : Precategory] {a1 a2 a3 a4 a5 a6 : C} (f1 : a5 ⟶ a6) (f2 : a4 ⟶ a5) (f3 : a3 ⟶ a4) (f4 : a2 ⟶ a3) (f5 : a1 ⟶ a2) : (f1 ∘ f2) ∘ f3 ∘ (f4 ∘ f5) = f1 ∘ (f2 ∘ f3 ∘ f4) ∘ f5 :=
  calc
    (f1 ∘ f2) ∘ f3 ∘ f4 ∘ f5 = f1 ∘ f2 ∘ f3 ∘ f4 ∘ f5 : assoc
    ... = f1 ∘ (f2 ∘ f3) ∘ f4 ∘ f5 : assoc
    ... = f1 ∘ ((f2 ∘ f3) ∘ f4) ∘ f5 : assoc
    ... = f1 ∘ (f2 ∘ f3 ∘ f4) ∘ f5 : assoc

  --disturbing behaviour: giving the type of f "(x ⟶ y)" explicitly makes the unifier loop
  definition representable_functor (C : Precategory) : Cᵒᵖ ×c C ⇒ set :=
  functor.mk (λ(x : Cᵒᵖ ×c C), homset x.1 x.2)
             (λ(x y : Cᵒᵖ ×c C) (f : _) (h : homset x.1 x.2), f.2 ∘⁅ C ⁆ (h ∘⁅ C ⁆ f.1))
             proof (λ(x : Cᵒᵖ ×c C), eq_of_homotopy (λ(h : homset x.1 x.2), !id_left ⬝ !id_right)) qed
             -- (λ(x y z : Cᵒᵖ ×c C) (g : y ⟶ z) (f : x ⟶ y), eq_of_homotopy (λ(h : hom x.1 x.2), representable_functor_assoc g.2 f.2 h f.1 g.1))
             begin
               intros (x, y, z, g, f), apply eq_of_homotopy, intro h,
               exact (representable_functor_assoc g.2 f.2 h f.1 g.1),
             end
end yoneda

attribute precategory_functor [instance] [reducible]
namespace nat_trans
  open morphism functor
  variables {C D : Precategory} {F G : C ⇒ D} (η : F ⟹ G) (H : Π(a : C), is_iso (η a))
  include H
  definition nat_trans_inverse : G ⟹ F :=
  nat_trans.mk
    (λc, (η c)⁻¹)
    (λc d f,
    begin
      apply iso.con_inv_eq_of_eq_con,
      apply concat, rotate_left 1, apply assoc,
      apply iso.eq_inv_con_of_con_eq,
      apply inverse,
      apply naturality,
    end)

  definition nat_trans_left_inverse : nat_trans_inverse η H ∘ η = nat_trans.id :=
  begin
  fapply (apD011 nat_trans.mk),
    apply eq_of_homotopy, intro c, apply inverse_compose,
  apply eq_of_homotopy, intros, apply eq_of_homotopy, intros, apply eq_of_homotopy, intros, fapply is_hset.elim
  end

  definition nat_trans_right_inverse : η ∘ nat_trans_inverse η H = nat_trans.id :=
  begin
  fapply (apD011 nat_trans.mk),
    apply eq_of_homotopy, intro c, apply compose_inverse,
  apply eq_of_homotopy, intros, apply eq_of_homotopy, intros, apply eq_of_homotopy, intros, fapply is_hset.elim
  end

  definition nat_trans_is_iso.mk : is_iso η :=
  is_iso.mk (nat_trans_left_inverse η H) (nat_trans_right_inverse η H)

end nat_trans

-- Coq uses unit/counit definitions as basic

-- open yoneda precategory.product precategory.opposite functor morphism
--   --universe levels are given explicitly because Lean uses 6 variables otherwise

--   structure adjoint.{u v} [C D : Precategory.{u v}] (F : C ⇒ D) (G : D ⇒ C) : Type.{max u v} :=
--   (nat_iso : (representable_functor D) ∘f (prod_functor (opposite_functor F) (functor.ID D)) ⟹
--              (representable_functor C) ∘f (prod_functor (functor.ID (Cᵒᵖ)) G))
--   (is_iso_nat_iso : is_iso nat_iso)

--   infix `⊣`:55 := adjoint

-- namespace adjoint
--   universe variables l1 l2
--   variables [C D : Precategory.{l1 l2}] (F : C ⇒ D) (G : D ⇒ C)



-- end adjoint
