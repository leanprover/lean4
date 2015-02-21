/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn
Ported from Coq HoTT

Theorems about products
-/

open eq equiv is_equiv is_trunc prod

variables {A A' B B' C D : Type}
          {a a' a'' : A} {b b₁ b₂ b' b'' : B} {u v w : A × B}

namespace prod

  -- prod.eta is already used for the eta rule for strict equality
  protected definition eta (u : A × B) : (pr₁ u , pr₂ u) = u :=
  destruct u (λu1 u2, idp)

  definition pair_eq (pa : a = a') (pb : b = b') : (a , b) = (a' , b') :=
  eq.rec_on pa (eq.rec_on pb idp)

  definition prod_eq : (pr₁ u = pr₁ v) → (pr₂ u = pr₂ v) → u = v :=
  begin
    apply (prod.rec_on u), intros (a₁, b₁),
    apply (prod.rec_on v), intros (a₂, b₂, H₁, H₂),
    apply (transport _ (eta (a₁, b₁))),
    apply (transport _ (eta (a₂, b₂))),
    apply (pair_eq H₁ H₂),
  end

  /- Symmetry -/

  definition is_equiv_flip [instance] (A B : Type) : is_equiv (@flip A B) :=
  adjointify flip
             flip
             (λu, destruct u (λb a, idp))
             (λu, destruct u (λa b, idp))

  definition prod_comm_equiv (A B : Type) : A × B ≃ B × A :=
  equiv.mk flip _

  -- is_trunc_prod is defined in sigma

end prod
