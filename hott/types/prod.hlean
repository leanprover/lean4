/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: types.prod
Author: Floris van Doorn

Ported from Coq HoTT
Theorems about products
-/

open eq equiv is_equiv is_trunc prod prod.ops

variables {A A' B B' C D : Type}
          {a a' a'' : A} {b b₁ b₂ b' b'' : B} {u v w : A × B}

namespace prod

  -- prod.eta is already used for the eta rule for strict equality
  protected definition eta (u : A × B) : (pr₁ u , pr₂ u) = u :=
  by cases u; apply idp

  definition pair_eq (pa : a = a') (pb : b = b') : (a , b) = (a' , b') :=
  by cases pa; cases pb; apply idp

  definition prod_eq (H₁ : pr₁ u = pr₁ v) (H₂ : pr₂ u = pr₂ v) : u = v :=
  begin
    cases u with a₁ b₁,
    cases v with a₂ b₂,
    apply transport _ (prod.eta (a₁, b₁)),
    apply transport _ (prod.eta (a₂, b₂)),
    apply pair_eq H₁ H₂,
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
