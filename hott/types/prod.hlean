/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Ported from Coq HoTT
Theorems about products
-/

open eq equiv is_equiv is_trunc prod prod.ops unit

variables {A A' B B' C D : Type}
          {a a' a'' : A} {b b₁ b₂ b' b'' : B} {u v w : A × B}

namespace prod

  protected definition eta (u : A × B) : (pr₁ u, pr₂ u) = u :=
  by cases u; apply idp

  definition pair_eq (pa : a = a') (pb : b = b') : (a, b) = (a', b') :=
  by cases pa; cases pb; apply idp

  definition prod_eq (H₁ : pr₁ u = pr₁ v) (H₂ : pr₂ u = pr₂ v) : u = v :=
  by cases u; cases v; exact pair_eq H₁ H₂

  /- Symmetry -/

  definition is_equiv_flip [instance] (A B : Type) : is_equiv (@flip A B) :=
  adjointify flip
             flip
             (λu, destruct u (λb a, idp))
             (λu, destruct u (λa b, idp))

  definition prod_comm_equiv (A B : Type) : A × B ≃ B × A :=
  equiv.mk flip _

  definition prod_contr_equiv (A B : Type) [H : is_contr B] : A × B ≃ A :=
  equiv.MK pr1
           (λx, (x, !center))
           (λx, idp)
           (λx, by cases x with a b; exact pair_eq idp !center_eq)

  definition prod_unit_equiv (A : Type) : A × unit ≃ A :=
  !prod_contr_equiv

  -- is_trunc_prod is defined in sigma

end prod
