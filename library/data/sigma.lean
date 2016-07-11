/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad, Floris van Doorn

Sigma types, aka dependent sum.
-/
import logic.cast
open inhabited sigma.ops

namespace sigma
  universe variables u v
  variables {A A' : Type.{u}} {B : A → Type.{v}} {B' : A' → Type.{v}}

  definition unpack {C : (Σa, B a) → Type} {u : Σa, B a} : C ⟨u.1 , u.2⟩ → C u :=
  sigma.rec_on u (λ u1 u2 H, H)

  theorem dpair_heq {a : A} {a' : A'} {b : B a} {b' : B' a'}
      (HB : B == B') (Ha : a == a') (Hb : b == b') : ⟨a, b⟩ == ⟨a', b'⟩ :=
  hcongr_arg4 @mk (type_eq_of_heq Ha) HB Ha Hb

  protected theorem heq {p : Σa : A, B a} {p' : Σa' : A', B' a'} (HB : B == B') :
    ∀(H₁ : p.1 == p'.1) (H₂ : p.2 == p'.2), p == p' :=
  destruct p (take a₁ b₁, destruct p' (take a₂ b₂ H₁ H₂, dpair_heq HB H₁ H₂))

  protected definition is_inhabited [instance] [H₁ : inhabited A] [H₂ : inhabited (B (default A))] :
    inhabited (sigma B) :=
  inhabited.destruct H₁ (λa, inhabited.destruct H₂ (λb, inhabited.mk ⟨default A, b⟩))

    variables {C : Πa, B a → Type} {D : Πa b, C a b → Type}

  definition dtrip (a : A) (b : B a) (c : C a b) := ⟨a, b, c⟩
  definition dquad (a : A) (b : B a) (c : C a b) (d : D a b c) := ⟨a, b, c, d⟩

  definition pr1' [reducible] (x : Σ a, B a) := x.1
  definition pr2' [reducible] (x : Σ a b, C a b) := x.2.1
  definition pr3  [reducible] (x : Σ a b, C a b) := x.2.2
  definition pr3' [reducible] (x : Σ a b c, D a b c) := x.2.2.1
  definition pr4  [reducible] (x : Σ a b c, D a b c) := x.2.2.2
end sigma
