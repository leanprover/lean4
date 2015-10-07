/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad, Floris van Doorn

Sigma types, aka dependent sum.
-/
import logic.cast
open inhabited sigma.ops
override eq.ops

namespace sigma
  universe variables u v
  variables {A A' : Type.{u}} {B : A → Type.{v}} {B' : A' → Type.{v}}

  definition unpack {C : (Σa, B a) → Type} {u : Σa, B a} (H : C ⟨u.1 , u.2⟩) : C u :=
  destruct u (λx y H, H) H

  theorem dpair_heq {a : A} {a' : A'} {b : B a} {b' : B' a'}
      (HB : B == B') (Ha : a == a') (Hb : b == b') : ⟨a, b⟩ == ⟨a', b'⟩ :=
  hcongr_arg4 @mk (heq.type_eq Ha) HB Ha Hb

  protected theorem heq {p : Σa : A, B a} {p' : Σa' : A', B' a'} (HB : B == B') :
    ∀(H₁ : p.1 == p'.1) (H₂ : p.2 == p'.2), p == p' :=
  destruct p (take a₁ b₁, destruct p' (take a₂ b₂ H₁ H₂, dpair_heq HB H₁ H₂))

  protected definition is_inhabited [instance] [H₁ : inhabited A] [H₂ : inhabited (B (default A))] :
    inhabited (sigma B) :=
  inhabited.destruct H₁ (λa, inhabited.destruct H₂ (λb, inhabited.mk ⟨default A, b⟩))

  theorem eq_rec_dpair_commute {C : Πa, B a → Type} {a a' : A} (H : a = a') (b : B a) (c : C a b) :
      eq.rec_on H ⟨b, c⟩ = ⟨eq.rec_on H b, eq.rec_on (dcongr_arg2 C H rfl) c⟩ :=
  eq.drec_on H (dpair_eq rfl (!eq.rec_on_id⁻¹))

  variables {C : Πa, B a → Type} {D : Πa b, C a b → Type}

  definition dtrip (a : A) (b : B a) (c : C a b) := ⟨a, b, c⟩
  definition dquad (a : A) (b : B a) (c : C a b) (d : D a b c) := ⟨a, b, c, d⟩

  definition pr1' [reducible] (x : Σ a, B a) := x.1
  definition pr2' [reducible] (x : Σ a b, C a b) := x.2.1
  definition pr3  [reducible] (x : Σ a b, C a b) := x.2.2
  definition pr3' [reducible] (x : Σ a b c, D a b c) := x.2.2.1
  definition pr4  [reducible] (x : Σ a b c, D a b c) := x.2.2.2

  theorem dtrip_eq {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} {c₁ : C a₁ b₁} {c₂ : C a₂ b₂}
      (H₁ : a₁ = a₂) (H₂ : eq.rec_on H₁ b₁ = b₂) (H₃ : cast (dcongr_arg2 C H₁ H₂) c₁ = c₂) :
    ⟨a₁, b₁, c₁⟩ = ⟨a₂, b₂, c₂⟩ :=
  dcongr_arg3 dtrip H₁ H₂ H₃

  theorem ndtrip_eq {A B : Type} {C : A → B → Type} {a₁ a₂ : A} {b₁ b₂ : B}
      {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} (H₁ : a₁ = a₂) (H₂ : b₁ = b₂)
      (H₃ : cast (congr_arg2 C H₁ H₂) c₁ = c₂) : ⟨a₁, b₁, c₁⟩ = ⟨a₂, b₂, c₂⟩ :=
  hdcongr_arg3 dtrip H₁ (heq.of_eq H₂) H₃

  theorem ndtrip_equal {A B : Type} {C : A → B → Type} {p₁ p₂ : Σa b, C a b} :
      ∀(H₁ : pr1 p₁ = pr1 p₂) (H₂ : pr2' p₁ = pr2' p₂)
      (H₃ : eq.rec_on (congr_arg2 C H₁ H₂) (pr3 p₁) = pr3 p₂), p₁ = p₂ :=
  destruct p₁ (take a₁ q₁, destruct q₁ (take b₁ c₁, destruct p₂ (take a₂ q₂, destruct q₂
    (take b₂ c₂ H₁ H₂ H₃, ndtrip_eq H₁ H₂ H₃))))

end sigma
