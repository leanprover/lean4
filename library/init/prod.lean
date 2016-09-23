/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad
-/
prelude
import init.num init.relation
notation A × B := prod A B
-- notation for n-ary tuples
notation `(` h `, ` t:(foldr `, ` (e r, prod.mk e r)) `)` := prod.mk h t

universe variables u v

instance {A : Type u} {B : Type v} [inhabited A] [inhabited B] : inhabited (prod A B) :=
⟨(default A, default B)⟩

instance {A : Type u} {B : Type v} [h₁ : decidable_eq A] [h₂ : decidable_eq B] : decidable_eq (A × B)
| (a, b) (a', b') :=
  match (h₁ a a') with
  | (is_true e₁) :=
    match (h₂ b b') with
    | (is_true e₂)  := is_true (eq.rec_on e₁ (eq.rec_on e₂ rfl))
    | (is_false n₂) := is_false (assume h, prod.no_confusion h (λ e₁' e₂', absurd e₂' n₂))
    end
  | (is_false n₁) := is_false (assume h, prod.no_confusion h (λ e₁' e₂', absurd e₁' n₁))
  end
