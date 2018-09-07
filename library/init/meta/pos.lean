/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.nat
universes u v

structure pos :=
(line   : nat)
(column : nat)

instance : decidable_eq pos :=
{dec_eq := λ ⟨l₁, c₁⟩ ⟨l₂, c₂⟩,
 if h₁ : l₁ = l₂ then
 if h₂ : c₁ = c₂ then is_true (eq.rec_on h₁ (eq.rec_on h₂ rfl))
 else is_false (λ contra, pos.no_confusion contra (λ e₁ e₂, absurd e₂ h₂))
 else is_false (λ contra, pos.no_confusion contra (λ e₁ e₂, absurd e₁ h₁))}
