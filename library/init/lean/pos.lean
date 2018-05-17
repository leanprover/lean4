/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.data.nat init.lean.format

namespace lean

structure pos :=
(line   : nat)
(column : nat)

instance : decidable_eq pos
| ⟨l₁, c₁⟩ ⟨l₂, c₂⟩ := if h₁ : l₁ = l₂ then
  if h₂ : c₁ = c₂ then is_true (eq.rec_on h₁ (eq.rec_on h₂ rfl))
  else is_false (λ contra, pos.no_confusion contra (λ e₁ e₂, absurd e₂ h₂))
else is_false (λ contra, pos.no_confusion contra (λ e₁ e₂, absurd e₁ h₁))

def pos.lt : pos → pos → Prop
| ⟨l₁, c₁⟩ ⟨l₂, c₂⟩ := (l₁, c₁) < (l₂, c₂)

instance pos.has_lt : has_lt pos := ⟨pos.lt⟩

instance pos.decidable_lt : Π (p₁ p₂ : pos), decidable (p₁ < p₂)
| ⟨l₁, c₁⟩ ⟨l₂, c₂⟩ := infer_instance_as $ decidable ((l₁, c₁) < (l₂, c₂))

instance : has_to_format pos :=
⟨λ ⟨l, c⟩, "⟨" ++ to_fmt l ++ ", " ++ to_fmt c ++ "⟩"⟩

end lean
