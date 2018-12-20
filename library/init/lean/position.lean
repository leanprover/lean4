/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.data.nat init.data.rbmap init.lean.format

namespace lean

structure position :=
(line   : nat)
(column : nat)

namespace position
instance : decidable_eq position :=
{dec_eq := λ ⟨l₁, c₁⟩ ⟨l₂, c₂⟩,
  if h₁ : l₁ = l₂ then
  if h₂ : c₁ = c₂ then is_true (eq.rec_on h₁ (eq.rec_on h₂ rfl))
  else is_false (λ contra, position.no_confusion contra (λ e₁ e₂, absurd e₂ h₂))
  else is_false (λ contra, position.no_confusion contra (λ e₁ e₂, absurd e₁ h₁))}

protected def lt : position → position → Prop
| ⟨l₁, c₁⟩ ⟨l₂, c₂⟩ := (l₁, c₁) < (l₂, c₂)

instance : has_lt position := ⟨position.lt⟩

instance decidable_lt : Π (p₁ p₂ : position), decidable (p₁ < p₂)
| ⟨l₁, c₁⟩ ⟨l₂, c₂⟩ := infer_instance_as $ decidable ((l₁, c₁) < (l₂, c₂))

instance : has_to_format position :=
⟨λ ⟨l, c⟩, "⟨" ++ to_fmt l ++ ", " ++ to_fmt c ++ "⟩"⟩

instance : inhabited position := ⟨⟨1, 0⟩⟩
end position

end lean
