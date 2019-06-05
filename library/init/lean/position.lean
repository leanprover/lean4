/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.data.nat init.data.rbmap init.lean.format

namespace Lean

structure Position :=
(line   : Nat)
(column : Nat)

namespace Position
instance : DecidableEq Position :=
{decEq := λ ⟨l₁, c₁⟩ ⟨l₂, c₂⟩,
  if h₁ : l₁ = l₂ then
  if h₂ : c₁ = c₂ then isTrue (Eq.recOn h₁ (Eq.recOn h₂ rfl))
  else isFalse (λ contra, Position.noConfusion contra (λ e₁ e₂, absurd e₂ h₂))
  else isFalse (λ contra, Position.noConfusion contra (λ e₁ e₂, absurd e₁ h₁))}

protected def lt : Position → Position → Bool
| ⟨l₁, c₁⟩ ⟨l₂, c₂⟩ := (l₁, c₁) < (l₂, c₂)

instance : HasFormat Position :=
⟨λ ⟨l, c⟩, "⟨" ++ fmt l ++ ", " ++ fmt c ++ "⟩"⟩

instance : Inhabited Position := ⟨⟨1, 0⟩⟩
end Position

end Lean
