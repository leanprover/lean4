/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.data.nat init.data.rbmap init.lean.format init.lean.parser.parsec

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

/-- A precomputed cache for quickly mapping Char offsets to positionitions. -/
structure FileMap :=
-- A mapping from Char offset of line start to line index
(lines : RBMap Nat Nat (λ a b, a < b))

namespace FileMap
private def fromStringAux : Nat → String.OldIterator → Nat → List (Nat × Nat)
| 0     it line := []
| (k+1) it line :=
  if it.hasNext = false then []
  else match it.curr with
       | '\n'  := (it.next.offset, line+1) :: fromStringAux k it.next (line+1)
       | other := fromStringAux k it.next line

def fromString (s : String) : FileMap :=
{lines := RBMap.ofList $ fromStringAux s.length s.mkOldIterator 1}

def toPosition (m : FileMap) (off : Nat) : Position :=
match m.lines.lowerBound off with
| some ⟨start, l⟩ := ⟨l, off - start⟩
| none            := ⟨1, off⟩
end FileMap

end Lean
