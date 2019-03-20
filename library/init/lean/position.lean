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
instance : decidableEq position :=
{decEq := λ ⟨l₁, c₁⟩ ⟨l₂, c₂⟩,
  if h₁ : l₁ = l₂ then
  if h₂ : c₁ = c₂ then isTrue (eq.recOn h₁ (eq.recOn h₂ rfl))
  else isFalse (λ contra, position.noConfusion contra (λ e₁ e₂, absurd e₂ h₂))
  else isFalse (λ contra, position.noConfusion contra (λ e₁ e₂, absurd e₁ h₁))}

protected def lt : position → position → Prop
| ⟨l₁, c₁⟩ ⟨l₂, c₂⟩ := (l₁, c₁) < (l₂, c₂)

instance : hasLt position := ⟨position.lt⟩

instance decidableLt : Π (p₁ p₂ : position), decidable (p₁ < p₂)
| ⟨l₁, c₁⟩ ⟨l₂, c₂⟩ := inferInstanceAs $ decidable ((l₁, c₁) < (l₂, c₂))

instance : hasToFormat position :=
⟨λ ⟨l, c⟩, "⟨" ++ toFmt l ++ ", " ++ toFmt c ++ "⟩"⟩

instance : inhabited position := ⟨⟨1, 0⟩⟩
end position

/-- A precomputed cache for quickly mapping char offsets to positionitions. -/
structure fileMap :=
-- A mapping from char offset of line start to line index
(lines : rbmap nat nat (<))

namespace fileMap
private def fromStringAux : nat → string.iterator → nat → list (nat × nat)
| 0     it line := []
| (k+1) it line :=
  if it.hasNext = ff then []
  else match it.curr with
       | '\n'  := (it.next.offset, line+1) :: fromStringAux k it.next (line+1)
       | other := fromStringAux k it.next line

def fromString (s : string) : fileMap :=
{lines := rbmap.ofList $ fromStringAux s.length s.mkIterator 1}

def toPosition (m : fileMap) (off : nat) : position :=
match m.lines.lowerBound off with
| some ⟨start, l⟩ := ⟨l, off - start⟩
| none            := ⟨1, off⟩
end fileMap

end lean
