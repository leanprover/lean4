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

/-- A precomputed cache for quickly mapping char offsets to positionitions. -/
structure file_map :=
-- A mapping from char offset of line start to line index
(lines : rbmap nat nat (<))

namespace file_map
private def from_string_aux : nat → string.iterator → nat → list (nat × nat)
| 0     it line := []
| (k+1) it line :=
  if it.has_next = ff then []
  else match it.curr with
       | '\n'  := (it.next.offset, line+1) :: from_string_aux k it.next (line+1)
       | other := from_string_aux k it.next line

def from_string (s : string) : file_map :=
{lines := rbmap.of_list $ from_string_aux s.length s.mk_iterator 1}

def to_position (m : file_map) (off : nat) : position :=
match m.lines.lower_bound off with
| some ⟨start, l⟩ := ⟨l, off - start⟩
| none            := ⟨1, off⟩
end file_map

end lean
