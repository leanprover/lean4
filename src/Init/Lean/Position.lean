/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Data.Nat
import Init.Data.RBMap
import Init.Lean.Format

namespace Lean

structure Position :=
(line   : Nat)
(column : Nat)

namespace Position
instance : DecidableEq Position :=
fun ⟨l₁, c₁⟩ ⟨l₂, c₂⟩ =>
  if h₁ : l₁ = l₂ then
  if h₂ : c₁ = c₂ then isTrue (Eq.recOn h₁ (Eq.recOn h₂ rfl))
  else isFalse (fun contra => Position.noConfusion contra (fun e₁ e₂ => absurd e₂ h₂))
  else isFalse (fun contra => Position.noConfusion contra (fun e₁ e₂ => absurd e₁ h₁))

protected def lt : Position → Position → Bool
| ⟨l₁, c₁⟩, ⟨l₂, c₂⟩ => (l₁, c₁) < (l₂, c₂)

instance : HasFormat Position :=
⟨fun ⟨l, c⟩ => "⟨" ++ fmt l ++ ", " ++ fmt c ++ "⟩"⟩

instance : HasToString Position :=
⟨fun ⟨l, c⟩ => "⟨" ++ toString l ++ ", " ++ toString c ++ "⟩"⟩

instance : Inhabited Position := ⟨⟨1, 0⟩⟩
end Position

structure FileMap :=
(source    : String)
(positions : Array String.Pos)
(lines     : Array Nat)

namespace FileMap

instance : Inhabited FileMap :=
⟨{ source := "", positions := #[], lines := #[] }⟩

private partial def ofStringAux (s : String) : String.Pos → Nat → Array String.Pos → Array Nat → FileMap
| i, line, ps, lines =>
  if s.atEnd i then { source := s, positions := ps.push i, lines := lines.push line }
  else
    let c := s.get i;
    let i := s.next i;
    if c == '\n' then ofStringAux i (line+1) (ps.push i) (lines.push (line+1))
    else ofStringAux i line ps lines

def ofString (s : String) : FileMap :=
ofStringAux s 0 1 (#[0]) (#[1])

private partial def toColumnAux (str : String) (lineBeginPos : String.Pos) (pos : String.Pos) : String.Pos → Nat → Nat
| i, c =>
  if i == pos || str.atEnd i then c
  else toColumnAux (str.next i) (c+1)

/- Remark: `pos` is in `[ps.get b, ps.get e]` and `b < e` -/
private partial def toPositionAux (str : String) (ps : Array Nat) (lines : Array Nat) (pos : String.Pos) : Nat → Nat → Position
| b, e =>
  let posB := ps.get! b;
  if e == b + 1 then { line := lines.get! b, column := toColumnAux str posB pos posB 0 }
  else
    let m := (b + e) / 2;
    let posM := ps.get! m;
    if pos == posM then { line := lines.get! m, column := 0 }
    else if pos > posM then toPositionAux m e
    else toPositionAux b m

def toPosition : FileMap → String.Pos → Position
| { source := str, positions := ps, lines := lines }, pos => toPositionAux str ps lines pos 0 (ps.size-1)

end FileMap
end Lean

def String.toFileMap (s : String) : Lean.FileMap :=
Lean.FileMap.ofString s
