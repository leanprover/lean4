/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Data.Format

namespace Lean

structure Position where
  line   : Nat
  column : Nat
  deriving Inhabited

namespace Position
instance : DecidableEq Position :=
  fun ⟨l₁, c₁⟩ ⟨l₂, c₂⟩ =>
    if h₁ : l₁ = l₂ then
    if h₂ : c₁ = c₂ then
      isTrue $ by subst h₁; subst h₂; rfl
    else
      isFalse fun contra => Position.noConfusion contra (fun e₁ e₂ => absurd e₂ h₂)
    else
      isFalse fun contra => Position.noConfusion contra (fun e₁ e₂ => absurd e₁ h₁)

protected def lt : Position → Position → Bool
  | ⟨l₁, c₁⟩, ⟨l₂, c₂⟩ => (l₁, c₁) < (l₂, c₂)

instance : ToFormat Position :=
  ⟨fun ⟨l, c⟩ => "⟨" ++ fmt l ++ ", " ++ fmt c ++ "⟩"⟩

instance : ToString Position :=
  ⟨fun ⟨l, c⟩ => "⟨" ++ toString l ++ ", " ++ toString c ++ "⟩"⟩
end Position

structure FileMap where
  source    : String
  positions : Array String.Pos
  lines     : Array Nat
  deriving Inhabited

namespace FileMap

partial def ofString (s : String) : FileMap :=
  let rec loop (i : String.Pos) (line : Nat) (ps : Array String.Pos) (lines : Array Nat) : FileMap :=
    if s.atEnd i then { source := s, positions := ps.push i, lines := lines.push line }
    else
      let c := s.get i;
      let i := s.next i;
      if c == '\n' then loop i (line+1) (ps.push i) (lines.push (line+1))
      else loop i line ps lines
  loop 0 1 (#[0]) (#[1])

partial def toPosition (fmap : FileMap) (pos : String.Pos) : Position :=
  match fmap with
  | { source := str, positions := ps, lines := lines } =>
    if ps.size >= 2 && pos <= ps.back then
      let rec toColumn (i : String.Pos) (c : Nat) : Nat :=
        if i == pos || str.atEnd i then c
        else toColumn (str.next i) (c+1)
      let rec loop (b e : Nat) :=
        let posB := ps[b]
        if e == b + 1 then { line := lines.get! b, column := toColumn posB 0 }
        else
          let m := (b + e) / 2;
          let posM := ps.get! m;
          if pos == posM then { line := lines.get! m, column := 0 }
          else if pos > posM then loop m e
          else loop b m
      loop 0 (ps.size -1)
    else
      -- Some systems like the delaborator use synthetic positions without an input file,
      -- which would violate `toPositionAux`'s invariant
      ⟨1, pos⟩

end FileMap
end Lean

def String.toFileMap (s : String) : Lean.FileMap :=
  Lean.FileMap.ofString s
