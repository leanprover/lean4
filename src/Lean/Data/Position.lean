/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Data.Format
import Lean.ToExpr

namespace Lean

structure Position where
  line   : Nat
  column : Nat
  deriving Inhabited, DecidableEq, Repr

namespace Position
protected def lt : Position → Position → Bool
  | ⟨l₁, c₁⟩, ⟨l₂, c₂⟩ => Prod.lexLt (l₁, c₁) (l₂, c₂)

instance : ToFormat Position :=
  ⟨fun ⟨l, c⟩ => "⟨" ++ format l ++ ", " ++ format c ++ "⟩"⟩

instance : ToString Position :=
  ⟨fun ⟨l, c⟩ => "⟨" ++ toString l ++ ", " ++ toString c ++ "⟩"⟩

instance : ToExpr Position where
  toExpr p   := mkAppN (mkConst ``Position.mk) #[toExpr p.line, toExpr p.column]
  toTypeExpr := mkConst ``Position

end Position

structure FileMap where
  source    : String
  positions : Array String.Pos
  lines     : Array Nat
  deriving Inhabited

class MonadFileMap (m : Type → Type) where
  getFileMap : m FileMap

export MonadFileMap (getFileMap)

namespace FileMap

partial def ofString (s : String) : FileMap :=
  let rec loop (i : String.Pos) (line : Nat) (ps : Array String.Pos) (lines : Array Nat) : FileMap :=
    if s.atEnd i then { source := s, positions := ps.push i, lines := lines.push line }
    else
      let c := s.get i
      let i := s.next i
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
        let posB := ps[b]!
        if e == b + 1 then { line := lines.get! b, column := toColumn posB 0 }
        else
          let m := (b + e) / 2;
          let posM := ps.get! m;
          if pos == posM then { line := lines.get! m, column := 0 }
          else if pos > posM then loop m e
          else loop b m
      loop 0 (ps.size -1)
    else if lines.isEmpty then
      ⟨0, 0⟩
    else
      -- Some systems like the delaborator use synthetic positions without an input file,
      -- which would violate `toPositionAux`'s invariant.
      -- Can also happen with EOF errors, which are not strictly inside the file.
      ⟨lines.back, (pos - ps.back).byteIdx⟩

end FileMap
end Lean

def String.toFileMap (s : String) : Lean.FileMap :=
  Lean.FileMap.ofString s
