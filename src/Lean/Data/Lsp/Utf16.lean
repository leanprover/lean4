/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
prelude
import Init.Data.String
import Init.Data.Array
import Lean.Data.Lsp.Basic
import Lean.Data.Position
import Lean.DeclarationRange

/-! LSP uses UTF-16 for indexing, so we need to provide some primitives
to interact with Lean strings using UTF-16 indices. -/

namespace Char

def utf16Size (c : Char) : UInt32 :=
  if c.val ≤ 0xFFFF then 1 else 2

end Char

namespace String

private def csize16 (c : Char) : Nat :=
  c.utf16Size.toNat

def utf16Length (s : String) : Nat :=
  s.foldr (fun c acc => csize16 c + acc) 0

private def codepointPosToUtf16PosFromAux (s : String) : Nat → Pos → Nat → Nat
  | 0,    _,       utf16pos => utf16pos
  | cp+1, utf8pos, utf16pos => codepointPosToUtf16PosFromAux s cp (s.next utf8pos) (utf16pos + csize16 (s.get utf8pos))

/-- Computes the UTF-16 offset of the `n`-th Unicode codepoint
in the substring of `s` starting at UTF-8 offset `off`.
Yes, this is actually useful.-/
def codepointPosToUtf16PosFrom (s : String) (n : Nat) (off : Pos) : Nat :=
  codepointPosToUtf16PosFromAux s n off 0

def codepointPosToUtf16Pos (s : String) (pos : Nat) : Nat :=
  codepointPosToUtf16PosFrom s pos 0

private partial def utf16PosToCodepointPosFromAux (s : String) : Nat → Pos → Nat → Nat
  | 0,        _,       cp => cp
  | utf16pos, utf8pos, cp => utf16PosToCodepointPosFromAux s (utf16pos - csize16 (s.get utf8pos)) (s.next utf8pos) (cp + 1)

/-- Computes the position of the Unicode codepoint at UTF-16 offset
`utf16pos` in the substring of `s` starting at UTF-8 offset `off`. -/
def utf16PosToCodepointPosFrom (s : String) (utf16pos : Nat) (off : Pos) : Nat :=
  utf16PosToCodepointPosFromAux s utf16pos off 0

def utf16PosToCodepointPos (s : String) (pos : Nat) : Nat :=
  utf16PosToCodepointPosFrom s pos 0

/-- Starting at `utf8pos`, finds the UTF-8 offset of the `p`-th codepoint. -/
def codepointPosToUtf8PosFrom (s : String) : String.Pos → Nat → String.Pos
  | utf8pos, 0 => utf8pos
  | utf8pos, p+1 => codepointPosToUtf8PosFrom s (s.next utf8pos) p

end String

namespace Lean
namespace FileMap

private def lineStartPos (text : FileMap) (line : Nat) : String.Pos :=
  if h : line < text.positions.size then
    text.positions[line]
  else if text.positions.isEmpty then
    0
  else
    text.positions.back!

/-- Computes an UTF-8 offset into `text.source`
from an LSP-style 0-indexed (ln, col) position. -/
def lspPosToUtf8Pos (text : FileMap) (pos : Lsp.Position) : String.Pos :=
  let lineStartPos := lineStartPos text pos.line
  let chr := text.source.utf16PosToCodepointPosFrom pos.character lineStartPos
  text.source.codepointPosToUtf8PosFrom lineStartPos chr

def leanPosToLspPos (text : FileMap) : Lean.Position → Lsp.Position
  | ⟨line, col⟩ =>
    ⟨line - 1, text.source.codepointPosToUtf16PosFrom col (lineStartPos text (line - 1))⟩

def utf8PosToLspPos (text : FileMap) (pos : String.Pos) : Lsp.Position :=
  text.leanPosToLspPos (text.toPosition pos)

/-- Gets the LSP range from a `String.Range`. -/
def utf8RangeToLspRange (text : FileMap) (range : String.Range) : Lsp.Range :=
  { start := text.utf8PosToLspPos range.start, «end» := text.utf8PosToLspPos range.stop }

end FileMap
end Lean

/--
Convert the Lean `DeclarationRange` to an LSP `Range` by turning the 1-indexed line numbering into a
0-indexed line numbering and converting the character offset within the line to a UTF-16 indexed
offset.
-/
def Lean.DeclarationRange.toLspRange (r : Lean.DeclarationRange) : Lsp.Range := {
  start := ⟨r.pos.line - 1, r.charUtf16⟩
  «end» := ⟨r.endPos.line - 1, r.endCharUtf16⟩
}
