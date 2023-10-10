/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Init.Data.String
import Init.Data.Array
import Lean.Data.Lsp.Basic
import Lean.Data.Lsp.PositionEncodingKind
import Lean.Data.Position


/-! LSP uses UTF-16 for indexing, so we need to provide some primitives
to interact with Lean strings using UTF-16 indices. -/

namespace Char

def utf16Size (c : Char) : UInt32 :=
  if c.val ≤ 0xFFFF then 1 else 2

end Char

namespace String

private def csize32 (_ : Char) : Nat :=
  1

private def csize16 (c : Char) : Nat :=
  c.utf16Size.toNat

private def csize8 (c : Char) : Nat :=
  c.utf8Size.toNat

def utf16Length (s : String) : Nat :=
  s.foldr (fun c acc => csize16 c + acc) 0

private def codepointPosToUtf32PosFromAux (s : String) : Nat → Pos → Nat → Nat
  | 0,    _,       utf32pos => utf32pos
  | cp+1, utf8pos, utf32pos => codepointPosToUtf32PosFromAux s cp (s.next utf8pos) (utf32pos + 1)

/-- Computes the UTF-32 offset of the `n`-th Unicode codepoint
in the substring of `s` starting at UTF-8 offset `off`.
Yes, this is actually useful.-/
def codepointPosToUtf32PosFrom (s : String) (n : Nat) (off : Pos) : Nat :=
  codepointPosToUtf32PosFromAux s n off 0

private def codepointPosToUtf16PosFromAux (s : String) : Nat → Pos → Nat → Nat
  | 0,    _,       utf16pos => utf16pos
  | cp+1, utf8pos, utf16pos => codepointPosToUtf16PosFromAux s cp (s.next utf8pos) (utf16pos + csize16 (s.get utf8pos))

/-- Computes the UTF-16 offset of the `n`-th Unicode codepoint
in the substring of `s` starting at UTF-8 offset `off`.
Yes, this is actually useful.-/
def codepointPosToUtf16PosFrom (s : String) (n : Nat) (off : Pos) : Nat :=
  codepointPosToUtf16PosFromAux s n off 0

private def codepointPosToUtf8PosFromAux (s : String) : Nat → Pos → Nat → Nat
  | 0,    _,       utf8pos => utf8pos
  | cp+1, utf8pos, utf8pos' => codepointPosToUtf16PosFromAux s cp (s.next utf8pos) (utf8pos' + csize16 (s.get utf8pos))

/-- Computes the UTF-8 offset of the `n`-th Unicode codepoint
in the substring of `s` starting at UTF-8 offset `off`.
Yes, this is actually useful.-/
def codepointPosToUtf8PosFrom (s : String) (n : Nat) (off : Pos) : Nat :=
  codepointPosToUtf8PosFromAux s n off 0

def codepointPosToUtf16Pos (s : String) (pos : Nat) : Nat :=
  codepointPosToUtf16PosFrom s pos 0

def codepointPosToLspPosFrom (encoding : Lean.Lsp.PositionEncodingKind) (s : String) (n : Nat) (off : Pos) : Nat :=
  match encoding with
  | .utf32 => codepointPosToUtf32PosFrom s n off
  | .utf16 => codepointPosToUtf16PosFrom s n off
  | .utf8 => codepointPosToUtf8PosFrom s n off

-- TODO get rid of this loop and use division here once everything works

private partial def utf32PosToCodepointPosFromAux (s : String) : Nat → Pos → Nat → Nat
  | 0,        _,       cp => cp
  | utf32pos, utf8pos, cp => utf32PosToCodepointPosFromAux s (utf32pos - csize32 (s.get utf8pos)) (s.next utf8pos) (cp + 1)

/-- Computes the position of the Unicode codepoint at UTF-32 offset
`utf32pos` in the substring of `s` starting at UTF-8 offset `off`. -/
def utf32PosToCodepointPosFrom (s : String) (utf32pos : Nat) (off : Pos) : Nat :=
  utf32PosToCodepointPosFromAux s utf32pos off 0


private partial def utf16PosToCodepointPosFromAux (s : String) : Nat → Pos → Nat → Nat
  | 0,        _,       cp => cp
  | utf16pos, utf8pos, cp => utf16PosToCodepointPosFromAux s (utf16pos - csize16 (s.get utf8pos)) (s.next utf8pos) (cp + 1)

/-- Computes the position of the Unicode codepoint at UTF-16 offset
`utf16pos` in the substring of `s` starting at UTF-8 offset `off`. -/
def utf16PosToCodepointPosFrom (s : String) (utf16pos : Nat) (off : Pos) : Nat :=
  utf16PosToCodepointPosFromAux s utf16pos off 0

private partial def utf8PosToCodepointPosFromAux (s : String) : Nat → Pos → Nat → Nat
  | 0,        _,       cp => cp
  | utf16pos, utf8pos, cp => utf16PosToCodepointPosFromAux s (utf16pos - csize8 (s.get utf8pos)) (s.next utf8pos) (cp + 1)

/-- Computes the position of the Unicode codepoint at UTF-8 offset
`utf8pos` in the substring of `s` starting at UTF-8 offset `off`. -/
def utf8PosToCodepointPosFrom (s : String) (utf8pos : Nat) (off : Pos) : Nat :=
  utf8PosToCodepointPosFromAux s utf8pos off 0


def utf32PosToCodepointPos (s : String) (pos : Nat) : Nat :=
  utf32PosToCodepointPosFrom s pos 0

def utf16PosToCodepointPos (s : String) (pos : Nat) : Nat :=
  utf16PosToCodepointPosFrom s pos 0

def utf8PosToCodepointPos (s : String) (pos : Nat) : Nat :=
  utf8PosToCodepointPosFrom s pos 0

/-- Starting at `utf8pos`, finds the UTF-8 offset of the `p`-th codepoint. -/
def codepointPosToStringPosFrom (s : String) : String.Pos → Nat → String.Pos
  | utf8pos, 0 => utf8pos
  | utf8pos, p+1 => codepointPosToStringPosFrom s (s.next utf8pos) p

end String

namespace Lean
namespace FileMap

/-- Computes an UTF-8 offset into `text.source`
from an LSP-style 0-indexed (ln, col) position. -/
def lspPosToUtf8Pos (text : FileMap) (encoding : Lsp.PositionEncodingKind) (pos : Lsp.Position) : String.Pos :=
  let colPos :=
    if h : pos.line < text.positions.size then
      text.positions.get ⟨pos.line, h⟩
    else if text.positions.isEmpty then
      0
    else
      text.positions.back
  let chr := match encoding with
    | .utf32 => text.source.utf32PosToCodepointPosFrom pos.character colPos
    | .utf16 => text.source.utf16PosToCodepointPosFrom pos.character colPos
    | .utf8 => text.source.utf8PosToCodepointPosFrom pos.character colPos
  text.source.codepointPosToStringPosFrom colPos chr

def leanPosToLspPos (text : FileMap) : Lean.Position → Lsp.EncodedPosition
  | ⟨ln, col⟩ => {
    line := ln-1
    characterUtf8 := text.source.codepointPosToLspPosFrom .utf8 col (text.positions.get! $ ln - 1),
    characterUtf16 := text.source.codepointPosToLspPosFrom .utf16 col (text.positions.get! $ ln - 1),
    characterUtf32 := text.source.codepointPosToLspPosFrom .utf32 col (text.positions.get! $ ln - 1)
  }

def leanPosToEncodedLspPos (text : FileMap) (encoding : Lsp.PositionEncodingKind) : Lean.Position → Lsp.Position
  | ⟨ln, col⟩ => {
    line := ln-1
    character := text.source.codepointPosToLspPosFrom encoding col (text.positions.get! $ ln - 1)
  }

def utf8PosToLspPos (text : FileMap) (pos : String.Pos) : Lsp.EncodedPosition :=
  text.leanPosToLspPos (text.toPosition pos)

def utf8PosToEncodedLspPos (text : FileMap) (encoding : Lsp.PositionEncodingKind) (pos : String.Pos) : Lsp.Position :=
  text.leanPosToEncodedLspPos encoding (text.toPosition pos)

end FileMap
end Lean
