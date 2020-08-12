/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Init.Data.String
import Init.Data.Array
import Lean.Data.Lsp.Basic

/-! LSP uses UTF-16 for indexing, so we need to provide some primitives
to interact with Lean strings using UTF-16 indices. -/

namespace Char

def utf16Size (c : Char) : UInt32 :=
if c.val ≤ 0xFFFF then 1 else 2

end Char

namespace String

/-- LSP is EOL agnostic, so we first split on "\r\n" to avoid possibly redundant line breaks. -/
def splitOnEOLs (s : String) : List String := do
line ← s.splitOn "\r\n";
line ← line.splitOn "\n";
line ← line.splitOn "\r";
pure line

private def csize (c : Char) : Nat :=
c.utf16Size.toNat

private def codepointPosToUtf16PosAux (s : String) : Nat → Pos → Nat → Nat
| 0,    utf8pos, utf16pos => utf16pos
| cp+1, utf8pos, utf16pos => codepointPosToUtf16PosAux cp (s.next utf8pos) (utf16pos + csize (s.get utf8pos))

def codepointPosToUtf16Pos (s : String) (pos : Nat) : Nat :=
codepointPosToUtf16PosAux s pos 0 0

private partial def utf16PosToCodepointPosAux (s : String) : Nat → Pos → Nat → Nat
| 0,        utf8pos, cp => cp
| utf16pos, utf8pos, cp => utf16PosToCodepointPosAux (utf16pos - csize (s.get utf8pos)) (s.next utf8pos) (cp + 1)

def utf16PosToCodepointPos (s : String) (pos : Nat) : Nat :=
utf16PosToCodepointPosAux s pos 0 0

def utf16Length (s : String) : Nat :=
s.foldr (fun c acc => csize c + acc) 0

/-- Delete text until endIdx. -/
private def utf16ReplaceAux₀ : List Char → Nat → Nat → List Char
| [],       i, endIdx => [] -- no more text to delete
| (c :: s), i, endIdx =>
  if i ≥ endIdx then
    c :: s
  else
    utf16ReplaceAux₀ s (i + csize c) endIdx

private def utf16ReplaceAux₁ : List Char → List Char → Nat → Nat → List Char
| [],     n :: new, i, endIdx => n :: new
| s,      [],       i, endIdx => utf16ReplaceAux₀ s i endIdx
| c :: s, n :: new, i, endIdx =>
  if i ≥ endIdx then
    n :: new ++ c :: s -- range ended, insert rest of the text
  else
    n :: utf16ReplaceAux₁ s new (i + csize c) endIdx

private def utf16ReplaceAux₂ : List Char → List Char → Nat → Nat → Nat → List Char
| [],     [],       i, startIdx, endIdx => []
| [],     n :: new, i, startIdx, endIdx => n :: new
| c :: s, new,      i, startIdx, endIdx =>
  if i ≥ startIdx then
    utf16ReplaceAux₁ (c :: s) new i endIdx
  else
    c :: utf16ReplaceAux₂ s new (i + csize c) startIdx endIdx

def utf16Replace (s new : String) (a b : Nat) : String :=
⟨utf16ReplaceAux₂ s.data new.data 0 a b⟩

end String

namespace Array

def insertAll {α} (as : Array α) (i : Nat) (as' : Array α) : Array α :=
as'.foldr (fun a' acc => acc.insertAt i a') as

def eraseAll {α} (as : Array α) (i n : Nat) : Array α :=
n.repeat (fun acc => acc.eraseIdx i) as

end Array

namespace Lean
namespace Lsp

def replaceRange (text : DocumentText) (r : Range) (newText : String) : DocumentText :=
let sl := r.start.line;
let si := r.start.character;
let el := r.«end».line;
let ei := r.«end».character;
let focused := text.extract sl (el+1);
let lastFocusedLine := focused.size - 1;
let endIdx := focused.iterateRev 0 $ fun lineIdx line endIdxAcc =>
  if lineIdx.val ≠ lastFocusedLine then
    endIdxAcc + line.utf16Length + 1 -- +1 to account for '\n' after intercalating `focused`
  else
    endIdxAcc + ei;
let focused := "\n".intercalate focused.toList;
let replaced := (focused.utf16Replace newText si endIdx).splitOnEOLs.toArray;
(text.eraseAll sl (el - sl + 1)).insertAll sl replaced

end Lsp
end Lean
