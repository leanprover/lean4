import Init.Data.String
import Init.Data.Array
import Lean.Data.Lsp.Structure

-- LSP uses UTF-16 for indexing, so we need to provide some primitives
-- to interact with Lean strings using UTF-16 indices

namespace Char

def utf16Size (c : Char) : UInt32 :=
if c.val ≤ 0xFFFF then 1 else 2

end Char

namespace String

-- LSP is EOL agnostic, so we first split on "\r\n" to avoid possibly redundant line breaks
def splitOnEOLs (s : String) : List String := do
line ← s.splitOn "\r\n";
line ← line.splitOn "\n";
line ← line.splitOn "\r";
pure line

private def csize (c : Char) : Nat :=
c.utf16Size.toNat

-- HACK(WN): String.take n (unintentionally?) produces n UTF-8 bytes rather
-- than n codepoints. This function deals with codepoints instead.
def takeCodepoints (s : String) (n : Nat) : String :=
List.asString (s.toList.take n)

def codepointPosToUtf16Pos (s : String) (pos : Pos) : Nat :=
(s.takeCodepoints pos).foldr (fun ch acc => acc + csize ch) 0

private def utf16PosToCodepointPosAux : List Char → Nat → Pos → Pos
| c :: cs, 0, acc => acc
| c :: cs, n, acc => utf16PosToCodepointPosAux cs (n - csize c) (acc + 1)
| [],      _, acc => acc

def utf16PosToCodepointPos (s : String) (pos : Nat) : Pos :=
utf16PosToCodepointPosAux s.toList pos 0

def utf16Length (s : String) : Nat :=
s.foldr (fun c acc => csize c + acc) 0

-- delete text until endIdx
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
