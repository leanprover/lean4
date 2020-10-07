import Lean.Data.Position
import Lean.Data.Lsp

namespace Lean
namespace Server

def replaceLspRange (text : FileMap) (r : Lsp.Range) (newText : String) : FileMap :=
let start := text.lspPosToUtf8Pos r.start;
let «end» := text.lspPosToUtf8Pos r.«end»;
let pre := text.source.extract 0 start;
let post := text.source.extract «end» text.source.bsize;
(pre ++ newText ++ post).toFileMap

open Lsp

/-- Returns the document contents with all changes applied, together with the position of the change
which lands earliest in the file. Panics if there are no changes. -/
def foldDocumentChanges (changes : @& Array Lsp.TextDocumentContentChangeEvent) (oldText : FileMap)
  : FileMap × String.Pos :=
if changes.isEmpty then panic! "Lean.Server.foldDocumentChanges: empty change array" else
let accumulateChanges : TextDocumentContentChangeEvent → FileMap × String.Pos → FileMap × String.Pos :=
  fun change ⟨newDocText, minStartOff⟩ =>
    match change with
    | TextDocumentContentChangeEvent.rangeChange (range : Range) (newText : String) =>
      let startOff    := oldText.lspPosToUtf8Pos range.start;
      let newDocText  := replaceLspRange newDocText range newText;
      let minStartOff := minStartOff.min startOff;
      ⟨newDocText, minStartOff⟩
    | TextDocumentContentChangeEvent.fullChange (newText : String) =>
      ⟨newText.toFileMap, 0⟩;
-- NOTE: We assume Lean files are below 16 EiB.
changes.foldr accumulateChanges (oldText, 0xffffffff)

-- TODO(WN): should these instances be in Core?
instance Thunk.monad : Monad Thunk :=
{ pure := @Thunk.pure,
  bind := @Thunk.bind }

end Server
end Lean
