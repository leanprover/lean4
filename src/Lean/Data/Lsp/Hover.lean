import Lean.Data.Json
import Lean.Data.Lsp.Structure

namespace Lean.Lsp

open Lean
open Lean.Json

/- The result of a hover request. -/
structure Hover :=
/- The hover's content -/
--(contents: MarkedString | MarkedString[] | MarkupContent)
/- An optional range is a range inside a text document
that is used to visualize a hover, e.g. by changing the background color. -/
(range? : Range)

structure HoverParams extends TextDocumentPositionParams

instance hoverParamsHasFromJson : HasFromJson HoverParams :=
⟨fun j => do
  tdpp : TextDocumentPositionParams ← fromJson? j;
  pure ⟨tdpp⟩⟩

end Lean.Lsp

