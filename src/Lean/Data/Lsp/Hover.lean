import Lean.Data.Json
import Lean.Data.Lsp.Basic

namespace Lean
namespace Lsp

open Json

/- The result of a hover request. -/
structure Hover :=
/- The hover's content -/
--(contents: MarkedString | MarkedString[] | MarkupContent)
/- An optional range is a range inside a text document
that is used to visualize a hover, e.g. by changing the background color. -/
(range? : Option Range := none)

structure HoverParams extends TextDocumentPositionParams

instance hoverParamsHasFromJson : HasFromJson HoverParams :=
⟨fun j => do
  tdpp : TextDocumentPositionParams ← fromJson? j;
  pure ⟨tdpp⟩⟩

end Lsp
end Lean
