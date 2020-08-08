import Lean.Data.Json
import Lean.Data.Lsp.Basic

/-! Handling of mouse hover requests. -/

namespace Lean
namespace Lsp

open Json

structure Hover :=
/- NOTE we should also accept MarkedString/MarkedString[] here
but they are deprecated, so maybe can get away without. -/
(contents : MarkupContent)
(range? : Option Range := none)

instance Hover.hasFromJson : HasFromJson Hover :=
⟨fun j => do
  contents ← j.getObjValAs? MarkupContent "contents";
  let range? := j.getObjValAs? Range "range";
  pure ⟨contents, range?⟩⟩

instance Hover.hasToJson : HasToJson Hover :=
⟨fun o => mkObj $
  ⟨"contents", toJson o.contents⟩ ::
  opt "range" o.range?⟩

structure HoverParams extends TextDocumentPositionParams

instance HoverParams.hasFromJson : HasFromJson HoverParams :=
⟨fun j => do
  tdpp ← @fromJson? TextDocumentPositionParams _ j;
  pure ⟨tdpp⟩⟩

instance HoverParams.hasToJson : HasToJson HoverParams :=
⟨fun o => toJson o.toTextDocumentPositionParams⟩

end Lsp
end Lean
