import Lean.Data.JsonRpc
import Lean.Data.Lsp.TextSync

namespace Lean.Lsp

open Lean
open Lean.Json
open Lean.JsonRpc

-- TODO: right now we ignore the client's capabilities
inductive ClientCapabilities | mk

instance clientCapabilitiesHasFromJson : HasFromJson ClientCapabilities :=
⟨fun j => ClientCapabilities.mk⟩

-- TODO largely unimplemented
structure ServerCapabilities :=
(textDocumentSync? : Option TextDocumentSyncOptions := none)
(hoverProvider : Bool := false)

instance serverCapabilitiesHasToJson : HasToJson ServerCapabilities :=
⟨fun o => mkObj $
  opt "textDocumentSync" o.textDocumentSync? ++
  [⟨"hoverProvider", o.hoverProvider⟩]⟩

def mkLeanServerCapabilities : ServerCapabilities :=
{ textDocumentSync? := some
  { openClose := true
  , change? := TextDocumentSyncKind.incremental }
, hoverProvider := true }

end Lean.Lsp
