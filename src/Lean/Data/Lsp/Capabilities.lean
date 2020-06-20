import Lean.Data.JsonRpc
import Lean.Data.Lsp.TextSync

namespace Lean.Lsp

open Lean
open Lean.Json
open Lean.JsonRpc

-- TODO: right now we ignore the capabilities
inductive ClientCapabilities | mk

-- largely unimplemented
structure ServerCapabilities :=
(textDocumentSync? : Option TextDocumentSyncOptions := none)

def mkLeanServerCapabilities : ServerCapabilities :=
{textDocumentSync? := some {openClose := true, change? := TextDocumentSyncKind.incremental}}

instance clientCapabilitiesHasFromJson : HasFromJson ClientCapabilities :=
⟨fun j => ClientCapabilities.mk⟩

instance serverCapabilitiesHasToJson : HasToJson ServerCapabilities :=
⟨fun o => mkObj $
  opt "textDocumentSync" o.textDocumentSync? ++ []⟩

end Lean.Lsp
