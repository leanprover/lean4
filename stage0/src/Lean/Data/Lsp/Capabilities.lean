/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Lean.Data.JsonRpc
import Lean.Data.Lsp.TextSync

/-! Minimal LSP servers/clients do not have to implement a lot
of functionality. Most useful additional behaviour is instead
opted into via capabilities. -/

namespace Lean
namespace Lsp

open Json

-- TODO: right now we ignore the client's capabilities
inductive ClientCapabilities where
  | mk

instance : FromJson ClientCapabilities :=
  ⟨fun j => ClientCapabilities.mk⟩

instance ClientCapabilities.hasToJson : ToJson ClientCapabilities :=
  ⟨fun o => mkObj []⟩

-- TODO largely unimplemented
structure ServerCapabilities where
  textDocumentSync? : Option TextDocumentSyncOptions := none
  hoverProvider : Bool := false
  deriving ToJson, FromJson

end Lsp
end Lean
