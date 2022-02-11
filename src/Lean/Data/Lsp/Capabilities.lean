/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Lean.Data.JsonRpc
import Lean.Data.Lsp.TextSync
import Lean.Data.Lsp.LanguageFeatures

/-! Minimal LSP servers/clients do not have to implement a lot
of functionality. Most useful additional behavior is instead
opted into via capabilities. -/

namespace Lean
namespace Lsp

open Json

structure CompletionItemCapabilities where
  insertReplaceSupport? : Option Bool
  deriving ToJson, FromJson

structure CompletionClientCapabilities where
  completionItem? : Option CompletionItemCapabilities
  deriving ToJson, FromJson

structure TextDocumentClientCapabilities where
  completion? : Option CompletionClientCapabilities
  deriving ToJson, FromJson

structure ClientCapabilities where
  textDocument? : Option TextDocumentClientCapabilities
  deriving ToJson, FromJson

-- TODO largely unimplemented
structure ServerCapabilities where
  textDocumentSync? : Option TextDocumentSyncOptions := none
  completionProvider? : Option CompletionOptions := none
  hoverProvider : Bool := false
  documentHighlightProvider : Bool := false
  documentSymbolProvider : Bool := false
  definitionProvider : Bool := false
  declarationProvider : Bool := false
  typeDefinitionProvider : Bool := false
  referencesProvider : Bool := false
  workspaceSymbolProvider : Bool := false
  foldingRangeProvider : Bool := false
  semanticTokensProvider? : Option SemanticTokensOptions := none
  deriving ToJson, FromJson

end Lsp
end Lean
