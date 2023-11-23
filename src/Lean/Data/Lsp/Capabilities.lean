/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Lean.Data.JsonRpc
import Lean.Data.Lsp.TextSync
import Lean.Data.Lsp.LanguageFeatures
import Lean.Data.Lsp.CodeActions

/-! Minimal LSP servers/clients do not have to implement a lot
of functionality. Most useful additional behavior is instead
opted into via capabilities. -/

namespace Lean
namespace Lsp

open Json

structure CompletionItemCapabilities where
  insertReplaceSupport? : Option Bool := none
  deriving ToJson, FromJson

structure CompletionClientCapabilities where
  completionItem? : Option CompletionItemCapabilities := none
  deriving ToJson, FromJson

structure TextDocumentClientCapabilities where
  completion? : Option CompletionClientCapabilities := none
  codeAction? : Option CodeActionClientCapabilities := none
  deriving ToJson, FromJson

structure ShowDocumentClientCapabilities where
  support : Bool
  deriving ToJson, FromJson

structure WindowClientCapabilities where
  showDocument? : Option ShowDocumentClientCapabilities := none
  deriving ToJson, FromJson

structure ChangeAnnotationSupport where
  groupsOnLabel? : Option Bool := none
  deriving ToJson, FromJson

structure WorkspaceEditClientCapabilities where
  /-- The client supports versioned document changes in `WorkspaceEdit`s. -/
  documentChanges?         : Option Bool := none
  /--  Whether the client in general supports change annotations on text edits. -/
  changeAnnotationSupport? : Option ChangeAnnotationSupport := none
  /-- The resource operations the client supports. Clients should at least support 'create', 'rename' and 'delete' files and folders. -/
  resourceOperations?      : Option (Array String) := none
  deriving ToJson, FromJson

structure WorkspaceClientCapabilities where
  applyEdit: Bool
  workspaceEdit? : Option WorkspaceEditClientCapabilities := none
  deriving ToJson, FromJson

structure ClientCapabilities where
  textDocument? : Option TextDocumentClientCapabilities := none
  window?       : Option WindowClientCapabilities       := none
  workspace?    : Option WorkspaceClientCapabilities    := none
  deriving ToJson, FromJson

-- TODO largely unimplemented
structure ServerCapabilities where
  textDocumentSync?         : Option TextDocumentSyncOptions := none
  completionProvider?       : Option CompletionOptions       := none
  hoverProvider             : Bool                           := false
  documentHighlightProvider : Bool                           := false
  documentSymbolProvider    : Bool                           := false
  definitionProvider        : Bool                           := false
  declarationProvider       : Bool                           := false
  typeDefinitionProvider    : Bool                           := false
  referencesProvider        : Bool                           := false
  renameProvider?           : Option RenameOptions           := none
  workspaceSymbolProvider   : Bool                           := false
  foldingRangeProvider      : Bool                           := false
  semanticTokensProvider?   : Option SemanticTokensOptions   := none
  codeActionProvider?       : Option CodeActionOptions       := none
  deriving ToJson, FromJson

end Lsp
end Lean
