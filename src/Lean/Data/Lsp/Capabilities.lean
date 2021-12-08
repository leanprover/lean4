/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Lean.Data.JsonRpc
import Lean.Data.Lsp.TextSync
import Lean.Data.Lsp.LanguageFeatures
import Lean.Data.Lsp.SignatureHelp

/-! Minimal LSP servers/clients do not have to implement a lot
of functionality. Most useful additional behavior is instead
opted into via capabilities. -/

namespace Lean
namespace Lsp

open Json

/-- ClientCapabilities define capabilities for dynamic registration, workspace and text document features the client
  supports.-/
-- TODO: right now we ignore the client's capabilities
inductive ClientCapabilities where
  | mk

instance : FromJson ClientCapabilities :=
  ⟨fun j => ClientCapabilities.mk⟩

instance ClientCapabilities.hasToJson : ToJson ClientCapabilities :=
  ⟨fun o => mkObj []⟩

/-- The server can signal the following capabilities -/
structure ServerCapabilities where
  /-- Defines how text documents are synced.-/
  textDocumentSync? : Option TextDocumentSyncOptions := none
  /-- The server provides completion support. -/
  completionProvider? : Option CompletionOptions := none
  /-- The server provides hover support. -/
  hoverProvider : Bool := false
  /-- The server provides signature help support.-/
  signatureHelpProvider : Option SignatureHelpOptions := none
  /-- The server provides go to declaration support. -/
  declarationProvider : Bool := false
  /-- The server provides goto definition support. -/
  definitionProvider : Bool := false
  /-- The server provides goto type definition support. -/
  typeDefinitionProvider : Bool := false
  /-- The server provides document highlight support.-/
  documentHighlightProvider : Bool := false
  /-- The server provides document symbol support.-/
  documentSymbolProvider : Bool := false
  /-- The server provides semantic tokens support. -/
  semanticTokensProvider? : Option SemanticTokensOptions := none

  /- Not implemented:
  /-- The server provides goto implementation support. -/
  implementationProvider : Bool := false

  /-- The server provides find references support. -/
  referencesProvider : Bool := false

  /-- The server provides code actions. -/
  codeActionProvider: Bool := false

  /-- The server provides code lens. -/
  codeLensProvider?: CodeLensOptions;

  /-- The server provides document link support. -/
  documentLinkProvider?: DocumentLinkOptions;

  /-- The server provides color provider support. -/
  colorProvider?: ColorProviderOptions;

  /-- The server provides document formatting. -/
  documentFormattingProvider?: boolean | DocumentFormattingOptions;

  /-- The server provides document range formatting. -/
  documentRangeFormattingProvider?: boolean | DocumentRangeFormattingOptions;

  /-- The server provides document formatting on typing. -/
  documentOnTypeFormattingProvider?: boolean | DocumentOnTypeFormattingOptions;

  /-- The server provides refactor rename support. -/
  renameProvider?: boolean | RenameOptions;

  /-- The server provides document folding. -/
  foldingRangeProvider?: boolean | FoldingRangeOptions;

  /-- The server provides execute command support. -/
  executeCommandProvider?: ExecuteCommandOptions;

  /-- The server provides selection range support. -/
  selectionRangeProvider?: boolean | SelectionRangeOptions;

  /-- The server provides linked editing range support. -/
  linkedEditingRangeProvider?: boolean | LinkedEditingRangeOptions;

  /-- The server provides call hierarchy support. -/
  callHierarchyProvider?: boolean | CallHierarchyOptions;

  /-- Whether server provides moniker support. -/
  monikerProvider?: boolean | MonikerOptions;

  /-- The server provides workspace symbol support.-/
  workspaceSymbolProvider?: boolean | WorkspaceSymbolOptions;

  /-- Workspace specific server capabilities -/
  workspace?: WorkspaceServerCapabilities;

  /-- Experimental server capabilities.-/
  experimental?: ExperimentalServerCapabilities;
  -/

  deriving ToJson, FromJson

end Lsp
end Lean
