/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga
-/
import Lean.Data.Lsp

namespace Lean
namespace Lsp

class FileSource (α : Type) where
  fileSource : α → DocumentUri
export FileSource (fileSource)

instance Location.hasFileSource : FileSource Location :=
  ⟨fun l => l.uri⟩

instance TextDocumentIdentifier.hasFileSource : FileSource TextDocumentIdentifier :=
  ⟨fun i => i.uri⟩

instance VersionedTextDocumentIdentifier.hasFileSource : FileSource VersionedTextDocumentIdentifier :=
  ⟨fun i => i.uri⟩

instance TextDocumentEdit.hasFileSource : FileSource TextDocumentEdit :=
  ⟨fun e => fileSource e.textDocument⟩

instance TextDocumentItem.hasFileSource : FileSource TextDocumentItem :=
  ⟨fun i => i.uri⟩

instance TextDocumentPositionParams.hasFileSource : FileSource TextDocumentPositionParams :=
  ⟨fun p => fileSource p.textDocument⟩

instance DidOpenTextDocumentParams.hasFileSource : FileSource DidOpenTextDocumentParams :=
  ⟨fun p => fileSource p.textDocument⟩

instance DidChangeTextDocumentParams.hasFileSource : FileSource DidChangeTextDocumentParams :=
  ⟨fun p => fileSource p.textDocument⟩

instance DidCloseTextDocumentParams.hasFileSource : FileSource DidCloseTextDocumentParams :=
  ⟨fun p => fileSource p.textDocument⟩

instance CompletionParams.hasFileSource : FileSource CompletionParams :=
  ⟨fun h => fileSource h.toTextDocumentPositionParams⟩

instance HoverParams.hasFileSource : FileSource HoverParams :=
  ⟨fun h => fileSource h.toTextDocumentPositionParams⟩

instance DeclarationParams.hasFileSource : FileSource DeclarationParams :=
  ⟨fun h => fileSource h.toTextDocumentPositionParams⟩

instance DefinitionParams.hasFileSource : FileSource DefinitionParams :=
  ⟨fun h => fileSource h.toTextDocumentPositionParams⟩

instance TypeDefinitionParams.hasFileSource : FileSource TypeDefinitionParams :=
  ⟨fun h => fileSource h.toTextDocumentPositionParams⟩

instance WaitForDiagnosticsParams.hasFileSource : FileSource WaitForDiagnosticsParams :=
  ⟨fun p => p.uri⟩

instance DocumentHighlightParams.hasFileSource : FileSource DocumentHighlightParams :=
  ⟨fun h => fileSource h.toTextDocumentPositionParams⟩

instance DocumentSymbolParams.hasFileSource : FileSource DocumentSymbolParams :=
  ⟨fun p => fileSource p.textDocument⟩

instance SemanticTokensParams.hasFileSource : FileSource SemanticTokensParams :=
  ⟨fun p => fileSource p.textDocument⟩

instance SemanticTokensRangeParams.hasFileSource : FileSource SemanticTokensRangeParams :=
  ⟨fun p => fileSource p.textDocument⟩

instance PlainGoalParams.hasFileSource : FileSource PlainGoalParams :=
  ⟨fun p => fileSource p.textDocument⟩

instance : FileSource PlainTermGoalParams where
  fileSource p := fileSource p.textDocument

end Lsp
end Lean
