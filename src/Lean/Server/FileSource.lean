/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga
-/
prelude
import Lean.Data.Lsp

namespace Lean.Lsp

class FileSource (α : Type) where
  fileSource : α → DocumentUri
export FileSource (fileSource)

instance : FileSource Location :=
  ⟨fun l => l.uri⟩

instance : FileSource TextDocumentIdentifier :=
  ⟨fun i => i.uri⟩

instance : FileSource VersionedTextDocumentIdentifier :=
  ⟨fun i => i.uri⟩

instance : FileSource TextDocumentEdit :=
  ⟨fun e => fileSource e.textDocument⟩

instance : FileSource TextDocumentItem :=
  ⟨fun i => i.uri⟩

instance : FileSource TextDocumentPositionParams :=
  ⟨fun p => fileSource p.textDocument⟩

instance : FileSource DidOpenTextDocumentParams :=
  ⟨fun p => fileSource p.textDocument⟩

instance : FileSource DidChangeTextDocumentParams :=
  ⟨fun p => fileSource p.textDocument⟩

instance : FileSource DidSaveTextDocumentParams :=
  ⟨fun p => fileSource p.textDocument⟩

instance : FileSource DidCloseTextDocumentParams :=
  ⟨fun p => fileSource p.textDocument⟩

instance : FileSource CompletionParams :=
  ⟨fun h => fileSource h.toTextDocumentPositionParams⟩

instance : FileSource HoverParams :=
  ⟨fun h => fileSource h.toTextDocumentPositionParams⟩

instance : FileSource DeclarationParams :=
  ⟨fun h => fileSource h.toTextDocumentPositionParams⟩

instance : FileSource DefinitionParams :=
  ⟨fun h => fileSource h.toTextDocumentPositionParams⟩

instance : FileSource TypeDefinitionParams :=
  ⟨fun h => fileSource h.toTextDocumentPositionParams⟩

instance : FileSource ReferenceParams :=
  ⟨fun h => fileSource h.toTextDocumentPositionParams⟩

instance : FileSource WaitForDiagnosticsParams :=
  ⟨fun p => p.uri⟩

instance : FileSource DocumentHighlightParams :=
  ⟨fun h => fileSource h.toTextDocumentPositionParams⟩

instance : FileSource DocumentSymbolParams :=
  ⟨fun p => fileSource p.textDocument⟩

instance : FileSource SemanticTokensParams :=
  ⟨fun p => fileSource p.textDocument⟩

instance : FileSource SemanticTokensRangeParams :=
  ⟨fun p => fileSource p.textDocument⟩

instance : FileSource FoldingRangeParams :=
  ⟨fun p => fileSource p.textDocument⟩

instance : FileSource PlainGoalParams :=
  ⟨fun p => fileSource p.textDocument⟩

instance : FileSource PlainTermGoalParams where
  fileSource p := fileSource p.textDocument

instance : FileSource RpcConnectParams where
  fileSource p := p.uri

instance : FileSource RpcCallParams where
  fileSource p := fileSource p.textDocument

instance : FileSource RpcReleaseParams where
  fileSource p := p.uri

instance : FileSource RpcKeepAliveParams where
  fileSource p := p.uri

instance : FileSource CodeActionParams where
  fileSource p := fileSource p.textDocument

instance : FileSource InlayHintParams where
  fileSource p := fileSource p.textDocument

end Lean.Lsp
