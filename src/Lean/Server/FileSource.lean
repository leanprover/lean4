/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga
-/
import Lean.Data.Lsp

namespace Lean
namespace Lsp

class FileSource (α : Type) :=
  (fileSource : α → DocumentUri)
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

instance HoverParams.hasFileSource : FileSource HoverParams :=
  ⟨fun h => fileSource h.toTextDocumentPositionParams⟩

end Lsp
end Lean
