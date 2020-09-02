/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga
-/
import Lean.Data.Lsp

namespace Lean
namespace Lsp

class HasFileSource (α : Type*) := 
(fileSource : α → DocumentUri)
export HasFileSource (fileSource)

instance Location.hasFileSource : HasFileSource Location :=
⟨fun l => l.uri⟩

instance TextDocumentIdentifier.hasFileSource : HasFileSource TextDocumentIdentifier :=
⟨fun i => i.uri⟩

instance VersionedTextDocumentIdentifier.hasFileSource : HasFileSource VersionedTextDocumentIdentifier :=
⟨fun i => i.uri⟩

instance TextDocumentEdit.hasFileSource : HasFileSource TextDocumentEdit :=
⟨fun e => fileSource e.textDocument⟩

instance TextDocumentItem.hasFileSource : HasFileSource TextDocumentItem :=
⟨fun i => i.uri⟩

instance TextDocumentPositionParams.hasFileSource : HasFileSource TextDocumentPositionParams :=
⟨fun p => fileSource p.textDocument⟩

instance DidOpenTextDocumentParams.hasFileSource : HasFileSource DidOpenTextDocumentParams :=
⟨fun p => fileSource p.textDocument⟩

instance DidChangeTextDocumentParams.hasFileSource : HasFileSource DidChangeTextDocumentParams :=
⟨fun p => fileSource p.textDocument⟩

instance DidCloseTextDocumentParams.hasFileSource : HasFileSource DidCloseTextDocumentParams :=
⟨fun p => fileSource p.textDocument⟩

instance HoverParams.hasFileSource : HasFileSource HoverParams :=
⟨fun h => fileSource h.toTextDocumentPositionParams⟩

end Lsp
end Lean
