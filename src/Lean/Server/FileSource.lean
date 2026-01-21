/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga
-/
module

prelude
public import Lean.Data.Lsp

public section

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

instance : FileSource SignatureHelpParams where
  fileSource p := fileSource p.textDocument

instance : FileSource DocumentColorParams where
  fileSource p := fileSource p.textDocument

/--
Yields the file source of `item` by attempting to obtain `mod : Name` from `item.data?`. \
Panics if `item.data?` is not present or does not contain a `mod` field and the first element of a
`data?` array cannot be parsed to `Name`.
Used when `completionItem/resolve` requests pass the watchdog to decide which file worker to forward
the request to.
Since this function can panic and clients typically send `completionItem/resolve` requests for every
selected completion item, all completion items returned by the server in `textDocument/completion`
requests must have a `data?` field that has a `mod` field.
-/
def CompletionItem.getFileSource! (item : CompletionItem) : DocumentUri :=
  let r : Except String DocumentUri := do
    let some data := item.data?
      | throw s!"no data param on completion item {item.label}"
    match data with
    | .obj _ =>
      -- In the language server, `data` is always an array,
      -- but we also support having `uri` as an object field for
      -- `chainLspRequestHandler` consumers.
      let uri ← data.getObjValAs? DocumentUri "uri"
      return uri
    | .arr _ =>
      let uri ← fromJson? <| ← data.getArrVal? 0
      return uri
    | _ =>
      throw s!"unexpected completion item data: {data}"
  match r with
  | Except.ok id => id
  | Except.error e => panic! e

instance : FileSource CompletionItem where
  fileSource := CompletionItem.getFileSource!

end Lean.Lsp
