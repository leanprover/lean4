/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Lean.Data.Lsp
import Lean.Language.HashLang
import Lean.Server.FileWorker.Utils
import Lean.Server.ImportCompletion

namespace Lean.Server.FileWorker

/-- A document editable in the sense that we track the environment
and parser state after each command so that edits can be applied
without recompiling code appearing earlier in the file. -/
structure EditableDocument where
  meta       : DocumentMeta
  /-- State snapshots after header and each command. -/
  -- TODO: generalize to other languages by moving request handlers into `Language`
  initSnap : (Language.hashLang .Lean).InitialSnapshot
  /--
    Task reporting processing status back to client. We store it here for implementing
    `waitForDiagnostics`. -/
  reporter : Task Unit

namespace EditableDocument

/-- Construct a VersionedTextDocumentIdentifier from an EditableDocument --/
def versionedIdentifier (ed : EditableDocument) : Lsp.VersionedTextDocumentIdentifier := {
  uri := ed.meta.uri
  version? := some ed.meta.version
}

end EditableDocument

structure WorkerContext where
  /-- Synchronized output channel for LSP messages. Notifications for outdated versions are
    discarded on read. -/
  chanOut          : IO.Channel JsonRpc.Message
  hLog             : IO.FS.Stream
  initParams       : Lsp.InitializeParams
  processor        : Parser.InputContext → BaseIO (Language.hashLang .Lean).InitialSnapshot
  clientHasWidgets : Bool

-- Pending requests are tracked so they can be canceled
abbrev PendingRequestMap := RBMap JsonRpc.RequestID (Task (Except IO.Error Unit)) compare

structure AvailableImportsCache where
  availableImports       : ImportCompletion.AvailableImports
  lastRequestTimestampMs : Nat

structure WorkerState where
  doc                : EditableDocument
  importCachingTask? : Option (Task (Except IO.Error AvailableImportsCache))
  pendingRequests    : PendingRequestMap
  /-- A map of RPC session IDs. We allow asynchronous elab tasks and request handlers
  to modify sessions. A single `Ref` ensures atomic transactions. -/
  rpcSessions        : RBMap UInt64 (IO.Ref RpcSession) compare

abbrev WorkerM := ReaderT WorkerContext <| StateRefT WorkerState IO
