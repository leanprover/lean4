/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga
-/
import Lean.Data.Json
import Lean.Data.JsonRpc
import Lean.Data.Lsp.Basic

/-!
This file contains Lean-specific extensions to LSP.
The following additional requests and notifications are supported:

- `textDocument/waitForDiagnostics`: Yields a response when all the diagnostics for a version of the document
  greater or equal to the specified one have been emitted. If the request specifies a version above the most
  recently processed one, the server will delay the response until it does receive the specified version.
  Exists for synchronization purposes, e.g. during testing or when external tools might want to use our LSP server.

- `$/lean/fileProgress`: Notification that contains the ranges of the document that are still being processed
  by the server.

- `$/lean/plainGoal`: Returns the goal(s) at the specified position, pretty-printed as a string.
-/

namespace Lean.Lsp

open Json

structure WaitForDiagnosticsParams where
  uri     : DocumentUri
  version : Nat
  deriving ToJson, FromJson

structure WaitForDiagnostics

instance : FromJson WaitForDiagnostics :=
  ⟨fun j => WaitForDiagnostics.mk⟩

instance : ToJson WaitForDiagnostics :=
  ⟨fun o => mkObj []⟩

structure LeanFileProgressProcessingInfo where
  range : Range
  deriving FromJson, ToJson

structure LeanFileProgressParams where
  textDocument : VersionedTextDocumentIdentifier
  processing : Array LeanFileProgressProcessingInfo
  deriving FromJson, ToJson

structure PlainGoalParams extends TextDocumentPositionParams
  deriving FromJson, ToJson

structure PlainGoal where
  rendered : String
  goals : Array String
  deriving FromJson, ToJson

structure PlainTermGoalParams extends TextDocumentPositionParams
  deriving FromJson, ToJson

structure PlainTermGoal where
  goal : String
  range : Range
  deriving FromJson, ToJson

end Lean.Lsp
