/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Lean.Data.Json
import Lean.Data.JsonRpc
import Lean.Data.Lsp.Basic

/-! This file contains Lean-specific extensions to LSP. See the structures below for which
additional requests and notifications are supported. -/

namespace Lean.Lsp
open Json

/-- `textDocument/waitForDiagnostics` client->server request.

Yields a response when all the diagnostics for a version of the document greater or equal to the
specified one have been emitted. If the request specifies a version above the most recently
processed one, the server will delay the response until it does receive the specified version.
Exists for synchronization purposes, e.g. during testing or when external tools might want to use
our LSP server. -/
structure WaitForDiagnosticsParams where
  uri     : DocumentUri
  version : Nat
  deriving FromJson, ToJson

/-- `textDocument/waitForDiagnostics` client<-server reply. -/
structure WaitForDiagnostics

instance : FromJson WaitForDiagnostics :=
  ⟨fun j => WaitForDiagnostics.mk⟩

instance : ToJson WaitForDiagnostics :=
  ⟨fun o => mkObj []⟩

structure LeanFileProgressProcessingInfo where
  range : Range
  deriving FromJson, ToJson

/-- `$/lean/fileProgress` client<-server notification.

Contains the ranges of the document that are currently being processed by the server. -/
structure LeanFileProgressParams where
  textDocument : VersionedTextDocumentIdentifier
  processing : Array LeanFileProgressProcessingInfo
  deriving FromJson, ToJson

/-- `$/lean/plainGoal` client->server request.

If there is a tactic proof at the specified position, returns the current goals.
Otherwise returns `null`. -/
structure PlainGoalParams extends TextDocumentPositionParams
  deriving FromJson, ToJson

/-- `$/lean/plainGoal` client<-server reply. -/
structure PlainGoal where
  /-- The goals as pretty-printed Markdown, or something like "no goals" if accomplished. -/
  rendered : String
  /-- The pretty-printed goals, empty if all accomplished. -/
  goals : Array String
  deriving FromJson, ToJson

/-- `$/lean/plainTermGoal` client->server request.

Returns the expected type at the specified position, pretty-printed as a string. -/
structure PlainTermGoalParams extends TextDocumentPositionParams
  deriving FromJson, ToJson

/-- `$/lean/plainTermGoal` client<-server reply. -/
structure PlainTermGoal where
  goal : String
  range : Range
  deriving FromJson, ToJson

/-- An object which RPC clients can refer to without marshalling. -/
structure RpcRef where
  /- NOTE(WN): It is important for this to be a single-field structure
  in order to deserialize as an `Object` on the JS side. -/
  p : USize
  deriving BEq, Hashable, FromJson, ToJson

instance : ToString RpcRef where
  toString r := toString r.p

/-- `$/lean/rpc/connect` client->server request.

Starts an RPC session at the given file's worker, replying with the new session ID.
Multiple sessions may be started and operating concurrently.

A session may be destroyed by the server at any time (e.g. due to a crash), in which case further
RPC requests for that session will reply with `RpcNeedsReconnect` errors. The client should discard
references held from that session and `connect` again. -/
structure RpcConnectParams where
  uri : DocumentUri
  deriving FromJson, ToJson

/-- `$/lean/rpc/connect` client<-server reply.

Indicates that an RPC connection had been made and a session started for it. -/
structure RpcConnected where
  sessionId : UInt64
  deriving FromJson, ToJson

/-- `$/lean/rpc/call` client->server request.

A request to execute a procedure bound for RPC. If an incorrect session ID is present, the server
errors with `RpcNeedsReconnect`.

Extending TDPP is weird. But in Lean, symbols exist in the context of a position within a source
file. So we need this to refer to code in the environment at that position. -/
structure RpcCallParams extends TextDocumentPositionParams where
  sessionId : UInt64
  /-- Procedure to invoke. Must be fully qualified. -/
  method : Name
  params : Json
  deriving FromJson, ToJson

/-- `$/lean/rpc/release` client->server notification.

A notification to release remote references. Should be sent by the client when it no longer needs
`RpcRef`s it has previously received from the server. Not doing so is safe but will leak memory. -/
structure RpcReleaseParams where
  uri : DocumentUri
  sessionId : UInt64
  refs : Array RpcRef
  deriving FromJson, ToJson

/-- `$/lean/rpc/keepAlive` client->server notification.

The client must send an RPC notification every 10s in order to keep the RPC session alive.
This is the simplest one. On not seeing any notifications for three 10s periods, the server
will drop the RPC session and its associated references. -/
structure RpcKeepAliveParams where
  uri : DocumentUri
  sessionId : UInt64
  deriving FromJson, ToJson

end Lean.Lsp
