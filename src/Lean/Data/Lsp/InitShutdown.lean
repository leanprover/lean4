/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
prelude
import Lean.Data.Lsp.Capabilities
import Lean.Data.Lsp.Workspace
import Lean.Data.Json

/-! Functionality to do with initializing and shutting down
the server ("General Messages" section of LSP spec). -/

namespace Lean
namespace Lsp

open Json

structure ClientInfo where
  name : String
  version? : Option String := none
  deriving ToJson, FromJson

/--
A TraceValue represents the level of verbosity with which the server systematically reports its execution trace using `$/logTrace` notifications.
[reference](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#traceValue)
-/
inductive Trace where
  | off
  | messages
  | verbose

instance : FromJson Trace := ⟨fun j =>
  match j.getStr? with
  | Except.ok "off"      => return Trace.off
  | Except.ok "messages" => return Trace.messages
  | Except.ok "verbose"  => return Trace.verbose
  | _               => throw "unknown trace"⟩

instance Trace.hasToJson : ToJson Trace :=
⟨fun
  | Trace.off => "off"
  | Trace.messages => "messages"
  | Trace.verbose => "verbose"⟩

/-- Lean-specific initialization options. -/
structure InitializationOptions where
  /-- Time (in milliseconds) which must pass since latest edit until elaboration begins. Lower
  values may make editors feel faster at the cost of higher CPU usage. Defaults to 200ms. -/
  editDelay? : Option Nat
  /-- Whether the client supports interactive widgets. When true, in order to improve performance
  the server may cease including information which can be retrieved interactively in some standard
  LSP messages. Defaults to false. -/
  hasWidgets? : Option Bool
  deriving ToJson, FromJson

structure InitializeParams where
  processId? : Option Int := none
  clientInfo? : Option ClientInfo := none
  /- We don't support the deprecated rootPath
  (rootPath? : Option String) -/
  rootUri? : Option String := none
  initializationOptions? : Option InitializationOptions := none
  capabilities : ClientCapabilities
  /-- If omitted, we default to off. -/
  trace : Trace := Trace.off
  workspaceFolders? : Option (Array WorkspaceFolder) := none
  deriving ToJson

def InitializeParams.editDelay (params : InitializeParams) : Nat :=
  params.initializationOptions? |>.bind (·.editDelay?) |>.getD 200

instance : FromJson InitializeParams where
  fromJson? j := do
    /- Many of these params can be null instead of not present.
    For ease of implementation, we're liberal:
    missing params, wrong json types and null all map to none,
    even if LSP sometimes only allows some subset of these.
    In cases where LSP makes a meaningful distinction
    between different kinds of missing values, we'll
    follow accordingly. -/
    let processId? := j.getObjValAs? Int "processId"
    let clientInfo? := j.getObjValAs? ClientInfo "clientInfo"
    let rootUri? := j.getObjValAs? String "rootUri"
    let initializationOptions? := j.getObjValAs? InitializationOptions "initializationOptions"
    let capabilities ← j.getObjValAs? ClientCapabilities "capabilities"
    let trace := (j.getObjValAs? Trace "trace").toOption.getD Trace.off
    let workspaceFolders? := j.getObjValAs? (Array WorkspaceFolder) "workspaceFolders"
    return ⟨
      processId?.toOption,
      clientInfo?.toOption,
      rootUri?.toOption,
      initializationOptions?.toOption,
      capabilities,
      trace,
      workspaceFolders?.toOption⟩

inductive InitializedParams where
  | mk

instance : FromJson InitializedParams :=
  ⟨fun _ => pure InitializedParams.mk⟩

instance : ToJson InitializedParams :=
  ⟨fun _ => Json.null⟩

structure ServerInfo where
  name : String
  version? : Option String := none
  deriving ToJson, FromJson

structure InitializeResult where
  capabilities : ServerCapabilities
  serverInfo? : Option ServerInfo := none
  deriving ToJson, FromJson

end Lsp
end Lean
