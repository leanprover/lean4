/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
module

prelude
public import Lean.Data.Lsp.Capabilities
public import Lean.Data.Lsp.Workspace

public section

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

local instance [BEq α] [Hashable α] [ToJson α] : ToJson (Std.HashSet α) where
  toJson s := .arr <| s.toArray.map toJson

local instance [BEq α] [Hashable α] [FromJson α] : FromJson (Std.HashSet α) where
  fromJson?
    | .arr a => return Std.HashSet.ofArray <| ← a.mapM fromJson?
    | _ => throw "Expected array when converting JSON to Std.HashSet"

structure LogConfig where
  logDir? : Option System.FilePath
  allowedMethods? : Option (Std.HashSet String)
  disallowedMethods? : Option (Std.HashSet String)
  deriving FromJson, ToJson

/-- Lean-specific initialization options. -/
structure InitializationOptions where
  /-- Whether the client supports interactive widgets. When true, in order to improve performance
  the server may cease including information which can be retrieved interactively in some standard
  LSP messages. Defaults to false. -/
  hasWidgets? : Option Bool
  logCfg? : Option LogConfig
  deriving ToJson, FromJson

structure InitializeParams where
  processId? : Option Int := none
  clientInfo? : Option ClientInfo := none
  /-- Not used by the language server. We use the cwd of the server process instead. -/
  rootUri? : Option String := none
  initializationOptions? : Option InitializationOptions := none
  capabilities : ClientCapabilities
  /-- If omitted, we default to off. -/
  trace : Trace := Trace.off
  workspaceFolders? : Option (Array WorkspaceFolder) := none
  deriving ToJson

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
