/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Lean.Data.Lsp.Capabilities
import Lean.Data.Lsp.Workspace
import Lean.Data.Json

/-! Functionality to do with initializing and shutting down
the server ("General Messages" section of LSP spec). -/

namespace Lean
namespace Lsp

open Json

structure ClientInfo :=
(name : String)
(version? : Option String := none)

instance ClientInfo.hasFromJson : HasFromJson ClientInfo :=
⟨fun j => do
  name ← j.getObjValAs? String "name";
  let version? := j.getObjValAs? String "version";
  pure ⟨name, version?⟩⟩

inductive Trace
| off
| messages
| verbose

instance Trace.hasFromJson : HasFromJson Trace :=
⟨fun j => match j.getStr? with
  | some "off"      => Trace.off
  | some "messages" => Trace.messages
  | some "verbose"  => Trace.verbose
  | _               => none⟩

structure InitializeParams :=
(processId? : Option Int := none)
(clientInfo? : Option ClientInfo := none)
/- We don't support the deprecated rootPath
(rootPath? : Option String) -/
(rootUri? : Option String := none)
(initializationOptions? : Option Json := none)
(capabilities : ClientCapabilities)
/- If omitted, we default to off. -/
(trace : Trace := Trace.off)
(workspaceFolders? : Option (Array WorkspaceFolder) := none)

instance InitializeParams.hasFromJson : HasFromJson InitializeParams :=
⟨fun j => do
  /- Many of these params can be null instead of not present.
  For ease of implementation, we're liberal:
  missing params, wrong json types and null all map to none,
  even if LSP sometimes only allows some subset of these.
  In cases where LSP makes a meaningful distinction
  between different kinds of missing values, we'll
  follow accordingly. -/
  let processId? := j.getObjValAs? Int "processId";
  let clientInfo? := j.getObjValAs? ClientInfo "clientInfo";
  let rootUri? := j.getObjValAs? String "rootUri";
  let initializationOptions? := j.getObjVal? "initializationOptions";
  capabilities ← j.getObjValAs? ClientCapabilities "capabilities";
  let trace := (j.getObjValAs? Trace "trace").getD Trace.off;
  let workspaceFolders? := j.getObjValAs? (Array WorkspaceFolder) "workspaceFolders";
  pure ⟨processId?, clientInfo?, rootUri?, initializationOptions?, capabilities, trace, workspaceFolders?⟩⟩

inductive InitializedParams | mk

instance InitializedParams.hasFromJson : HasFromJson InitializedParams :=
⟨fun j => InitializedParams.mk⟩

structure ServerInfo :=
(name : String)
(version? : Option String := none)

instance ServerInfo.hasToJson : HasToJson ServerInfo :=
⟨fun o => mkObj $
  ⟨"name", o.name⟩ ::
  opt "version" o.version?⟩

structure InitializeResult :=
(capabilities : ServerCapabilities)
(serverInfo? : Option ServerInfo := none)

instance InitializeResult.hasToJson : HasToJson InitializeResult :=
⟨fun o => mkObj $
  ⟨"capabilities", toJson o.capabilities⟩ ::
  opt "serverInfo" o.serverInfo?⟩

end Lsp
end Lean
