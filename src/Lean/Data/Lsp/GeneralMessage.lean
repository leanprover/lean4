import Lean.Data.Lsp.Capabilities
import Lean.Data.Json

namespace Lean
namespace Lsp

open Json

structure ClientInfo :=
(name : String)
(version? : Option String := none)

instance clientInfoHasFromJson : HasFromJson ClientInfo :=
⟨fun j => do
  name ← j.getObjValAs? String "name";
  let version? := j.getObjValAs? String "version";
  pure ⟨name, version?⟩⟩

inductive Trace
| messages
| verbose

instance traceHasFromJson : HasFromJson Trace :=
⟨fun j => match j.getStr? with
| some "messages" => Trace.messages
| some "verbose" => Trace.verbose
| _ => none⟩

structure InitializeParams :=
-- id of parent process, none if no parent process
(processId? : Option Int := none)
(clientInfo? : Option ClientInfo := none)
/- We don't support the deprecated rootPath
(rootPath? : Option String)-/
-- none: no folder is open
(rootUri? : Option String := none)
(initializationOptions? : Option Json := none)
(capabilities : ClientCapabilities)
(trace? : Option Trace := none) -- none: no trace
--(workspaceFolders? : Option Unit) TODO

instance initializeParamsHasFromJson : HasFromJson InitializeParams :=
⟨fun j => do
  -- many of these params can be null instead of not present.
  -- for ease of implementation, we're liberal:
  -- missing params, wrong json types and null all map to none,
  -- even if LSP sometimes only allows some subset of these.
  -- in cases where LSP makes a meaningful distinction
  -- between different kinds of missing values, we'll
  -- follow accordingly.
  let processId? := j.getObjValAs? Int "processId";
  let clientInfo? := j.getObjValAs? ClientInfo "clientInfo";
  let rootUri? := j.getObjValAs? String "rootUri";
  let initializationOptions? := j.getObjVal? "initializationOptions";
  capabilities ← j.getObjValAs? ClientCapabilities "capabilities";
  let trace? := j.getObjValAs? Trace "trace";
  pure ⟨processId?, clientInfo?, rootUri?, initializationOptions?, capabilities, trace?⟩⟩

inductive Initialized
| mk

instance initializedHasFromJson : HasFromJson Initialized :=
⟨fun j => Initialized.mk⟩

structure ServerInfo :=
(name : String)
(version? : Option String := none)

instance serverInfoHasToJson : HasToJson ServerInfo :=
⟨fun o => mkObj $
  ⟨"name", o.name⟩ :: opt "version" o.version?⟩

structure InitializeResult :=
(capabilities : ServerCapabilities)
(serverInfo? : Option ServerInfo := none)

instance initializeResultHasToJson : HasToJson InitializeResult :=
⟨fun o => mkObj $
  ⟨"capabilities", toJson o.capabilities⟩ :: opt "serverInfo" o.serverInfo?⟩

end Lsp
end Lean
