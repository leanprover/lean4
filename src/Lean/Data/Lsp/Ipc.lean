/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
module

prelude
public import Lean.Data.Lsp.Communication
public import Lean.Data.Lsp.Diagnostics
public import Lean.Data.Lsp.Extra
import Init.Data.List.Sort.Basic
public import Lean.Data.Lsp.LanguageFeatures
import Init.While

public section

/-! Provides an IpcM monad for interacting with an external LSP process.
Used for testing the Lean server. -/

namespace Lean.Lsp.Ipc

open IO
open JsonRpc

def ipcStdioConfig : Process.StdioConfig where
  stdin  := Process.Stdio.piped
  stdout := Process.Stdio.piped
  stderr := Process.Stdio.inherit

abbrev IpcM := ReaderT (Process.Child ipcStdioConfig) IO

variable [ToJson α]

def stdin : IpcM FS.Stream := do
  return FS.Stream.ofHandle (←read).stdin

def stdout : IpcM FS.Stream := do
  return FS.Stream.ofHandle (←read).stdout

def writeRequest (r : Request α) : IpcM Unit := do
  (←stdin).writeLspRequest r

def writeNotification (n : Notification α) : IpcM Unit := do
  (←stdin).writeLspNotification n

def shutdown (requestNo : Nat) : IpcM Unit := do
  let hIn ← stdout
  let hOut ← stdin
  hOut.writeLspRequest ⟨requestNo, "shutdown", Json.null⟩
  repeat
    let shutMsg ← hIn.readLspMessage
    match shutMsg with
    | Message.response id result =>
      assert! result.isNull
      if id != requestNo then
        throw <| IO.userError s!"Expected id {requestNo}, got id {id}"

      hOut.writeLspNotification ⟨"exit", Json.null⟩
      break
    | _ =>  -- ignore other messages in between.
      pure ()

def readMessage : IpcM JsonRpc.Message := do
  (←stdout).readLspMessage

def readRequestAs (expectedMethod : String) (α) [FromJson α] : IpcM (Request α) := do
  (←stdout).readLspRequestAs expectedMethod α

/--
Reads response, discarding notifications and server-to-client requests in between.
This function is meant purely for testing where we use `collectDiagnostics` explicitly
if we do care about such notifications.
-/
partial def readResponseAs (expectedID : RequestID) (α) [FromJson α] :
    IpcM (Response α) := do
  let m ← (←stdout).readLspMessage
  match m with
  | Message.response id result =>
    if id == expectedID then
      match fromJson? result with
      | Except.ok v => pure ⟨expectedID, v⟩
      | Except.error inner => throw $ userError s!"Unexpected result '{result.compress}'\n{inner}"
    else
      throw $ userError s!"Expected id {expectedID}, got id {id}"
  | .notification .. => readResponseAs expectedID α
  | .request .. => readResponseAs expectedID α
  | .responseError .. => throw $ userError s!"Expected JSON-RPC response, got: '{(toJson m).compress}'"

def waitForExit : IpcM UInt32 := do
  (←read).wait

def normalizePublishDiagnosticsParams (p : PublishDiagnosticsParams) :
    PublishDiagnosticsParams := {
  p with
  diagnostics :=
    -- Sort diagnostics by range and message to erase non-determinism in the order of diagnostics
    -- induced by parallelism. This isn't complete, but it will hopefully be plenty for all tests.
    let sorted := p.diagnostics.toList.mergeSort fun d1 d2 =>
      compare d1.fullRange d2.fullRange |>.then (compare d1.message d2.message) |>.isLE
    sorted.toArray
}

/--
Waits for the worker to emit all diagnostic notifications for the current document version and
returns the last notification, if any.

We used to return all notifications but with debouncing in the server, this would not be
deterministic anymore as what messages are dropped depends on wall-clock timing.
 -/
partial def collectDiagnostics (waitForDiagnosticsId : RequestID := 0) (target : DocumentUri) (version : Nat)
: IpcM (Option (Notification PublishDiagnosticsParams)) := do
  writeRequest ⟨waitForDiagnosticsId, "textDocument/waitForDiagnostics", WaitForDiagnosticsParams.mk target version⟩
  loop
where
  loop := do
    match (←readMessage) with
    | Message.response id _ =>
      if id == waitForDiagnosticsId then return none
      else loop
    | Message.responseError id _    msg _ =>
      if id == waitForDiagnosticsId then
        throw $ userError s!"Waiting for diagnostics failed: {msg}"
      else loop
    | Message.notification "textDocument/publishDiagnostics" (some param) =>
      match fromJson? (toJson param) with
      | Except.ok diagnosticParam => return (← loop).getD ⟨"textDocument/publishDiagnostics", normalizePublishDiagnosticsParams diagnosticParam⟩
      | Except.error inner => throw $ userError s!"Cannot decode publishDiagnostics parameters\n{inner}"
    | _ => loop

partial def waitForILeans (waitForILeansId : RequestID := 0) (target : DocumentUri) (version : Nat) : IpcM Unit := do
  writeRequest ⟨waitForILeansId, "$/lean/waitForILeans", WaitForILeansParams.mk target version⟩
  while true do
    match (← readMessage) with
    | .response id _ =>
      if id == waitForILeansId then
        return
    | .responseError id _ msg _ =>
      if id == waitForILeansId then
        throw $ userError s!"Waiting for ILeans failed: {msg}"
    | _ =>
      pure ()

partial def waitForWatchdogILeans (waitForILeansId : RequestID := 0) : IpcM Unit := do
  writeRequest ⟨waitForILeansId, "$/lean/waitForILeans", WaitForILeansParams.mk none none⟩
  while true do
    match (← readMessage) with
    | .response id _ =>
      if id == waitForILeansId then
        return
    | .responseError id _ msg _ =>
      if id == waitForILeansId then
        throw $ userError s!"Waiting for ILeans failed: {msg}"
    | _ =>
      pure ()

/--
Waits for a diagnostic notification with a specific message to be emitted. Discards all received
messages, so should not be combined with `collectDiagnostics`.
-/
partial def waitForMessage (msg : String) : IpcM Unit := do
  loop
where
  loop := do
    match (←readMessage) with
    | Message.notification "textDocument/publishDiagnostics" (some param) =>
      match fromJson? (α := PublishDiagnosticsParams) (toJson param) with
      | Except.ok diagnosticParam =>
        if diagnosticParam.diagnostics.any (·.message == msg) then
          return
        loop
      | Except.error inner => throw $ userError s!"Cannot decode publishDiagnostics parameters\n{inner}"
    | _ => loop

structure CallHierarchy where
  item       : CallHierarchyItem
  fromRanges : Array Range
  children   : Array CallHierarchy
  deriving FromJson, ToJson

partial def expandIncomingCallHierarchy (requestNo : Nat) (uri : DocumentUri) (pos : Lsp.Position) : IpcM (Array CallHierarchy × Nat) := do
  writeRequest {
    id := requestNo
    method := "textDocument/prepareCallHierarchy"
    param := {
      textDocument := { uri }
      position := pos
      : CallHierarchyPrepareParams
    }
  }
  let r ← readResponseAs requestNo (Option (Array CallHierarchyItem))
  let mut requestNo := requestNo + 1
  let roots := r.result.getD #[]
  let mut hierarchies := #[]
  for root in roots do
    let (hierarchy, rootRequestNo) ← go requestNo root #[] {}
    requestNo := rootRequestNo
    hierarchies := hierarchies.push hierarchy
  return (hierarchies, requestNo)
where
  go (requestNo : Nat) (item : CallHierarchyItem) (fromRanges : Array Range) (visited : Std.TreeSet String) : IpcM (CallHierarchy × Nat) := do
    if visited.contains item.name then
      return ({ item, fromRanges := #[], children := #[] }, requestNo)
    writeRequest {
      id := requestNo
      method := "callHierarchy/incomingCalls"
      param := {
        item
        : CallHierarchyIncomingCallsParams
      }
    }
    let r ← readResponseAs requestNo (Option (Array CallHierarchyIncomingCall))
    let visited : Std.TreeSet String := visited.insert item.name
    let mut requestNo := requestNo + 1
    let children := r.result.getD #[]
    let mut childHierarchies := #[]
    for c in children do
      let (childHierarchy, childRequestNo) ← go requestNo c.from c.fromRanges visited
      childHierarchies := childHierarchies.push childHierarchy
      requestNo := childRequestNo
    return ({ item, fromRanges, children := childHierarchies }, requestNo)

partial def expandOutgoingCallHierarchy (requestNo : Nat) (uri : DocumentUri) (pos : Lsp.Position) : IpcM (Array CallHierarchy × Nat) := do
  writeRequest {
    id := requestNo
    method := "textDocument/prepareCallHierarchy"
    param := {
      textDocument := { uri }
      position := pos
      : CallHierarchyPrepareParams
    }
  }
  let r ← readResponseAs requestNo (Option (Array CallHierarchyItem))
  let mut requestNo := requestNo + 1
  let roots := r.result.getD #[]
  let mut hierarchies := #[]
  for root in roots do
    let (hierarchy, rootRequestNo) ← go requestNo root #[] {}
    requestNo := rootRequestNo
    hierarchies := hierarchies.push hierarchy
  return (hierarchies, requestNo)
where
  go (requestNo : Nat) (item : CallHierarchyItem) (fromRanges : Array Range) (visited : Std.TreeSet String) : IpcM (CallHierarchy × Nat) := do
    if visited.contains item.name then
      return ({ item, fromRanges := #[], children := #[] }, requestNo)
    writeRequest {
      id := requestNo
      method := "callHierarchy/outgoingCalls"
      param := {
        item
        : CallHierarchyOutgoingCallsParams
      }
    }
    let r ← readResponseAs requestNo (Option (Array CallHierarchyOutgoingCall))
    let visited : Std.TreeSet String := visited.insert item.name
    let mut requestNo := requestNo + 1
    let children := r.result.getD #[]
    let mut childHierarchies := #[]
    for c in children do
      let (childHierarchy, childRequestNo) ← go requestNo c.to c.fromRanges visited
      childHierarchies := childHierarchies.push childHierarchy
      requestNo := childRequestNo
    return ({ item, fromRanges, children := childHierarchies }, requestNo)

structure ModuleHierarchy where
  item : LeanImport
  children : Array ModuleHierarchy
  deriving FromJson, ToJson

partial def expandModuleHierarchyImports (requestNo : Nat) (uri : DocumentUri) : IpcM (Option ModuleHierarchy × Nat) := do
  writeRequest {
    id := requestNo
    method := "$/lean/prepareModuleHierarchy"
    param := {
      textDocument := { uri }
      : LeanPrepareModuleHierarchyParams
    }
  }
  let r ← readResponseAs requestNo (Option LeanModule)
  let mut requestNo := requestNo + 1
  let some root := r.result
    | return (none, requestNo)
  let root := {
    module := root
    kind := { isAll := false, isPrivate := false, metaKind := .full }
  }
  let (hierarchy, rootRequestNo) ← go requestNo root {}
  requestNo := rootRequestNo
  return (hierarchy, requestNo)
where
  go (requestNo : Nat) (item : LeanImport) (visited : Std.TreeSet String) : IpcM (ModuleHierarchy × Nat) := do
    if visited.contains item.module.name then
      return ({ item, children := #[] }, requestNo)
    writeRequest {
      id := requestNo
      method := "$/lean/moduleHierarchy/imports"
      param := {
        module := item.module
        : LeanModuleHierarchyImportsParams
      }
    }
    let r ← readResponseAs requestNo (Array LeanImport)
    let visited : Std.TreeSet String := visited.insert item.module.name
    let mut requestNo := requestNo + 1
    let children := r.result
    let mut childHierarchies := #[]
    for c in children do
      let (childHierarchy, childRequestNo) ← go requestNo c visited
      childHierarchies := childHierarchies.push childHierarchy
      requestNo := childRequestNo
    return ({ item, children := childHierarchies }, requestNo)

partial def expandModuleHierarchyImportedBy (requestNo : Nat) (uri : DocumentUri) : IpcM (Option ModuleHierarchy × Nat) := do
  writeRequest {
    id := requestNo
    method := "$/lean/prepareModuleHierarchy"
    param := {
      textDocument := { uri }
      : LeanPrepareModuleHierarchyParams
    }
  }
  let r ← readResponseAs requestNo (Option LeanModule)
  let mut requestNo := requestNo + 1
  let some root := r.result
    | return (none, requestNo)
  let root := {
    module := root
    kind := { isAll := false, isPrivate := false, metaKind := .full }
  }
  let (hierarchy, rootRequestNo) ← go requestNo root {}
  requestNo := rootRequestNo
  return (hierarchy, requestNo)
where
  go (requestNo : Nat) (item : LeanImport) (visited : Std.TreeSet String) : IpcM (ModuleHierarchy × Nat) := do
    if visited.contains item.module.name then
      return ({ item, children := #[] }, requestNo)
    writeRequest {
      id := requestNo
      method := "$/lean/moduleHierarchy/importedBy"
      param := {
        module := item.module
        : LeanModuleHierarchyImportedByParams
      }
    }
    let r ← readResponseAs requestNo (Array LeanImport)
    let visited : Std.TreeSet String := visited.insert item.module.name
    let mut requestNo := requestNo + 1
    let children := r.result
    let mut childHierarchies := #[]
    for c in children do
      let (childHierarchy, childRequestNo) ← go requestNo c visited
      childHierarchies := childHierarchies.push childHierarchy
      requestNo := childRequestNo
    return ({ item, children := childHierarchies }, requestNo)

def runWith (lean : String) (args : Array String := #[]) (test : IpcM α) : IO α := do
  let proc ← Process.spawn {
    toStdioConfig := ipcStdioConfig
    cmd := lean
    args := args }
  ReaderT.run test proc

end Lean.Lsp.Ipc
