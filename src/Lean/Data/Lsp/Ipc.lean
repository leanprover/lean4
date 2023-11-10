/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Init.System.IO
import Lean.Data.Json
import Lean.Data.Lsp.Communication
import Lean.Data.Lsp.Diagnostics
import Lean.Data.Lsp.Extra

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
  Reads response, discarding notifications in between. This function is meant
  purely for testing where we use `collectDiagnostics` explicitly if we do care
  about such notifications. -/
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
  | _ => throw $ userError s!"Expected JSON-RPC response, got: '{(toJson m).compress}'"

def waitForExit : IpcM UInt32 := do
  (←read).wait

/-- Waits for the worker to emit all diagnostics for the current document version
and returns them as a list. -/
partial def collectDiagnostics (waitForDiagnosticsId : RequestID := 0) (target : DocumentUri) (version : Nat)
: IpcM (List (Notification PublishDiagnosticsParams)) := do
  writeRequest ⟨waitForDiagnosticsId, "textDocument/waitForDiagnostics", WaitForDiagnosticsParams.mk target version⟩
  let rec loop : IpcM (List (Notification PublishDiagnosticsParams)) := do
    match (←readMessage) with
    | Message.response id _ =>
      if id == waitForDiagnosticsId then return []
      else loop
    | Message.responseError id _    msg _ =>
      if id == waitForDiagnosticsId then
        throw $ userError s!"Waiting for diagnostics failed: {msg}"
      else loop
    | Message.notification "textDocument/publishDiagnostics" (some param) =>
      match fromJson? (toJson param) with
      | Except.ok diagnosticParam => return ⟨"textDocument/publishDiagnostics", diagnosticParam⟩ :: (←loop)
      | Except.error inner => throw $ userError s!"Cannot decode publishDiagnostics parameters\n{inner}"
    | _ => loop
  loop

def runWith (lean : System.FilePath) (args : Array String := #[]) (test : IpcM α) : IO α := do
  let proc ← Process.spawn {
    toStdioConfig := ipcStdioConfig
    cmd := lean.toString
    args := args }
  ReaderT.run test proc

end Lean.Lsp.Ipc
