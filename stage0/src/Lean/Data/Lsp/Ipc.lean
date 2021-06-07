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
  FS.Stream.ofHandle (←read).stdin

def stdout : IpcM FS.Stream := do
  FS.Stream.ofHandle (←read).stdout

def writeRequest (r : Request α) : IpcM Unit := do
  (←stdin).writeLspRequest r

def writeNotification (n : Notification α) : IpcM Unit := do
  (←stdin).writeLspNotification n

def readMessage : IpcM JsonRpc.Message := do
  (←stdout).readLspMessage

def readResponseAs (expectedID : RequestID) (α) [FromJson α] : IpcM (Response α) := do
  (←stdout).readLspResponseAs expectedID α

def waitForExit : IpcM UInt32 := do
  (←read).wait

/-- Waits for the worker to emit all diagnostics for the current document version
and returns them as a list. -/
partial def collectDiagnostics (waitForDiagnosticsId : RequestID := 0) (target : DocumentUri) (version : Nat)
: IpcM (List (Notification PublishDiagnosticsParams)) := do
  writeRequest ⟨waitForDiagnosticsId, "textDocument/waitForDiagnostics", WaitForDiagnosticsParams.mk target version⟩
  let rec loop : IpcM (List (Notification PublishDiagnosticsParams)) := do
    match ←readMessage with
    | Message.response id _ =>
      if id == waitForDiagnosticsId then []
      else loop
    | Message.responseError id code msg _ =>
      if id == waitForDiagnosticsId then
        throw $ userError s!"Waiting for diagnostics failed: {msg}"
      else loop
    | Message.notification "textDocument/publishDiagnostics" (some param) =>
      match fromJson? (toJson param) with
      | Except.ok diagnosticParam => ⟨"textDocument/publishDiagnostics", diagnosticParam⟩ :: (←loop)
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
