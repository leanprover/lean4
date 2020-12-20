/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga
-/
import Lean.Data.Json
import Lean.Data.JsonRpc
import Lean.Data.Lsp.Basic

/-
This file contains Lean-specific extensions to LSP.
The following additional packets are supported:
- "textDocument/waitForDiagnostics": Yields a response when all the diagnostics that were pending at the time of
  arrival of the packet have been emitted. Exists for synchronization purposes, e.g. during testing or when external tools might want to use
  our LSP server.
-/

namespace Lean.Lsp

open Json

structure WaitForDiagnosticsParam where
  uri : DocumentUri

instance : FromJson WaitForDiagnosticsParam :=
  ⟨fun j => do
    let id ← j.getObjValAs? DocumentUri "uri"
    pure ⟨id⟩⟩

instance : ToJson WaitForDiagnosticsParam :=
  ⟨fun o => mkObj [⟨"uri", toJson o.uri⟩]⟩

structure WaitForDiagnostics

instance : FromJson WaitForDiagnostics :=
  ⟨fun j => WaitForDiagnostics.mk⟩

instance : ToJson WaitForDiagnostics :=
  ⟨fun o => mkObj []⟩

end Lean.Lsp