/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Marc Huisinga
-/
import Lean.Data.Lsp.Communication
import Lean.Data.Lsp.Diagnostics
import Lean.Data.Lsp.Extra
import Lean.Data.Lsp.TextSync
import Lean.Server.InfoUtils

namespace IO

def throwServerError (err : String) : IO α :=
  throw (userError err)

namespace FS.Stream

/-- Chains two streams by creating a new stream s.t. writing to it
just writes to `a` but reading from it also duplicates the read output
into `b`, c.f. `a | tee b` on Unix.
NB: if `a` is written to but this stream is never read from,
the output will *not* be duplicated. Use this if you only care
about the data that was actually read. -/
def chainRight (a : Stream) (b : Stream) (flushEagerly : Bool := false) : Stream :=
  { a with
    flush := a.flush *> b.flush
    read := fun sz => do
      let bs ← a.read sz
      b.write bs
      if flushEagerly then b.flush
      pure bs
    getLine := do
      let ln ← a.getLine
      b.putStr ln
      if flushEagerly then b.flush
      pure ln }

/-- Like `tee a | b` on Unix. See `chainOut`. -/
def chainLeft (a : Stream) (b : Stream) (flushEagerly : Bool := false) : Stream :=
  { b with
    flush := a.flush *> b.flush
    write := fun bs => do
      a.write bs
      if flushEagerly then a.flush
      b.write bs
    putStr := fun s => do
      a.putStr s
      if flushEagerly then a.flush
      b.putStr s }

/-- Prefixes all written outputs with `pre`. -/
def withPrefix (a : Stream) (pre : String) : Stream :=
  { a with
    write := fun bs => do
      a.putStr pre
      a.write bs
    putStr := fun s =>
      a.putStr (pre ++ s) }

end FS.Stream
end IO

namespace Lean.Server

structure DocumentMeta where
  uri                 : Lsp.DocumentUri
  version             : Nat
  text                : FileMap
  dependencyBuildMode : Lsp.DependencyBuildMode
  deriving Inhabited

def DocumentMeta.mkInputContext (doc : DocumentMeta) : Parser.InputContext where
  input    := doc.text.source
  fileName := (System.Uri.fileUriToPath? doc.uri).getD doc.uri |>.toString
  fileMap  := doc.text

def replaceLspRange (text : FileMap) (r : Lsp.Range) (newText : String) : FileMap :=
  let start := text.lspPosToUtf8Pos r.start
  let «end» := text.lspPosToUtf8Pos r.«end»
  let pre := text.source.extract 0 start
  let post := text.source.extract «end» text.source.endPos
  (pre ++ newText ++ post).toFileMap

open IO

/-- Duplicates an I/O stream to a log file `fName` in LEAN_SERVER_LOG_DIR
if that envvar is set. -/
def maybeTee (fName : String) (isOut : Bool) (h : FS.Stream) : IO FS.Stream := do
  match (← IO.getEnv "LEAN_SERVER_LOG_DIR") with
  | none => pure h
  | some logDir =>
    IO.FS.createDirAll logDir
    let hTee ← FS.Handle.mk (System.mkFilePath [logDir, fName]) FS.Mode.write
    let hTee := FS.Stream.ofHandle hTee
    pure $ if isOut then
      hTee.chainLeft h true
    else
      h.chainRight hTee true

open Lsp

/-- Returns the document contents with the change applied. -/
def applyDocumentChange (oldText : FileMap) : (change : Lsp.TextDocumentContentChangeEvent) → FileMap
  | TextDocumentContentChangeEvent.rangeChange (range : Range) (newText : String) =>
    replaceLspRange oldText range newText
  | TextDocumentContentChangeEvent.fullChange (newText : String) =>
    newText.toFileMap

/-- Returns the document contents with all changes applied. -/
def foldDocumentChanges (changes : Array Lsp.TextDocumentContentChangeEvent) (oldText : FileMap) : FileMap :=
  changes.foldl applyDocumentChange oldText

def publishDiagnostics (m : DocumentMeta) (diagnostics : Array Lsp.Diagnostic) (hOut : FS.Stream) : IO Unit :=
  hOut.writeLspNotification {
    method := "textDocument/publishDiagnostics"
    param  := {
      uri         := m.uri
      version?    := m.version
      diagnostics := diagnostics
      : PublishDiagnosticsParams
    }
  }

def publishProgress (m : DocumentMeta) (processing : Array LeanFileProgressProcessingInfo) (hOut : FS.Stream) : IO Unit :=
  hOut.writeLspNotification {
    method := "$/lean/fileProgress"
    param := {
      textDocument := { uri := m.uri, version? := m.version }
      processing
      : LeanFileProgressParams
    }
  }

def publishProgressAtPos (m : DocumentMeta) (pos : String.Pos) (hOut : FS.Stream) (kind : LeanFileProgressKind := LeanFileProgressKind.processing) : IO Unit :=
  publishProgress m #[{ range := ⟨m.text.utf8PosToLspPos pos, m.text.utf8PosToLspPos m.text.source.endPos⟩, kind := kind }] hOut

def publishProgressDone (m : DocumentMeta) (hOut : FS.Stream) : IO Unit :=
  publishProgress m #[] hOut

-- TODO: should return a request ID (or task?) when we add response handling
def applyWorkspaceEdit (params : ApplyWorkspaceEditParams) (hOut : FS.Stream) : IO Unit :=
  hOut.writeLspRequest ⟨"workspace/applyEdit", "workspace/applyEdit", params⟩

end Lean.Server

def String.Range.toLspRange (text : Lean.FileMap) (r : String.Range) : Lean.Lsp.Range :=
  ⟨text.utf8PosToLspPos r.start, text.utf8PosToLspPos r.stop⟩
