/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Marc Huisinga
-/
module

prelude
public import Init.System.Uri
public import Lean.Data.Lsp.Communication
public import Lean.Data.Lsp.Diagnostics
public import Lean.Data.Lsp.Extra
public import Lean.Server.InfoUtils

public section

namespace IO

/-- Throws an `IO.userError`. -/
def throwServerError (err : String) : IO α :=
  throw (userError err)

namespace FS.Stream

/--
Chains two streams by creating a new stream s.t. writing to it
just writes to `a` but reading from it also duplicates the read output
into `b`, c.f. `a | tee b` on Unix.
NB: if `a` is written to but this stream is never read from,
the output will *not* be duplicated. Use this if you only care
about the data that was actually read.
-/
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

open IO
open Lsp

private def externalUriToName (uri : DocumentUri) : Lean.Name :=
  .str .anonymous s!"external:{uri}"

private def externalNameToUri? (name : Lean.Name) : Option DocumentUri := do
  let .str .anonymous name := name
    | none
  let uri ← name.dropPrefix? "external:"
  return uri.toString

def modToUri'? (c : PkgContext) (modId : GlobalModId) : Option DocumentUri := do
  if let some uri := externalNameToUri? modId.mod then
    return uri
  let path ← c.modToPath'? modId
  return System.Uri.pathToUri path

def uriToMod' (c : PkgContext) (uri : DocumentUri) : GlobalModId := Id.run do
  let some path := System.Uri.fileUriToPath? uri
    | return { pkg? := none, mod := externalUriToName uri }
  if path.extension != "lean" then
    return { pkg? := none, mod := externalUriToName uri }
  let some modId := PkgContext.pathToMod'? c path
    | return { pkg? := none, mod := externalUriToName uri }
  return modId

/--
Finds the URI corresponding to `modId`. Yields `none` if the given module cannot be found in the
search path anymore (e.g. because the module name was loaded from a file that was built using an old
search path).
-/
def modToUri? (modId : GlobalModId) : BaseIO (Option DocumentUri) := do
  let c ← PkgContext.getPkgContext
  return modToUri'? c modId

/-- Finds the module identifier corresponding to `uri`. -/
def uriToMod (uri : DocumentUri) : BaseIO GlobalModId := do
  let c ← PkgContext.getPkgContext
  return uriToMod' c uri

/-- Meta-Data of a document. -/
structure DocumentMeta where
  /-- URI where the document is located. -/
  uri                 : Lsp.DocumentUri
  modId               : GlobalModId
  /-- Version number of the document. Incremented whenever the document is edited. -/
  version             : Nat
  /--
  Current text of the document.
  It is maintained such that it is normalized using `String.crlfToLf`, which preserves logical line/column numbers.
  (Note: we assume that edit operations never split or merge `\r\n` line endings.) -/
  text                : FileMap
  /--
  Controls when dependencies of the document are built on `textDocument/didOpen` notifications.
  -/
  dependencyBuildMode : Lsp.DependencyBuildMode
  deriving Inhabited

/-- Extracts an `InputContext` from `doc`. -/
def DocumentMeta.mkInputContext (doc : DocumentMeta) : Parser.InputContext :=
  .mk
    (input := doc.text.source)
    (fileName := (System.Uri.fileUriToPath? doc.uri).getD doc.uri |>.toString)
    (fileMap  := doc.text)

/-- Converts a module name to a URI in the dependency closure of this document. -/
def DocumentMeta.modToUri? (doc : DocumentMeta) (mod : Name) : BaseIO (Option DocumentUri) :=
  Server.modToUri? { pkg? := doc.modId.pkg?, mod }

/--
Replaces the range `r` (using LSP UTF-16 positions) in `text` (using UTF-8 positions)
with `newText`.
-/
def replaceLspRange (text : FileMap) (r : Lsp.Range) (newText : String) : FileMap :=
  let start := text.lspPosToUtf8Pos r.start
  let «end» := text.lspPosToUtf8Pos r.«end»
  let pre := String.Pos.Raw.extract text.source 0 start
  let post := String.Pos.Raw.extract text.source «end» text.source.rawEndPos
  -- `pre` and `post` already have normalized line endings, so only `newText` needs its endings normalized.
  -- Note: this assumes that editing never separates a `\r\n`.
  -- If `pre` ends with `\r` and `newText` begins with `\n`, the result is potentially inaccurate.
  -- If this is ever a problem, we could store a second unnormalized FileMap, edit it, and normalize it here.
  (pre ++ newText.crlfToLf ++ post).toFileMap

/-- Returns the document contents with the change applied. -/
def applyDocumentChange (oldText : FileMap) : (change : Lsp.TextDocumentContentChangeEvent) → FileMap
  | TextDocumentContentChangeEvent.rangeChange (range : Range) (newText : String) =>
    replaceLspRange oldText range newText
  | TextDocumentContentChangeEvent.fullChange (newText : String) =>
    newText.crlfToLf.toFileMap

/-- Returns the document contents with all changes applied. -/
def foldDocumentChanges (changes : Array Lsp.TextDocumentContentChangeEvent) (oldText : FileMap) : FileMap :=
  changes.foldl applyDocumentChange oldText

/-- Constructs a `textDocument/publishDiagnostics` notification. -/
def mkPublishDiagnosticsNotification (m : DocumentMeta) (diagnostics : Array Lsp.Diagnostic) :
    JsonRpc.Notification Lsp.PublishDiagnosticsParams where
  method := "textDocument/publishDiagnostics"
  param  := {
    uri         := m.uri
    version?    := some m.version
    diagnostics := diagnostics
  }

/-- Constructs a `$/lean/fileProgress` notification. -/
def mkFileProgressNotification (m : DocumentMeta) (processing : Array LeanFileProgressProcessingInfo) :
    JsonRpc.Notification Lsp.LeanFileProgressParams where
  method := "$/lean/fileProgress"
  param := {
    textDocument := { uri := m.uri, version? := m.version }
    processing
  }

/-- Constructs a `$/lean/fileProgress` notification from the given position onwards. -/
def mkFileProgressAtPosNotification (m : DocumentMeta) (pos : String.Pos.Raw)
  (kind : LeanFileProgressKind := LeanFileProgressKind.processing) :
    JsonRpc.Notification Lsp.LeanFileProgressParams :=
  mkFileProgressNotification m #[{ range := ⟨m.text.utf8PosToLspPos pos, m.text.utf8PosToLspPos m.text.source.rawEndPos⟩, kind := kind }]

/-- Constructs a `$/lean/fileProgress` notification marking processing as done. -/
def mkFileProgressDoneNotification (m : DocumentMeta) : JsonRpc.Notification Lsp.LeanFileProgressParams :=
  mkFileProgressNotification m #[]

-- TODO: should return a request ID (or task?) when we add response handling
def mkApplyWorkspaceEditRequest (params : ApplyWorkspaceEditParams) :
    JsonRpc.Request ApplyWorkspaceEditParams :=
  ⟨"workspace/applyEdit", "workspace/applyEdit", params⟩

/--
Finds the URI corresponding to `modName` in `searchSearchPath`.
Yields `none` if the file corresponding to `modName` has been deleted in the mean-time.

See also `getSrcSearchPath`.
-/
@[deprecated Lean.Server.modToUri? (since := "2026-02-03")]
def documentUriFromModule? (modName : Name) : IO (Option DocumentUri) := do
  if let some uri := externalNameToUri? modName then
    return uri
  let some path ← (← getSrcSearchPath).findModuleWithExt "lean" modName
    | return none
  -- Resolve symlinks (such as `src` in the build dir) so that files are opened
  -- in the right folder
  let path ← IO.FS.realPath path
  return some <| System.Uri.pathToUri path

/--
Finds the module name corresponding to `uri` in `srcSearchPath`.

See also `getSrcSearchPath`.
-/
@[deprecated Lean.Server.uriToMod (since := "2026-02-03")]
def moduleFromDocumentUri (uri : DocumentUri) : IO Name := do
  let some path := System.Uri.fileUriToPath? uri
    | return externalUriToName uri
  if path.extension != "lean" then
    return externalUriToName uri
  let some modNameInPath ← searchModuleNameOfFileName path (← getSrcSearchPath)
    | return externalUriToName uri
  return modNameInPath

end Lean.Server

/--
Converts an UTF-8-based `Lean.Syntax.Range` in `text` to an equivalent LSP UTF-16-based `Lsp.Range`
in `text`.
-/
def Lean.Syntax.Range.toLspRange (text : Lean.FileMap) (r : Lean.Syntax.Range) : Lean.Lsp.Range :=
  ⟨text.utf8PosToLspPos r.start, text.utf8PosToLspPos r.stop⟩
