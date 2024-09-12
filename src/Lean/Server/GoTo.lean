/-
Copyright (c) 2022 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Sebastian Ullrich, Lars König, Wojciech Nawrocki
-/
prelude
import Lean.Data.Json.FromToJson
import Lean.Util.Path
import Lean.Server.Utils

namespace Lean.Server

open Lsp

inductive GoToKind
  | declaration | definition | type
  deriving BEq, ToJson, FromJson

/-- Finds the URI corresponding to `modName` in `searchSearchPath`. -/
def documentUriFromModule (srcSearchPath : SearchPath) (modName : Name)
    : IO (Option DocumentUri) := do
  let some modFname ← srcSearchPath.findModuleWithExt "lean" modName
    | pure none
  -- resolve symlinks (such as `src` in the build dir) so that files are opened
  -- in the right folder
  let modFname ← IO.FS.realPath modFname
  return some <| System.Uri.pathToUri modFname

/-- Finds the module name corresponding to `uri` in `srcSearchPath`. -/
def moduleFromDocumentUri (srcSearchPath : SearchPath) (uri : DocumentUri)
    : IO (Option Name) := do
  let some modFname := System.Uri.fileUriToPath? uri
    | return none
  searchModuleNameOfFileName modFname srcSearchPath

open Elab in
def locationLinksFromDecl (srcSearchPath : SearchPath) (uri : DocumentUri) (n : Name)
    (originRange? : Option Range) : MetaM (Array LocationLink) := do
  -- Potentially this name is a builtin that has not been imported yet:
  unless (← getEnv).contains n do return #[]
  let mod? ← findModuleOf? n
  let modUri? ← match mod? with
    | some modName => documentUriFromModule srcSearchPath modName
    | none         => pure <| some uri

  let ranges? ← findDeclarationRanges? n
  if let (some ranges, some modUri) := (ranges?, modUri?) then
    let ll : LocationLink := {
      originSelectionRange? := originRange?
      targetUri := modUri
      targetRange := ranges.range.toLspRange
      targetSelectionRange := ranges.selectionRange.toLspRange
    }
    return #[ll]
  return #[]

end Lean.Server
