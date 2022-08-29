/-
Copyright (c) 2022 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Sebastian Ullrich, Lars König, Wojciech Nawrocki
-/
import Lean.Data.Json.FromToJson
import Lean.Util.Path
import Lean.Server.Utils

namespace Lean.Server

open Lsp

inductive GoToKind
  | declaration | definition | type
  deriving BEq, ToJson, FromJson

def documentUriFromModule (srcSearchPath : SearchPath) (modName : Name) : IO (Option DocumentUri) := do
  let some modFname ← srcSearchPath.findModuleWithExt "lean" modName
    | pure none
  -- resolve symlinks (such as `src` in the build dir) so that files are opened
  -- in the right folder
  let modFname ← IO.FS.realPath modFname
  return some <| System.Uri.pathToUri modFname

open Elab in
def locationLinksFromDecl (srcSearchPath : SearchPath) (uri : DocumentUri) (n : Name)
    (originRange? : Option Range) : MetaM (Array LocationLink) := do
  let mod? ← findModuleOf? n
  let modUri? ← match mod? with
    | some modName => documentUriFromModule srcSearchPath modName
    | none         => pure <| some uri

  let ranges? ← findDeclarationRanges? n
  if let (some ranges, some modUri) := (ranges?, modUri?) then
    let declRangeToLspRange (r : DeclarationRange) : Lsp.Range :=
      { start := ⟨r.pos.line - 1, r.charUtf16⟩
        «end» := ⟨r.endPos.line - 1, r.endCharUtf16⟩ }
    let ll : LocationLink := {
      originSelectionRange? := originRange?
      targetUri := modUri
      targetRange := declRangeToLspRange ranges.range
      targetSelectionRange := declRangeToLspRange ranges.selectionRange
    }
    return #[ll]
  return #[]

end Lean.Server
