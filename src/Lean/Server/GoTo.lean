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

open Elab in
def locationLinksFromDecl (uri : DocumentUri) (n : Name) (originRange? : Option Range)
    : MetaM (Array LocationLink) := do
  -- Potentially this name is a builtin that has not been imported yet:
  unless (← getEnv).contains n do return #[]
  let mod? ← findModuleOf? n
  let modUri? ← match mod? with
    | some modName => documentUriFromModule? modName
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
