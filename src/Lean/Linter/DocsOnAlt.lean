/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
import Lean.Parser.Syntax
public import Lean.Data.Options
import Lean.Elab.Command

public section

namespace Lean.Linter
open Elab.Command Parser Command
open Parser.Term hiding «set_option»

register_builtin_option linter.tactic.docsOnAlt : Bool := {
  defValue := true
  descr := "enable the 'documentation on tactic alternatives' linter"
}

private def getLinterDocsOnAlt (o : LinterOptions) : Bool :=
  getLinterValue linter.tactic.docsOnAlt o


namespace DocsOnAlt


private partial def docsOnAlt : Linter where
  run stx := do
    if getLinterDocsOnAlt (← getLinterOptions) then
      if let some mods := stx.find? (·.getKind ∈ [``declModifiers, ``Command.syntax]) then
        if mods.find? isAltAttr |>.isSome then
          if let some doc := mods.find? (·.getKind == ``docComment) then
            let msg := m!"Documentation is ignored on a tactic alternative."
            logLint linter.tactic.docsOnAlt doc msg
where
  isAltAttr : Syntax → Bool
    | `(attr|tactic_alt $_) => true
    | _ => false


builtin_initialize addLinter docsOnAlt
