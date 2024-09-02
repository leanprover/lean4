/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
prelude
import Lean.Data.Options
import Lean.Server.InfoUtils
import Lean.Linter.Basic

namespace Lean.Linter

open Lean.Elab

/-- Go upwards through the given `tree` starting from the smallest node that
contains the given `range` and collect all `MacroExpansionInfo`s on the way up.
The result is `some []` if no `MacroExpansionInfo` was found on the way and
`none` if no `InfoTree` node was found that covers the given `range`.

Return the result reversed, s.t. the macro expansion that would be applied to
the original syntax first is the first element of the returned list. -/
def collectMacroExpansions? {m} [Monad m] (range : String.Range) (tree : Elab.InfoTree) : m <| Option <| List Elab.MacroExpansionInfo := do
  if let .some <| .some result ← go then
    return some result.reverse
  else
    return none
where
  go : m <| Option <| Option <| List Elab.MacroExpansionInfo := tree.visitM (postNode := fun _ i _ results => do
    let results := results |>.filterMap id |>.filterMap id

    -- we expect that at most one InfoTree child returns a result
    if let results :: _ := results then
      if let .ofMacroExpansionInfo i := i then
        return some <| i :: results
      else
        return some results
    else if i.contains range.start && i.contains (includeStop := true) range.stop then
      if let .ofMacroExpansionInfo i := i then
        return some [i]
      else
        return some []
    else
      return none)
