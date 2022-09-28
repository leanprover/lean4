/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: E.W.Ayers
-/
import Lean.Meta.AppBuilder
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.Simp.Main
import Lean.Elab.Tactic.Rewrite
import Lean.Server.CodeActions
import Lean.Server.Edits

namespace Lean
open Elab Tactic Lsp Server

syntax (name := suggest) "suggest" : tactic

@[builtinTactic suggest]
def suggestTactic : Tactic := fun stx => do
  let newStx ← `(tactic| intros)
  let es : EditSuggestion := {
    stx := stx,
    replacement := newStx.raw,
    kind := "quickfix"
    description? := "this is a test tactic",
    stateAfter? := some (←getMCtx, ←getGoals)
  }
  es.save
  return ()


end Lean
