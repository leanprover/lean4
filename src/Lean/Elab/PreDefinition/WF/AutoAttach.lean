/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
prelude
import Lean.Meta.Transform
import Lean.Meta.Match.MatcherApp.Basic
import Lean.Elab.Tactic.Simp

open Lean Meta

namespace Lean.Elab.WF

builtin_initialize wfPreprocessSimpExtension : SimpExtension ←
  registerSimpAttr `wf_preprocess
    "(not yet functional)"

end Lean.Elab.WF
