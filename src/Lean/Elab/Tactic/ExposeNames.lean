/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.ExposeNames
import Lean.Elab.Tactic.Basic

namespace Lean.Elab.Tactic

@[builtin_tactic Lean.Parser.Tactic.exposeNames] def evalExposeNames : Tactic := fun _ =>
  liftMetaTactic1 fun mvarId => mvarId.exposeNames

end Lean.Elab.Tactic
