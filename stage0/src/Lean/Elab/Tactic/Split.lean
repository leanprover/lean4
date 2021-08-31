/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Split
import Lean.Elab.Tactic.Basic

namespace Lean.Elab.Tactic
open Meta

@[builtinTactic Lean.Parser.Tactic.split] def evalSplit : Tactic := fun stx =>
  -- TODO: process arguments
  liftMetaTactic fun mvarId => do
    if let some mvarIds ← splitTarget? mvarId then
      return mvarIds
    else
      throwError "'split' tactic failed"

end Lean.Elab.Tactic
