/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.SymEval
import Lean.Elab.Tactic.Basic

namespace Lean.Elab.Tactic

open Meta Tactic

@[builtin_tactic Lean.Parser.Tactic.seval] def evalSEval : Tactic := fun _ => withMainContext do
  let mvarId ← getMainGoal
  let result? ← sevalTarget mvarId {}
  match result? with
  | none => replaceMainGoal []
  | some mvarId => replaceMainGoal [mvarId]

end Lean.Elab.Tactic
