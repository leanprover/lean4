/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.ProjFns
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Internalize

namespace Lean.Meta.Grind

/--
If `parent` is a projection-application `proj_i c`,
check whether the root of the equivalence class containing `c` is a constructor-application `ctor ... a_i ...`.
If so, internalize the term `proj_i (ctor ... a_i ...)` and add the equality `proj_i (ctor ... a_i ...) = a_i`.
-/
def propagateProjEq (parent : Expr) : GoalM Unit := do
  let .const declName _ := parent.getAppFn | return ()
  let some info ← getProjectionFnInfo? declName | return ()
  unless info.numParams + 1 == parent.getAppNumArgs do return ()
  -- It is wasteful to add equation if `parent` is not the root of its congruence class
  unless (← isCongrRoot parent) do return ()
  let arg := parent.appArg!
  let ctor ← getRoot arg
  unless ctor.isAppOf info.ctorName do return ()
  let parentNew ← if isSameExpr arg ctor then
    pure parent
  else
    let parentNew ← shareCommon (mkApp parent.appFn! ctor)
    internalize parentNew (← getGeneration parent)
    pure parentNew
  trace_goal[grind.debug.proj] "{parentNew}"
  let idx := info.numParams + info.i
  unless idx < ctor.getAppNumArgs do return ()
  let v := ctor.getArg! idx
  pushEq parentNew v (← mkEqRefl v)

end Lean.Meta.Grind
