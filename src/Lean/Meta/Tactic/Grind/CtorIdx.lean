/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module
prelude
public import Lean.Meta.Tactic.Grind.Types
public import Init.Grind.Propagator
import Init.Simproc
import Init.Grind.Norm
import Lean.Meta.Tactic.Grind.PropagatorAttr
import Lean.Meta.Tactic.Grind.Propagate
import Lean.Meta.Tactic.Grind.Internalize
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Anchor
import Lean.Meta.Tactic.Grind.EqResolution
import Lean.Meta.Tactic.Grind.SynthInstance
public section
namespace Lean.Meta.Grind

/--
Propagation for `T.ctorIdx`. See the `reduceCtorIdx` simproc.
-/
def propagateCtorIdxUp (e : Expr) : GoalM Unit := e.withApp fun f xs => do
  -- TODO: Faster to
  let some fnName := f.constName? | return
  let .str indName "ctorIdx" := fnName | return
  trace_goal[grind.debug] "propagateCtorIdxUp {e}"
  let some indInfo ← isInductive? indName | return
  unless xs.size == indInfo.numParams + indInfo.numIndices + 1 do return
  let a := xs.back!
  let aNode ← getRootENode a
  unless aNode.ctor do return
  let some conInfo ← isConstructorApp? aNode.self | return
  if aNode.heqProofs then
    -- Bail out on heterogeneous equality. Can we do better?
    unless (← hasSameType a aNode.self) do
      return
  let e' ← shareCommon (mkNatLit conInfo.cidx)
  internalize e' 0
  pushEq e e' (← mkCongrArg e.appFn! (← mkEqProof a aNode.self))
  trace_goal[grind.debug] "pushed {e} = {e'}"

end Lean.Meta.Grind
