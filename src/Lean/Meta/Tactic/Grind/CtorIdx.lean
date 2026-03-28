/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Constructions.CtorIdx
import Lean.Meta.CtorIdxHInj
public section
namespace Lean.Meta.Grind

/--
Propagation for `T.ctorIdx`. Cf. the `reduceCtorIdx` simproc.
-/
def propagateCtorIdxUp (e : Expr) : GoalM Unit := e.withApp fun f xs => do
  let some fnName := f.constName? | return
  let some indInfo ← isCtorIdx? fnName | return
  unless xs.size == indInfo.numParams + indInfo.numIndices + 1 do return
  let a := xs.back!
  let aNode ← getRootENode a
  -- NB: This does not work for `Nat.ctorIdx`, as grind normalizes `Nat.succ` to `_ + k`.
  -- But we have `attribute [grind] Nat.ctorIdx` to handle that case.
  unless aNode.ctor do
    return
  let some conInfo ← isConstructorApp? aNode.self | return
  if aNode.heqProofs then
    unless (← hasSameType a aNode.self) do
      let b := aNode.self
      let gen := max (← getGeneration a) (← getGeneration b)
      -- Handle heterogeneous equality case
      -- We add a suitable invocation of the `.ctorIdx.hinj` theorem
      let aType ← whnfD (← inferType a)
      let bType ← whnfD (← inferType b)
      assert! aType.isAppOfArity indInfo.name (indInfo.numParams + indInfo.numIndices)
      -- both types should be headed by the same type former
      unless bType.isAppOfArity indInfo.name (indInfo.numParams + indInfo.numIndices) do return
      let us := aType.getAppFn.constLevels!
      let hinjName := mkCtorIdxHInjTheoremNameFor indInfo.name
      unless (← getEnv).containsOnBranch hinjName do
        let _ ← executeReservedNameAction hinjName
      let proof := mkConst hinjName us
      let proof := mkApp (mkAppN proof aType.getAppArgs) a
      let proof := mkApp (mkAppN proof bType.getAppArgs) b
      addNewRawFact proof (← inferType proof) gen (.inj (.decl hinjName))
      return
  -- Homogeneous case
  let e' ← shareCommon (mkNatLit conInfo.cidx)
  internalize e' 0
  -- We used `mkExpectedPropHint` so that the inferred type of the proof matches the goal,
  -- to satisfy `debug.grind` checks
  pushEq e e' (mkExpectedPropHint (← mkCongrArg e.appFn! (← mkEqProof a aNode.self)) (← mkEq e e'))

end Lean.Meta.Grind
