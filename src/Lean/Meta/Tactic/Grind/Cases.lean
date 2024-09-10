/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Cases

namespace Lean.Meta.Grind
/--
The `grind` tactic includes an auxiliary `cases` tactic that is not intended for direct use by users.
This method implements it.
This tactic is automatically applied when introducing local declarations with a type tagged with `[grind_cases]`.
It differs from the user-facing Lean `cases` tactic in the following ways:

- It avoids unnecessary `revert` and `intro` operations.

- It does not introduce new local declarations for each minor premise. Instead, the `grind` tactic preprocessor is responsible for introducing them.

- It assumes that the major premise (i.e., the parameter `fvarId`) is the latest local declaration in the current goal.

- If the major premise type is an indexed family, auxiliary declarations and (heterogeneous) equalities are introduced.
  However, these equalities are not resolved using `unifyEqs`. Instead, the `grind` tactic employs union-find and
  congruence closure to process these auxiliary equalities. This approach avoids applying substitution to propositions
  that have already been internalized by `grind`.
-/
def cases (mvarId : MVarId) (fvarId : FVarId) : MetaM (List MVarId) := mvarId.withContext do
  let tag ← mvarId.getTag
  let type ← whnf (← fvarId.getType)
  let .const declName _ := type.getAppFn | throwInductiveExpected type
  let .inductInfo _ ← getConstInfo declName | throwInductiveExpected type
  let recursorInfo ← mkRecursorInfo (mkCasesOnName declName)
  let k (mvarId : MVarId) (fvarId : FVarId) (indices : Array Expr) (clearMajor : Bool) : MetaM (List MVarId) := do
    let recursor ← mkRecursorAppPrefix mvarId `grind.cases fvarId recursorInfo indices
    let mut recursor := mkApp (mkAppN recursor indices) (mkFVar fvarId)
    let mut recursorType ← inferType recursor
    let mut mvarIdsNew := #[]
    for _ in [:recursorInfo.numMinors] do
      let .forallE _ targetNew recursorTypeNew _ ← whnf recursorType
        | throwTacticEx `grind.cases mvarId "unexpected recursor type"
      recursorType := recursorTypeNew
      let mvar ← mkFreshExprSyntheticOpaqueMVar targetNew tag
      recursor := mkApp recursor mvar
      let mvarIdNew ← if clearMajor then
        mvar.mvarId!.clear fvarId
      else
        pure mvar.mvarId!
      mvarIdsNew := mvarIdsNew.push mvarIdNew
    mvarId.assign recursor
    return mvarIdsNew.toList
  if recursorInfo.numIndices > 0 then
    let s ← generalizeIndices mvarId fvarId
    s.mvarId.withContext do
      k s.mvarId s.fvarId (s.indicesFVarIds.map mkFVar) (clearMajor := false)
  else
    let indices ← getMajorTypeIndices mvarId `grind.cases recursorInfo type
    k mvarId fvarId indices (clearMajor := true)
where
  throwInductiveExpected {α} (type : Expr) : MetaM α := do
    throwTacticEx `grind.cases mvarId m!"(non-recursive) inductive type expected at {mkFVar fvarId}{indentExpr type}"

end Lean.Meta.Grind
