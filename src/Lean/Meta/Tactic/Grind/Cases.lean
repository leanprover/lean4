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
It is also used for "case-splitting" on terms during the search.

It differs from the user-facing Lean `cases` tactic in the following ways:

- It avoids unnecessary `revert` and `intro` operations.

- It does not introduce new local declarations for each minor premise. Instead, the `grind` tactic preprocessor is responsible for introducing them.

- If the major premise type is an indexed family, auxiliary declarations and (heterogeneous) equalities are introduced.
  However, these equalities are not resolved using `unifyEqs`. Instead, the `grind` tactic employs union-find and
  congruence closure to process these auxiliary equalities. This approach avoids applying substitution to propositions
  that have already been internalized by `grind`.
-/
def cases (mvarId : MVarId) (e : Expr) : MetaM (List MVarId) := mvarId.withContext do
  let tag ← mvarId.getTag
  let type ← whnf (← inferType e)
  let .const declName _ := type.getAppFn | throwInductiveExpected type
  let .inductInfo _ ← getConstInfo declName | throwInductiveExpected type
  let recursorInfo ← mkRecursorInfo (mkCasesOnName declName)
  let k (mvarId : MVarId) (fvarId : FVarId) (indices : Array FVarId) : MetaM (List MVarId) := do
    let indicesExpr := indices.map mkFVar
    let recursor ← mkRecursorAppPrefix mvarId `grind.cases fvarId recursorInfo indicesExpr
    let mut recursor := mkApp (mkAppN recursor indicesExpr) (mkFVar fvarId)
    let mut recursorType ← inferType recursor
    let mut mvarIdsNew := #[]
    let mut idx := 1
    for _ in [:recursorInfo.numMinors] do
      let .forallE _ targetNew recursorTypeNew _ ← whnf recursorType
        | throwTacticEx `grind.cases mvarId "unexpected recursor type"
      recursorType := recursorTypeNew
      let tagNew := if recursorInfo.numMinors > 1 then Name.num tag idx else tag
      let mvar ← mkFreshExprSyntheticOpaqueMVar targetNew tagNew
      recursor := mkApp recursor mvar
      let mvarIdNew ← mvar.mvarId!.tryClearMany (indices.push fvarId)
      mvarIdsNew := mvarIdsNew.push mvarIdNew
      idx := idx + 1
    mvarId.assign recursor
    return mvarIdsNew.toList
  if recursorInfo.numIndices > 0 then
    let s ← generalizeIndices' mvarId e
    s.mvarId.withContext do
      k s.mvarId s.fvarId s.indicesFVarIds
  else if let .fvar fvarId := e then
    k mvarId fvarId #[]
  else
    let mvarId ← mvarId.assert (← mkFreshUserName `x) type e
    let (fvarId, mvarId) ← mvarId.intro1
    mvarId.withContext do k mvarId fvarId #[]
where
  throwInductiveExpected {α} (type : Expr) : MetaM α := do
    throwTacticEx `grind.cases mvarId m!"(non-recursive) inductive type expected at {e}{indentExpr type}"

end Lean.Meta.Grind
