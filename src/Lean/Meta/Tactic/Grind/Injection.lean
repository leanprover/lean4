/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.CtorRecognizer
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Clear

namespace Lean.Meta.Grind
/--
The `grind` tactic includes an auxiliary `injection?` tactic that is not intended for direct use by users.
This tactic is automatically applied when introducing non-dependent propositions.
It differs from the user-facing Lean `injection` tactic in the following ways:

- It does not introduce new propositions. Instead, the `grind` tactic preprocessor is responsible for introducing them.
- It assumes that `fvarId` is the latest local declaration in the current goal.
- It does not handle cases where the constructors are different because the simplifier already reduces such equalities to `False`.
- It does not have support for heterogeneous equality. Recall that the simplifier already reduces them to `Eq` if
  the types are definitionally equal.
-/
def injection? (mvarId : MVarId) (fvarId : FVarId) : MetaM (Option MVarId) := mvarId.withContext do
  let decl ← fvarId.getDecl
  let_expr Eq _ a b := decl.type | return none
  match (← isConstructorAppCore? a), (← isConstructorAppCore? b) with
  | some aCtor, some bCtor =>
    if aCtor.name != bCtor.name then return none -- Simplifier handles this case
    let target ← mvarId.getType
    let val ← mkNoConfusion target (mkFVar fvarId)
    let .forallE _ targetNew _ _ ← whnfD (← inferType val) | return none
    let targetNew := targetNew.headBeta
    let tag ← mvarId.getTag
    let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew tag
    mvarId.assign (mkApp val mvarNew)
    return some (← mvarNew.mvarId!.clear fvarId)
  | _, _ => return none

end Lean.Meta.Grind
