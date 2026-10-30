/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude
public import Lean.Meta.Eqns
public import Lean.Meta.Tactic.Rfl
public import Lean.Meta.Tactic.Intro
import Lean.Elab.PreDefinition.EqnsUtils

public section

namespace Lean.Meta

/--
Returns the "const unfold" theorem (`f.eq_unfold`) for the given declaration.
This is not extensible, and always builds on the unfold theorem (`f.eq_def`).
-/
def getConstUnfoldEqnFor? (declName : Name) : MetaM (Option Name) := do
  if (← getUnfoldEqnFor? (nonRec := true) declName).isNone then
    trace[ReservedNameAction] "getConstUnfoldEqnFor? {declName} failed, no unfold theorem available"
    return none
  let name := mkEqLikeNameFor (← getEnv) declName eqUnfoldThmSuffix
  realizeConst declName name <| withEqnOptions declName do
    -- we have to call `getUnfoldEqnFor?` again to make `unfoldEqnName` available in this context
    let some unfoldEqnName ← getUnfoldEqnFor? (nonRec := true) declName | unreachable!
    let info ← getConstInfo unfoldEqnName
    let type ← forallTelescope info.type fun xs eq => do
      let some (_, lhs, rhs) := eq.eq? | throwError "Unexpected unfold theorem type {info.type}"
      unless lhs.getAppFn.isConstOf declName do
        throwError "Unexpected unfold theorem type {info.type}"
      unless lhs.getAppArgs == xs do
        throwError "Unexpected unfold theorem type {info.type}"
      let type ← mkEq lhs.getAppFn (← mkLambdaFVars xs rhs)
      return type
    let value ← withNewMCtxDepth do
      let main ← mkFreshExprSyntheticOpaqueMVar type
      if (← Elab.Eqns.tryURefl main.mvarId!) then -- try to make a rfl lemma if possible
        instantiateMVars main
      else forallTelescope info.type fun xs _eq => do
        let mut proof ← mkConstWithLevelParams unfoldEqnName
        proof := mkAppN proof xs
        for x in xs.reverse do
          proof ← mkLambdaFVars #[x] proof
          proof ← mkAppM ``funext #[proof]
        return proof
    addDecl <| Declaration.thmDecl {
      name, type, value
      levelParams := info.levelParams
    }
    inferDefEqAttr name
  return some name


builtin_initialize
  registerReservedNameAction fun name => do
    let .str p s := name | return false
    if s == eqUnfoldThmSuffix then
      let env := (← getEnv).setExporting false
      for p in [p, privateToUserName p] do
        if env.isSafeDefinition p then
          return (← MetaM.run' <| getConstUnfoldEqnFor? p).isSome
    return false

end Lean.Meta
