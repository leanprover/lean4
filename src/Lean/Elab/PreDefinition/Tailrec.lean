/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Elab.PreDefinition.WF.PackMutual
import Init.Tailrec

namespace Lean.Elab
open WF
open Meta

partial def solveMono (goal : MVarId) : MetaM Unit := goal.withContext do
  let type ← goal.getType
  if type.isForall then
    let (_, goal) ← goal.intro1P
    solveMono goal
    return

  let_expr Tailrec.mono α β inst f := type |
    throwError "Unexpected goal:{goal}"

  unless f.isLambda do
    throwError "Unexpected goal:{goal}"

  let failK :=
    lambdaBoundedTelescope f 1 fun _ t =>
      throwError "Recursive calls in non-tail position:{indentExpr t}"

  -- No recursive calls left
  if !f.bindingBody!.hasLooseBVars then
    let new_goals ← goal.applyConst ``Tailrec.mono_const
    unless new_goals.isEmpty do
      throwError "Left over goals"
    return

  -- A recursive call here
  if f.bindingBody!.isApp && f.bindingBody!.appFn! == .bvar 0 then
    let new_goals ← goal.applyConst ``Tailrec.mono_apply
    unless new_goals.isEmpty do
      throwError "Left over goals"
    return

  -- Manually handle PSigma.casesOn, as split doesn't
  match_expr f.bindingBody! with
  | PSigma.casesOn γ δ _motive x k =>
    if f.bindingBody!.appFn!.hasLooseBVars then
      failK
    let us := type.getAppFn.constLevels! ++ f.bindingBody!.getAppFn.constLevels!.tail
    let k' := f.updateLambdaE! f.bindingDomain! k
    let p := mkApp7 (.const ``Tailrec.mono_psigma_casesOn us) α β inst γ δ x k'
    let new_goals ← goal.apply p
    new_goals.forM solveMono
    return
  | _ => pure

  -- We could be more careful here and only split a match or ite that
  -- is right under the lambda, and maybe use `apply_ite`-style lemmas to avoid the more
  -- expesive splitter machinery. For now using `splitTarget` works fine.
  if let some mvarIds ← splitTarget? goal (splitIte := true) then
    mvarIds.forM solveMono
    return

  failK

private def replaceRecApps (recFnName : Name) (fixedPrefixSize : Nat) (F : Expr) (e : Expr) : Expr :=
  e.replace fun e =>
    if e.isAppOfArity recFnName fixedPrefixSize then
      some F
    else
      none

def derecursifyTailrec (fixedPrefixSize : Nat) (preDef : PreDefinition) :
    TermElabM PreDefinition := do
  forallBoundedTelescope preDef.type fixedPrefixSize fun prefixArgs type => do
    let type ← whnfForall type
    unless type.isForall do
      throwError "expected unary function type: {type}"
    -- TODO: Check these properties on the original function types
    let some (α, β) := type.arrow?
      | throwError "Termination by tailrecursion cannot handle dependent type:{indentExpr type}"
    let u ← getDecLevel α
    let v ← getDecLevel β
    let inst ← mapError (f := (m!"Termination by tailrecursion needs an inhabited codomain:{indentD ·}")) do
      synthInstance (mkApp (.const ``Inhabited [v.succ]) β)
    let value := mkApp3 (mkConst ``Lean.Tailrec.tailrec_fix [u, v]) α β inst

    let F ← withoutModifyingEnv do
      addAsAxiom preDef
      let value ←
        withLocalDeclD `F type fun f =>
          withLocalDeclD `x α fun x => do
            let val := preDef.value.beta (prefixArgs.push x)
            let val := replaceRecApps preDef.declName prefixArgs.size f val
            mkLambdaFVars #[f, x] val
      eraseRecAppSyntaxExpr value
    let value := .app value F

    -- Now try to prove the monotonicity
    let monoGoal := (← inferType value).bindingDomain!
    let mono ← mkFreshExprSyntheticOpaqueMVar monoGoal
    mapError (f := (m!"Could not prove function to be tailrecursive:{indentD ·}")) do
      solveMono mono.mvarId!
    let value := .app value (← instantiateMVars mono)

    let value ← mkLambdaFVars prefixArgs value
    return { preDef with value }

def tailRecursion (preDefs : Array PreDefinition) : TermElabM Unit := do
  let (fixedPrefixSize, argsPacker, unaryPreDef) ← mkUnaryPreDef preDefs
  let preDefNonRec : PreDefinition ← derecursifyTailrec fixedPrefixSize unaryPreDef
  addPreDefsFromUnary preDefs fixedPrefixSize argsPacker preDefNonRec (hasInduct := false)

end Lean.Elab
