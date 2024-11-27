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

  let_expr Tailrec.mono α β γ inst₁ inst₂ f := type |
    throwError "Unexpected goal:{goal}"

  unless f.isLambda do
    throwError "Unexpected goal:{goal}"

  let failK :=
    lambdaBoundedTelescope f 1 fun _ t => do
      trace[Elab.definition.tailrec] "Failing at goal{goal}"
      throwError "Recursive call in non-tail position:{indentExpr t}"

  -- No recursive calls left
  if !f.bindingBody!.hasLooseBVars then
    let new_goals ← goal.applyConst ``Tailrec.mono_const
    unless new_goals.isEmpty do
      throwError "Left over goals"
    return

  -- A recursive call directly here
  if f.bindingBody!.isApp && f.bindingBody!.appFn! == .bvar 0 then
    let new_goals ← goal.applyConst ``Tailrec.mono_apply
    unless new_goals.isEmpty do
      throwError "Left over goals"
    return

  -- Float letE to the environment
  if let .letE n t v b _nonDep := f.bindingBody! then
    if t.hasLooseBVars || v.hasLooseBVars then
      failK
    withLetDecl n t v fun x => do
      let b' := f.updateLambdaE! f.bindingDomain! (b.instantiate1 x)
      let goal' ← mkFreshExprSyntheticOpaqueMVar (mkApp type.appFn! b')
      goal.assign (← mkLetFVars #[x] goal')
      solveMono goal'.mvarId!
    return

  -- Manually handle PSigma.casesOn, as split doesn't
  match_expr f.bindingBody! with
  | PSigma.casesOn δ ε _motive p k =>
    if f.bindingBody!.appFn!.hasLooseBVars then
      failK
    let us := type.getAppFn.constLevels! ++ f.bindingBody!.getAppFn.constLevels!.tail
    let k' := f.updateLambdaE! f.bindingDomain! k
    let p := mkApp9 (.const ``Tailrec.mono_psigma_casesOn us) α β γ inst₁ inst₂ δ ε p k'
    let new_goals ← goal.apply p
    new_goals.forM solveMono
    return
  | PSum.casesOn δ ε γ p k₁ k₂ =>
    if f.bindingBody!.appFn!.appFn!.hasLooseBVars then
      failK
    -- Careful juggling of universes
    let us := type.getAppFn.constLevels! ++ f.bindingBody!.getAppFn.constLevels!.tail
    let k₁' := f.updateLambdaE! f.bindingDomain! k₁
    let k₂' := f.updateLambdaE! f.bindingDomain! k₂
    let p := mkAppN (.const ``Tailrec.mono_psum_casesOn us) #[α, β, inst₁, δ, ε, γ, p, inst₂, k₁', k₂']
    check p
    let new_goals ← goal.apply p
    new_goals.forM solveMono
    return
  | _ => pure

  -- We could be more careful here and only split a match or ite that
  -- is right under the lambda, and maybe use `apply_ite`-style lemmas to avoid the more
  -- expensive splitter machinery. For now using `splitTarget` works fine.
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
    let α := type.bindingDomain!

    let F ← withoutModifyingEnv do
      addAsAxiom preDef
      let value ←
        withLocalDeclD `F type fun f =>
          withLocalDeclD `x α fun x => do
            let val := preDef.value.beta (prefixArgs.push x)
            let val := replaceRecApps preDef.declName prefixArgs.size f val
            mkLambdaFVars #[f, x] val
      eraseRecAppSyntaxExpr value

    -- TODO: Check these properties on the original function types
    let value ← mapError (f := (m!"Termination by tailrecursion needs a nonempty codomain:{indentD ·}")) do
      mkAppOptM ``Lean.Tailrec.tailrec_fix #[α, .none, .none, F]

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

builtin_initialize Lean.registerTraceClass `Elab.definition.tailrec
