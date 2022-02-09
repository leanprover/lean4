/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.PreDefinition.Basic

namespace Lean.Elab.WF
open Meta

/--
  Given a (dependent) tuple `t` (using `PSigma`) of the given arity.
  Return an array containing its "elements".
  Example: `mkTupleElems a 4` returns `#[a.1, a.2.1, a.2.2.1, a.2.2.2]`.
  -/
private def mkTupleElems (t : Expr) (arity : Nat) : Array Expr := Id.run <| do
  let mut result := #[]
  let mut t := t
  for i in [:arity - 1] do
    result := result.push (mkProj ``PSigma 0 t)
    t := mkProj ``PSigma 1 t
  result.push t

/-- Create a unary application by packing the given arguments using `PSigma.mk` -/
partial def mkUnaryArg (type : Expr) (args : Array Expr) : MetaM Expr := do
  go 0 type
where
  go (i : Nat) (type : Expr) : MetaM Expr := do
    if i < args.size - 1 then
      let arg := args[i]
      assert! type.isAppOfArity ``PSigma 2
      let us := type.getAppFn.constLevels!
      let α := type.appFn!.appArg!
      let β := type.appArg!
      assert! β.isLambda
      let type := β.bindingBody!.instantiate1 arg
      let rest ← go (i+1) type
      return mkApp4 (mkConst ``PSigma.mk us) α β arg rest
    else
      return args[i]

private partial def mkPSigmaCasesOn (y : Expr) (codomain : Expr) (xs : Array Expr) (value : Expr) : MetaM Expr := do
  let mvar ← mkFreshExprSyntheticOpaqueMVar codomain
  let rec go (mvarId : MVarId) (y : FVarId) (ys : Array Expr) : MetaM Unit := do
    if ys.size < xs.size - 1 then
      let xDecl  ← getLocalDecl xs[ys.size].fvarId!
      let xDecl' ← getLocalDecl xs[ys.size + 1].fvarId!
      let #[s] ← cases mvarId y #[{ varNames := [xDecl.userName, xDecl'.userName] }] | unreachable!
      go s.mvarId s.fields[1].fvarId! (ys.push s.fields[0])
    else
      let ys := ys.push (mkFVar y)
      assignExprMVar mvarId (value.replaceFVars xs ys)
  go mvar.mvarId! y.fvarId! #[]
  instantiateMVars mvar

/--
  Convert the given pre-definitions into unary functions.
  We "pack" the arguments using `PSigma`.
-/
def packDomain (preDefs : Array PreDefinition) : MetaM (Array PreDefinition) := do
  let mut preDefsNew := #[]
  let mut arities := #[]
  let mut modified := false
  for preDef in preDefs do
    let (preDefNew, arity, modifiedCurr) ← lambdaTelescope preDef.value fun xs body => do
      if xs.size == 0 then
        throwError "well-founded recursion cannot be used, '{preDef.declName}' does not take any arguments"
      if xs.size > 1 then
        let bodyType ← instantiateForall preDef.type xs
        let mut d ← inferType xs.back
        for x in xs.pop.reverse do
          d ← mkAppOptM ``PSigma #[some (← inferType x), some (← mkLambdaFVars #[x] d)]
        withLocalDeclD (← mkFreshUserName `_x) d fun tuple => do
          let elems := mkTupleElems tuple xs.size
          let codomain := bodyType.replaceFVars xs elems
          let preDefNew:= { preDef with
            declName := preDef.declName ++ `_unary
            type := (← mkForallFVars #[tuple] codomain)
          }
          addAsAxiom preDefNew
          return (preDefNew, xs.size, true)
      else
        return (preDef, 1, false)
    modified := modified || modifiedCurr
    arities := arities.push arity
    preDefsNew := preDefsNew.push preDefNew
  if !modified then
    return preDefs
  /- Return `some i` if `e` is a `preDefs[i]` application -/
  let isAppOfPreDef? (e : Expr) : OptionM Nat := do
    let f := e.getAppFn
    guard f.isConst
    preDefs.findIdx? (·.declName == f.constName!)
  /- Return `some i` if `e` is a `preDefs[i]` application with `arities[i]` arguments.  -/
  let isTargetApp? (e : Expr) : OptionM Nat := do
    let i ← isAppOfPreDef? e
    guard (e.getAppNumArgs == arities[i])
    return i
  -- Update values
  for i in [:preDefs.size] do
    let preDef := preDefs[i]
    let preDefNew := preDefsNew[i]
    let arity := arities[i]
    let valueNew ← lambdaTelescope preDef.value fun xs body => do
      forallBoundedTelescope preDefNew.type (some 1) fun y codomain => do
        let y := y[0]
        let newBody ← mkPSigmaCasesOn y codomain xs body
        let visit (e : Expr) : MetaM TransformStep := do
          if let some idx := isTargetApp? e |>.run then
            let f := e.getAppFn
            let fNew := mkConst preDefsNew[idx].declName f.constLevels!
            let Expr.forallE _ d .. ← inferType fNew | unreachable!
            let argNew ← mkUnaryArg d e.getAppArgs
            return TransformStep.done <| mkApp fNew argNew
          else
            return TransformStep.done e
        mkLambdaFVars #[y] (← transform newBody (post := visit))
    let isBad (e : Expr) : Bool :=
      match isAppOfPreDef? e with
      | none   => false
      | some i => e.getAppNumArgs > 1 || preDefsNew[i].declName != preDefs[i].declName
    if let some bad := valueNew.find? isBad then
      if let some i := isAppOfPreDef? bad then
        throwErrorAt preDef.ref "well-founded recursion cannot be used, function '{preDef.declName}' contains application of function '{preDefs[i].declName}' with #{bad.getAppNumArgs} argument(s), but function has arity {arities[i]}"
    preDefsNew := preDefsNew.set! i { preDefNew with value := valueNew }
  return preDefsNew

end Lean.Elab.WF
