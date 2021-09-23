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
private def mkTupleElems (t : Expr) (arity : Nat) : Array Expr := do
  let mut result := #[]
  let mut t := t
  for i in [:arity - 1] do
    result := result.push (mkProj ``PSigma 0 t)
    t := mkProj ``PSigma 1 t
  result.push t

/-- Create a unary application by packing the given arguments using `PSigma.mk` -/
private partial def mkUnaryApp (unaryFn : Expr) (args : Array Expr) : MetaM Expr := do
  let Expr.forallE _ d .. ← inferType unaryFn | unreachable!
  go 0 d
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
      if arity > 1 then
        forallBoundedTelescope preDefNew.type (some 1) fun y _ => do
          let newBody := body.replaceFVars xs (mkTupleElems y[0] xs.size)
          trace[Elab.definition.wf] "newBody: {newBody}"
          let visit (e : Expr) : MetaM TransformStep := do
            if let some idx := isTargetApp? e |>.run then
              let f := e.getAppFn
              let fNew := mkConst preDefsNew[idx].declName f.constLevels!
              let argNew ← mkUnaryApp fNew e.getAppArgs
              return TransformStep.done <| mkApp fNew argNew
            else
              return TransformStep.done e
          mkLambdaFVars y (← transform newBody (post := visit))
      else
        preDef.value
    if let some bad := valueNew.find? fun e => isAppOfPreDef? e |>.isSome then
      if let some i := isAppOfPreDef? bad then
        throwErrorAt preDef.ref "well-founded recursion cannot be used, function '{preDef.declName}' contains application of function '{preDefs[i].declName}' with #{bad.getAppNumArgs} argument(s), but function has arity {arities[i]}"
    preDefsNew := preDefsNew.set! i { preDefNew with value := valueNew }
  return preDefsNew

end Lean.Elab.WF
