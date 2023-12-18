/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Cases
import Lean.Elab.PreDefinition.Basic

namespace Lean.Elab.WF
open Meta

/--
  Given a (dependent) tuple `t` (using `PSigma`) of the given arity.
  Return an array containing its "elements".
  Example: `mkTupleElems a 4` returns `#[a.1, a.2.1, a.2.2.1, a.2.2.2]`.
  -/
private def mkTupleElems (t : Expr) (arity : Nat) : Array Expr := Id.run do
  let mut result := #[]
  let mut t := t
  for _ in [:arity - 1] do
    result := result.push (mkProj ``PSigma 0 t)
    t := mkProj ``PSigma 1 t
  result.push t

/-- Create a unary application by packing the given arguments using `PSigma.mk` -/
partial def mkUnaryArg (type : Expr) (args : Array Expr) : MetaM Expr := do
  go 0 type
where
  go (i : Nat) (type : Expr) : MetaM Expr := do
    if i < args.size - 1 then
      let arg := args[i]!
      assert! type.isAppOfArity ``PSigma 2
      let us := type.getAppFn.constLevels!
      let α := type.appFn!.appArg!
      let β := type.appArg!
      assert! β.isLambda
      let type := β.bindingBody!.instantiate1 arg
      let rest ← go (i+1) type
      return mkApp4 (mkConst ``PSigma.mk us) α β arg rest
    else
      return args[i]!

/-- Unpacks a unary packed argument created with `mkUnaryArg`. -/
def unpackUnaryArg {m} [Monad m] [MonadError m] (arity : Nat) (e : Expr) : m (Array Expr) := do
  let mut e := e
  let mut args := #[]
  while args.size + 1 < arity do
    if e.isAppOfArity ``PSigma.mk 4 then
      args := args.push (e.getArg! 2)
      e := e.getArg! 3
    else
      throwError "Unexpected expression while unpacking n-ary argument"
  args := args.push e
  return args

private partial def mkPSigmaCasesOn (y : Expr) (codomain : Expr) (xs : Array Expr) (value : Expr) : MetaM Expr := do
  let mvar ← mkFreshExprSyntheticOpaqueMVar codomain
  let rec go (mvarId : MVarId) (y : FVarId) (ys : Array Expr) : MetaM Unit := do
    if ys.size < xs.size - 1 then
      let xDecl  ← xs[ys.size]!.fvarId!.getDecl
      let xDecl' ← xs[ys.size + 1]!.fvarId!.getDecl
      let #[s] ← mvarId.cases y #[{ varNames := [xDecl.userName, xDecl'.userName] }] | unreachable!
      go s.mvarId s.fields[1]!.fvarId! (ys.push s.fields[0]!)
    else
      let ys := ys.push (mkFVar y)
      mvarId.assign (value.replaceFVars xs ys)
  go mvar.mvarId! y.fvarId! #[]
  instantiateMVars mvar

/--
  Convert the given pre-definitions into unary functions.
  We "pack" the arguments using `PSigma`.
-/
partial def packDomain (fixedPrefix : Nat) (preDefs : Array PreDefinition) : MetaM (Array PreDefinition) := do
  let mut preDefsNew := #[]
  let mut arities := #[]
  let mut modified := false
  for preDef in preDefs do
    let (preDefNew, arity, modifiedCurr) ← lambdaTelescope preDef.value fun xs _ => do
      if xs.size == fixedPrefix then
        throwError "well-founded recursion cannot be used, '{preDef.declName}' does not take any (non-fixed) arguments"
      let arity := xs.size
      if arity > fixedPrefix + 1 then
        let bodyType ← instantiateForall preDef.type xs
        let mut d ← inferType xs.back
        let ys : Array Expr := xs[:fixedPrefix]
        let xs : Array Expr := xs[fixedPrefix:]
        for x in xs.pop.reverse do
          d ← mkAppOptM ``PSigma #[some (← inferType x), some (← mkLambdaFVars #[x] d)]
        withLocalDeclD (← mkFreshUserName `_x) d fun tuple => do
          let elems := mkTupleElems tuple xs.size
          let codomain := bodyType.replaceFVars xs elems
          let preDefNew:= { preDef with
            declName := preDef.declName ++ `_unary
            type := (← mkForallFVars (ys.push tuple) codomain)
          }
          addAsAxiom preDefNew
          return (preDefNew, arity, true)
      else
        return (preDef, arity, false)
    modified := modified || modifiedCurr
    arities := arities.push arity
    preDefsNew := preDefsNew.push preDefNew
  if !modified then
    return preDefs
  -- Update values
  for i in [:preDefs.size] do
    let preDef := preDefs[i]!
    let preDefNew := preDefsNew[i]!
    let valueNew ← lambdaTelescope preDef.value fun xs body => do
      let ys : Array Expr := xs[:fixedPrefix]
      let xs : Array Expr := xs[fixedPrefix:]
      let type ← instantiateForall preDefNew.type ys
      forallBoundedTelescope type (some 1) fun z codomain => do
        let z := z[0]!
        let newBody ← mkPSigmaCasesOn z codomain xs body
        mkLambdaFVars (ys.push z) (← packApplications newBody arities preDefsNew)
    let isBad (e : Expr) : Bool :=
      match isAppOfPreDef? e with
      | none   => false
      | some i => e.getAppNumArgs > fixedPrefix + 1 || preDefsNew[i]!.declName != preDefs[i]!.declName
    if let some bad := valueNew.find? isBad then
      if let some i := isAppOfPreDef? bad then
        throwErrorAt preDef.ref "well-founded recursion cannot be used, function '{preDef.declName}' contains application of function '{preDefs[i]!.declName}' with #{bad.getAppNumArgs} argument(s), but function has arity {arities[i]!}"
    preDefsNew := preDefsNew.set! i { preDefNew with value := valueNew }
  return preDefsNew
where
  /-- Return `some i` if `e` is a `preDefs[i]` application -/
  isAppOfPreDef? (e : Expr) : Option Nat := do
    let f := e.getAppFn
    guard f.isConst
    preDefs.findIdx? (·.declName == f.constName!)

  packApplications (e : Expr) (arities : Array Nat) (preDefsNew : Array PreDefinition) : MetaM Expr := do
    let pack (e : Expr) (funIdx : Nat) : MetaM Expr := do
      let f := e.getAppFn
      let args := e.getAppArgs
      let fNew := mkConst preDefsNew[funIdx]!.declName f.constLevels!
      let fNew := mkAppN fNew args[:fixedPrefix]
      let Expr.forallE _ d .. ← whnf (← inferType fNew) | unreachable!
      -- NB: Use whnf in case the type is not a manifest forall, but a definition around it
      let argNew ← mkUnaryArg d args[fixedPrefix:]
      return mkApp fNew argNew
    let rec
      visit (e : Expr) : MonadCacheT ExprStructEq Expr MetaM Expr := do
        checkCache { val := e : ExprStructEq } fun _ => Meta.withIncRecDepth do
          match e with
          | Expr.lam n d b c =>
            withLocalDecl n c (← visit d) fun x => do
              mkLambdaFVars (usedLetOnly := false) #[x] (← visit (b.instantiate1 x))
          | Expr.forallE n d b c =>
            withLocalDecl n c (← visit d) fun x => do
              mkForallFVars (usedLetOnly := false) #[x] (← visit (b.instantiate1 x))
          | Expr.letE n t v b _  =>
            withLetDecl n (← visit t) (← visit v) fun x => do
              mkLambdaFVars (usedLetOnly := false) #[x] (← visit (b.instantiate1 x))
          | Expr.proj n i s .. => return mkProj n i (← visit s)
          | Expr.mdata d b     => return mkMData d (← visit b)
          | Expr.app ..        => visitApp e
          | Expr.const ..      => visitApp e
          | e                  => return e,
      visitApp (e : Expr) : MonadCacheT ExprStructEq Expr MetaM Expr := e.withApp fun f args => do
        let args ← args.mapM visit
        if let some funIdx := isAppOfPreDef? f then
          let numArgs := args.size
          let arity   := arities[funIdx]!
          if numArgs < arity then
            -- Partial application
            let extra := arity - numArgs
            withDefault do forallBoundedTelescope (← inferType e) extra fun xs _ => do
              if xs.size != extra then
                return (mkAppN f args) -- It will fail later
              else
                mkLambdaFVars xs (← pack (mkAppN (mkAppN f args) xs) funIdx)
          else if numArgs > arity then
            -- Over application
            let r ← pack (mkAppN f args[:arity]) funIdx
            let rType ← inferType r
            -- Make sure the new auxiliary definition has only one argument.
            withLetDecl (← mkFreshUserName `aux) rType r fun aux =>
              mkLetFVars #[aux] (mkAppN aux args[arity:])
          else
            pack (mkAppN f args) funIdx
        else if args.isEmpty then
          return f
        else
          return mkAppN (← visit f) args
    visit e |>.run

end Lean.Elab.WF
