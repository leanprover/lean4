/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.PreDefinition.Basic

namespace Lean.Elab.WF
open Meta

private def getDomains (preDefs : Array PreDefinition) : Array Expr :=
  preDefs.map fun preDef => preDef.type.bindingDomain!

/-- Combine different function domains `ds` using `PSum`s -/
private def mkNewDomain (ds : Array Expr) : MetaM Expr := do
  let mut r := ds.back
  for d in ds.pop.reverse do
    r ← mkAppM ``PSum #[d, r]
  return r

private def getCodomainLevel (preDef : PreDefinition) : MetaM Level :=
  forallBoundedTelescope preDef.type (some 1) fun _ body => getLevel body

/--
  Return the universe level for the codomain of the given definitions.
  This method produces an error if the codomains are in different universe levels.
-/
private def getCodomainsLevel (preDefs : Array PreDefinition) : MetaM Level := do
  let r ← getCodomainLevel preDefs[0]
  for preDef in preDefs[1:] do
    unless (← isLevelDefEq r (← getCodomainLevel preDef)) do
      throwError "invalid mutual definition, result types must be in the same universe level"
  return r

/--
  Create the codomain for the new function that "combines" different `preDefs`
  See: `packMutual`
-/
private partial def mkNewCoDomain (x : Expr) (preDefs : Array PreDefinition) : MetaM Expr := do
  let u ← getCodomainsLevel preDefs
  let rec go (x : Expr) (i : Nat) : MetaM Expr := do
    if i < preDefs.size - 1 then
      let xType ← whnfD (← inferType x)
      assert! xType.isAppOfArity ``PSum 2
      let xTypeArgs := xType.getAppArgs
      let casesOn := mkConst (mkCasesOnName ``PSum) (mkLevelSucc u :: xType.getAppFn.constLevels!)
      let casesOn := mkAppN casesOn xTypeArgs -- parameters
      let casesOn := mkApp casesOn (← mkLambdaFVars #[x] (mkSort u)) -- motive
      let casesOn := mkApp casesOn x -- major
      let minor1 ← withLocalDeclD (← mkFreshUserName `_x) xTypeArgs[0] fun x =>
        mkLambdaFVars #[x] (preDefs[i].type.bindingBody!.instantiate1 x)
      let minor2 ← withLocalDeclD (← mkFreshUserName `_x) xTypeArgs[1] fun x => do
        mkLambdaFVars #[x] (← go x (i+1))
      return mkApp2 casesOn minor1 minor2
    else
      return preDefs[i].type.bindingBody!.instantiate1 x
  go x 0

/--
  Combine/pack the values of the different definitions in a single value
  `x` is `PSum`, and we use `PSum.casesOn` to select the appropriate `preDefs.value`.
  See: `packMutual`.
  Remark: this method does not replace the nested recursive `preDefs` applications.
  This step is performed by `transform` with the following `post` method.
 -/
private partial def packValues (x : Expr) (codomain : Expr) (preDefs : Array PreDefinition) : MetaM Expr := do
  let mvar ← mkFreshExprSyntheticOpaqueMVar codomain
  let rec go (mvarId : MVarId) (x : FVarId) (i : Nat) : MetaM Unit := do
    if i < preDefs.size - 1 then
      let #[s₁, s₂] ← cases mvarId x | unreachable!
      assignExprMVar s₁.mvarId (mkApp preDefs[i].value s₁.fields[0]).headBeta
      go s₂.mvarId s₂.fields[0].fvarId! (i+1)
    else
      assignExprMVar mvarId (mkApp preDefs[i].value (mkFVar x)).headBeta
  go mvar.mvarId! x.fvarId! 0
  instantiateMVars mvar

/--
  Auxiliary function for replacing nested `preDefs` recursive calls in `e` with the new function `newFn`.
  See: `packMutual`
-/
private partial def post (preDefs : Array PreDefinition) (domain : Expr) (newFn : Name) (e : Expr) : MetaM TransformStep := do
  if let Expr.app (Expr.const declName us _) arg _ := e then
    if let some fidx := preDefs.findIdx? (·.declName == declName) then
      let rec mkNewArg (i : Nat) (type : Expr) : MetaM Expr := do
        if i == preDefs.size - 1 then
          return arg
        else
          (← whnfD type).withApp fun f args => do
            assert! args.size == 2
            if i == fidx then
              return mkApp3 (mkConst ``PSum.inl f.constLevels!) args[0] args[1] arg
            else
              let r ← mkNewArg (i+1) args[1]
              return mkApp3 (mkConst ``PSum.inr f.constLevels!) args[0] args[1] r
      return TransformStep.done <| mkApp (mkConst newFn us) (← mkNewArg 0 domain)
  return TransformStep.done e

/--
  If `preDefs.size > 1`, combine different functions in a single one using `PSum`.
  This method assumes all `preDefs` have arity 1, and have already been processed using `packDomain`.
  Here is a small example. Suppose the input is
  ```
  f x :=
    match x.2.1, x.2.2.1, x.2.2.2 with
    | 0, a, b => a
    | Nat.succ n, a, b => (g ⟨x.1, n, a, b⟩).fst
  g x :=
    match x.2.1, x.2.2.1, x.2.2.2 with
    | 0, a, b => (a, b)
    | Nat.succ n, a, b => (h ⟨x.1, n, a, b⟩, a)
  h x =>
    match x.2.1, x.2.2.1, x.2.2.2 with
    | 0, a, b => b
    | Nat.succ n, a, b => f ⟨x.1, n, a, b⟩
  ```
  this method produces the following pre definition
  ```
  f._mutual x :=
    PSum.casesOn x
      (fun val =>
        match val.2.1, val.2.2.1, val.2.2.2 with
        | 0, a, b => a
        | Nat.succ n, a, b => (f._mutual (PSum.inr (PSum.inl ⟨val.1, n, a, b⟩))).fst
      fun val =>
        PSum.casesOn val
          (fun val =>
            match val.2.1, val.2.2.1, val.2.2.2 with
            | 0, a, b => (a, b)
            | Nat.succ n, a, b => (f._mutual (PSum.inr (PSum.inr ⟨val.1, n, a, b⟩)), a)
          fun val =>
            match val.2.1, val.2.2.1, val.2.2.2 with
            | 0, a, b => b
            | Nat.succ n, a, b =>
              f._mutual (PSum.inl ⟨val.1, n, a, b⟩)
  ```
 -/
def packMutual (preDefs : Array PreDefinition) : MetaM PreDefinition := do
  if preDefs.size == 1 then return preDefs[0]
  let domain ← mkNewDomain (getDomains preDefs)
  withLocalDeclD (← mkFreshUserName `_x) domain fun x => do
    let codomain ← mkNewCoDomain x preDefs
    let type ← mkForallFVars #[x] codomain
    trace[Elab.definition.wf] "packMutual type: {type}"
    let value ← packValues x codomain preDefs
    trace[Elab.definition.wf] "packMutual value: {value}"
    let newFn := preDefs[0].declName ++ `_mutual
    let preDefNew := { preDefs[0] with declName := newFn, type, value }
    addAsAxiom preDefNew
    let value ← transform value (post := post preDefs domain newFn)
    let value ← mkLambdaFVars #[x] value
    return { preDefNew with value }

end Lean.Elab.WF
