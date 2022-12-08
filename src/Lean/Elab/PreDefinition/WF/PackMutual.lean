/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Cases
import Lean.Elab.PreDefinition.Basic

namespace Lean.Elab.WF
open Meta

/-- Combine different function domains `ds` using `PSum`s -/
private def mkNewDomain (ds : Array Expr) : MetaM Expr := do
  let mut r := ds.back
  for d in ds.pop.reverse do
    r ← mkAppM ``PSum #[d, r]
  return r

private def getCodomainLevel (preDefType : Expr) : MetaM Level :=
  forallBoundedTelescope preDefType (some 1) fun _ body => getLevel body

/--
  Return the universe level for the codomain of the given definitions.
  This method produces an error if the codomains are in different universe levels.
-/
private def getCodomainsLevel (preDefsOriginal : Array PreDefinition) (preDefTypes : Array Expr) : MetaM Level := do
  let r ← getCodomainLevel preDefTypes[0]!
  for i in [1:preDefTypes.size] do
    let preDef := preDefTypes[i]!
    unless (← isLevelDefEq r (← getCodomainLevel preDef)) do
      let arity₀ ← lambdaTelescope preDefsOriginal[0]!.value fun xs _ => return xs.size
      let arityᵢ ← lambdaTelescope preDefsOriginal[i]!.value fun xs _ => return xs.size
      forallBoundedTelescope preDefsOriginal[0]!.type arity₀ fun _ type₀ =>
      forallBoundedTelescope preDefsOriginal[i]!.type arityᵢ fun _ typeᵢ =>
        withOptions (fun o => pp.sanitizeNames.set o false) do
          throwError "invalid mutual definition, result types must be in the same universe level, resulting type for `{preDefsOriginal[0]!.declName}` is{indentExpr type₀} : {← inferType type₀}\nand for `{preDefsOriginal[i]!.declName}` is{indentExpr typeᵢ} : {← inferType typeᵢ}"
  return r

/--
  Create the codomain for the new function that "combines" different `preDef` types
  See: `packMutual`
-/
private partial def mkNewCoDomain (preDefsOriginal : Array PreDefinition) (preDefTypes : Array Expr) (x : Expr) : MetaM Expr := do
  let u ← getCodomainsLevel preDefsOriginal preDefTypes
  let rec go (x : Expr) (i : Nat) : MetaM Expr := do
    if i < preDefTypes.size - 1 then
      let xType ← whnfD (← inferType x)
      assert! xType.isAppOfArity ``PSum 2
      let xTypeArgs := xType.getAppArgs
      let casesOn := mkConst (mkCasesOnName ``PSum) (mkLevelSucc u :: xType.getAppFn.constLevels!)
      let casesOn := mkAppN casesOn xTypeArgs -- parameters
      let casesOn := mkApp casesOn (← mkLambdaFVars #[x] (mkSort u)) -- motive
      let casesOn := mkApp casesOn x -- major
      let minor1 ← withLocalDeclD (← mkFreshUserName `_x) xTypeArgs[0]! fun x =>
        mkLambdaFVars #[x] (preDefTypes[i]!.bindingBody!.instantiate1 x)
      let minor2 ← withLocalDeclD (← mkFreshUserName `_x) xTypeArgs[1]! fun x => do
        mkLambdaFVars #[x] (← go x (i+1))
      return mkApp2 casesOn minor1 minor2
    else
      return preDefTypes[i]!.bindingBody!.instantiate1 x
  go x 0

/--
  Combine/pack the values of the different definitions in a single value
  `x` is `PSum`, and we use `PSum.casesOn` to select the appropriate `preDefs.value`.
  See: `packMutual`.
  Remark: this method does not replace the nested recursive `preDefValues` applications.
  This step is performed by `transform` with the following `post` method.
 -/
private partial def packValues (x : Expr) (codomain : Expr) (preDefValues : Array Expr) : MetaM Expr := do
  let varNames := preDefValues.map fun val =>
    assert! val.isLambda
    val.bindingName!
  let mvar ← mkFreshExprSyntheticOpaqueMVar codomain
  let rec go (mvarId : MVarId) (x : FVarId) (i : Nat) : MetaM Unit := do
    if i < preDefValues.size - 1 then
      /-
        Names for the `cases` tactics. The names are important to preserve the user provided names (unary functions).
      -/
      let givenNames : Array AltVarNames :=
         if i == preDefValues.size - 2 then
           #[{ varNames := [varNames[i]!] }, { varNames := [varNames[i+1]!] }]
         else
           #[{ varNames := [varNames[i]!] }]
       let #[s₁, s₂] ← mvarId.cases x (givenNames := givenNames) | unreachable!
      s₁.mvarId.assign (mkApp preDefValues[i]! s₁.fields[0]!).headBeta
      go s₂.mvarId s₂.fields[0]!.fvarId! (i+1)
    else
      mvarId.assign (mkApp preDefValues[i]! (mkFVar x)).headBeta
  go mvar.mvarId! x.fvarId! 0
  instantiateMVars mvar

/--
  Auxiliary function for replacing nested `preDefs` recursive calls in `e` with the new function `newFn`.
  See: `packMutual`
-/
private partial def post (fixedPrefix : Nat) (preDefs : Array PreDefinition) (domain : Expr) (newFn : Name) (e : Expr) : MetaM TransformStep := do
  if e.getAppNumArgs != fixedPrefix + 1 then
    return TransformStep.done e
  let f := e.getAppFn
  if !f.isConst then
    return TransformStep.done e
  let declName := f.constName!
  let us       := f.constLevels!
  if let some fidx := preDefs.findIdx? (·.declName == declName) then
    let args := e.getAppArgs
    let fixedArgs := args[:fixedPrefix]
    let arg  := args.back
    let rec mkNewArg (i : Nat) (type : Expr) : MetaM Expr := do
      if i == preDefs.size - 1 then
        return arg
      else
        (← whnfD type).withApp fun f args => do
          assert! args.size == 2
          if i == fidx then
            return mkApp3 (mkConst ``PSum.inl f.constLevels!) args[0]! args[1]! arg
          else
            let r ← mkNewArg (i+1) args[1]!
            return mkApp3 (mkConst ``PSum.inr f.constLevels!) args[0]! args[1]! r
    return TransformStep.done <| mkApp (mkAppN (mkConst newFn us) fixedArgs) (← mkNewArg 0 domain)
  return TransformStep.done e

partial def withFixedPrefix (fixedPrefix : Nat) (preDefs : Array PreDefinition) (k : Array Expr → Array Expr → Array Expr → MetaM α) : MetaM α :=
  go fixedPrefix #[] (preDefs.map (·.value))
where
  go (i : Nat) (fvars : Array Expr) (vals : Array Expr) : MetaM α := do
    match i with
    | 0 => k fvars (← preDefs.mapM fun preDef => instantiateForall preDef.type fvars) vals
    | i+1 =>
      withLocalDecl vals[0]!.bindingName! vals[0]!.binderInfo vals[0]!.bindingDomain! fun x =>
        go i (fvars.push x) (vals.map fun val => val.bindingBody!.instantiate1 x)

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

  Remark: `preDefsOriginal` is used for error reporting, it contains the definitions before applying `packDomain`.
 -/
def packMutual (fixedPrefix : Nat) (preDefsOriginal : Array PreDefinition) (preDefs : Array PreDefinition) : MetaM PreDefinition := do
  if preDefs.size == 1 then return preDefs[0]!
  withFixedPrefix fixedPrefix preDefs fun ys types vals => do
    let domains := types.map fun type => type.bindingDomain!
    let domain ← mkNewDomain domains
    withLocalDeclD (← mkFreshUserName `_x) domain fun x => do
      let codomain ← mkNewCoDomain preDefsOriginal types x
      let type ← mkForallFVars (ys.push x) codomain
      let value ← packValues x codomain vals
      let newFn := preDefs[0]!.declName ++ `_mutual
      let preDefNew := { preDefs[0]! with declName := newFn, type, value }
      addAsAxiom preDefNew
      let value ← transform value (post := post fixedPrefix preDefs domain newFn)
      let value ← mkLambdaFVars (ys.push x) value
      return { preDefNew with value }

end Lean.Elab.WF
