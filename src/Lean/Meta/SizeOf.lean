/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.AppBuilder
import Lean.Meta.Check

namespace Lean.Meta

/-- Create `SizeOf` local instances for applicable parameters, and execute `k` using them. -/
private partial def mkLocalInstances {α} (params : Array Expr) (k : Array Expr → MetaM α) : MetaM α :=
  loop 0 #[]
where
  loop (i : Nat) (insts : Array Expr) : MetaM α := do
    if i < params.size then
      let param := params[i]
      let paramType ← inferType param
      let instType? ← forallTelescopeReducing paramType fun xs _ => do
        let type ← mkAppN param xs
        try
          let sizeOf ← mkAppM `SizeOf #[type]
          let instType ← mkForallFVars xs sizeOf
          return some instType
        catch _ =>
          return none
      match instType? with
      | none => loop (i+1) insts
      | some instType =>
        let instName ← mkFreshUserName `inst
        withLocalDecl instName BinderInfo.instImplicit instType fun inst =>
          loop (i+1) (insts.push inst)
    else
      k insts
/--
  Let `motiveFVars` be free variables for each motive in a kernel recursor, and `minorFVars` the free variables for a minor premise.
  Then, return `true` is `fvar` (an element of `minorFVars`) corresponds to a recursive field.
  That is, there is a free variable `minorFVar` in `minorFVars` with type `... -> motive ... fvar` where `motive` is an element of `motiveFVars`.
-/
private def isRecField (motiveFVars : Array Expr) (minorFVars : Array Expr) (fvar : Expr) : MetaM Bool := do
  for minorFVar in minorFVars do
    let found ← forallTelescopeReducing (← inferType minorFVar) fun _ type =>
      return motiveFVars.contains type.getAppFn && type.appArg! == fvar
    if found then
      return true
  return false

private partial def mkSizeOfMotives {α} (motiveFVars : Array Expr) (k : Array Expr → MetaM α) : MetaM α :=
  loop 0 #[]
where
  loop (i : Nat) (motives : Array Expr) : MetaM α := do
    if i < motiveFVars.size then
      let type ← inferType motiveFVars[i]
      let motive ← forallTelescopeReducing type fun xs _ => do
        mkLambdaFVars xs <| mkConst ``Nat
      trace[Meta.sizeOf]! "motive: {motive}"
      loop (i+1) (motives.push motive)
    else
      k motives

private partial def mkSizeOfMinors {α} (motiveFVars : Array Expr) (minorFVars : Array Expr) (minorFVars' : Array Expr) (k : Array Expr → MetaM α) : MetaM α :=
  assert! minorFVars.size == minorFVars'.size
  loop 0 #[]
where
  loop (i : Nat) (minors : Array Expr) : MetaM α := do
    if i < minorFVars.size then
      forallTelescopeReducing (← inferType minorFVars[i]) fun xs _ =>
      forallBoundedTelescope (← inferType minorFVars'[i]) xs.size fun xs' _ => do
        let mut minor ← mkNumeral (mkConst ``Nat) 1
        for x in xs, x' in xs' do
          -- If `x` is a recursive field, we skip it since we use the inductive hypothesis occurring later
          unless (← isRecField motiveFVars xs x) do
            let xType ← inferType x
            minor ← forallTelescopeReducing xType fun ys xTypeResult => do
              if motiveFVars.contains xTypeResult.getAppFn then
                -- `x` is an inductive hypothesis
                if ys.size > 0 then
                  -- ignore `x` because it is a function
                  return minor
                else
                  mkAdd minor x'
              else
                try
                  mkAdd minor (← mkAppM ``SizeOf.sizeOf #[x'])
                catch _ =>
                  return minor
        minor ← mkLambdaFVars xs' minor
        trace[Meta.sizeOf]! "minor: {minor}"
        loop (i+1) (minors.push minor)
    else
      k minors

partial def mkSizeOfFn (recName : Name) : MetaM Unit := do
  trace[Meta.sizeOf]! "recName: {recName}"
  let recInfo : RecursorVal ← getConstInfoRec recName
  forallTelescopeReducing recInfo.type fun xs type =>
    let levelParams := recInfo.levelParams.tail! -- universe parameters for declaration being defined
    let params := xs[:recInfo.numParams]
    let motiveFVars := xs[recInfo.numParams : recInfo.numParams + recInfo.numMotives]
    let minorFVars := xs[recInfo.getFirstMinorIdx : recInfo.getFirstMinorIdx + recInfo.numMinors]
    let indices := xs[recInfo.getFirstIndexIdx : recInfo.getFirstIndexIdx + recInfo.numIndices]
    let major := xs[recInfo.getMajorIdx]
    let nat := mkConst ``Nat
    mkLocalInstances params fun localInsts =>
    mkSizeOfMotives motiveFVars fun motives => do
      let us := levelOne :: levelParams.map mkLevelParam -- universe level parameters for `rec`-application
      let recFn := mkConst recName us
      let val := mkAppN recFn (params ++ motives)
      forallBoundedTelescope (← inferType val) recInfo.numMinors fun minorFVars' _ =>
      mkSizeOfMinors motiveFVars minorFVars minorFVars' fun minors => do
        let sizeOfFnType ← mkForallFVars (params ++ localInsts ++ indices ++ #[major]) nat
        let val := mkAppN val (minors ++ indices ++ #[major])
        trace[Meta.sizeOf]! "val: {val}"
        trace[Meta.sizeOf]! "type: {← inferType val}"
        check val -- TODO: remove
        return ()

builtin_initialize
  registerTraceClass `Meta.sizeOf

end Lean.Meta
