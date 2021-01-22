/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.AppBuilder
import Lean.Meta.Instances

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
  Return `some x` if `fvar` has type of the form `... -> motive ... fvar` where `motive` in `motiveFVars`.
  That is, `x` "produces" one of the recursor motives.
-/
private def isInductiveHypothesis? (motiveFVars : Array Expr) (fvar : Expr) : MetaM (Option Expr) := do
  forallTelescopeReducing (← inferType fvar) fun _ type =>
    if type.isApp && motiveFVars.contains type.getAppFn then
      return some type.appArg!
    else
      return none

private def isInductiveHypothesis (motiveFVars : Array Expr) (fvar : Expr) : MetaM Bool :=
  return (← isInductiveHypothesis? motiveFVars fvar).isSome

/--
  Let `motiveFVars` be free variables for each motive in a kernel recursor, and `minorFVars` the free variables for a minor premise.
  Then, return `some idx` if `minorFVars[idx]` has a type of the form `... -> motive ... fvar` for some `motive` in `motiveFVars`.
-/
private def isRecField? (motiveFVars : Array Expr) (minorFVars : Array Expr) (fvar : Expr) : MetaM (Option Nat) := do
  let mut idx := 0
  for minorFVar in minorFVars do
    if let some fvar' ← isInductiveHypothesis? motiveFVars minorFVar then
      if fvar == fvar' then
        return some idx
    idx := idx + 1
  return none

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
          unless (← isInductiveHypothesis motiveFVars x) do
          unless (← whnf (← inferType x)).isForall do -- we suppress higher-order fields
            match (← isRecField? motiveFVars xs x) with
            | some idx => minor ← mkAdd minor xs'[idx]
            | none     => minor ← mkAdd minor (← mkAppM ``SizeOf.sizeOf #[x'])
        minor ← mkLambdaFVars xs' minor
        trace[Meta.sizeOf]! "minor: {minor}"
        loop (i+1) (minors.push minor)
    else
      k minors

/--
  Create a "sizeOf" function with name `declName` using the recursor `recName`.
-/
partial def mkSizeOfFn (recName : Name) (declName : Name): MetaM Unit := do
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
        let sizeOfParams := params ++ localInsts ++ indices ++ #[major]
        let sizeOfType ← mkForallFVars sizeOfParams nat
        let val := mkAppN val (minors ++ indices ++ #[major])
        trace[Meta.sizeOf]! "val: {val}"
        let sizeOfValue ← mkLambdaFVars sizeOfParams val
        addDecl <| Declaration.defnDecl {
          name        := declName
          levelParams := levelParams
          type        := sizeOfType
          value       := sizeOfValue
          safety      := DefinitionSafety.safe
          hints       := ReducibilityHints.abbrev
        }

/--
  Create `sizeOf` functions for all inductive datatypes in the mutual inductive declaration containing `typeName`
  The resulting array contains the generated functions names.
  There is a function for each element of the mutual inductive declaration, and for auxiliary recursors for nested inductive types.
-/
def mkSizeOfFns (typeName : Name) : MetaM (Array Name) := do
  let indInfo ← getConstInfoInduct typeName
  let recInfo ← getConstInfoRec (mkRecName typeName)
  let numExtra := recInfo.numMotives - indInfo.all.length -- numExtra > 0 for nested inductive types
  let mut result := #[]
  let baseName := indInfo.all.head! ++ `_sizeOf -- we use the first inductive type as the base name for `sizeOf` functions
  let mut i := 1
  for indTypeName in indInfo.all do
    let sizeOfName := baseName.appendIndexAfter i
    mkSizeOfFn (mkRecName indTypeName) sizeOfName
    result := result.push sizeOfName
    i := i + 1
  for j in [:numExtra] do
    let recName := (mkRecName indInfo.all.head!).appendIndexAfter (j+1)
    let sizeOfName := baseName.appendIndexAfter i
    mkSizeOfFn recName sizeOfName
    result := result.push sizeOfName
    i := i + 1
  return result

private def mkSizeOfSpecTheorem (indInfo : InductiveVal) (sizeOfFns : Array Name) (ctorName : Name) : MetaM Unit := do
  let ctorInfo ← getConstInfoCtor ctorName
  let us := ctorInfo.levelParams.map mkLevelParam
  forallTelescopeReducing ctorInfo.type fun xs _ => do
    let params := xs[:ctorInfo.numParams]
    let fields := xs[ctorInfo.numParams:]
    let ctorApp := mkAppN (mkConst ctorName us) xs
    mkLocalInstances params fun localInsts => do
      let lhs ← mkAppM ``SizeOf.sizeOf #[ctorApp]
      let mut rhs ← mkNumeral (mkConst ``Nat) 1
      for field in fields do
        unless (← whnf (← inferType field)).isForall do
          rhs ← mkAdd rhs (← mkAppM ``SizeOf.sizeOf #[field])
      let target ← mkEq lhs rhs
      let thmName := ctorName ++ `sizeOf_spec
      let thmParams := params ++ localInsts ++ fields
      let thmType ← mkForallFVars thmParams target
      let thmValue ←
        if indInfo.isNested then
          return () -- TODO
        else
          mkEqRefl rhs
      let thmValue ← mkLambdaFVars thmParams thmValue
      addDecl <| Declaration.thmDecl {
        name        := thmName
        levelParams := ctorInfo.levelParams
        type        := thmType
        value       := thmValue
      }

private def mkSizeOfSpecTheorems (indTypeNames : Array Name) (sizeOfFns : Array Name) : MetaM Unit := do
  for indTypeName in indTypeNames do
    let indInfo ← getConstInfoInduct indTypeName
    for ctorName in indInfo.ctors do
      mkSizeOfSpecTheorem indInfo sizeOfFns ctorName
  return ()

builtin_initialize
  registerOption `genSizeOf { defValue := true, group := "", descr := "generate `SizeOf` instance for inductive types and structures" }
  registerOption `genSizeOfSpec { defValue := true, group := "", descr := "generate `SizeOf` specificiation theorems for automatically generated instances" }

def generateSizeOfInstance (opts : Options) : Bool :=
  opts.get `genSizeOf true

def generateSizeOfSpec (opts : Options) : Bool :=
  opts.get `genSizeOfSpec true

def mkSizeOfInstances (typeName : Name) : MetaM Unit := do
  if (← getEnv).contains ``SizeOf && generateSizeOfInstance (← getOptions) && !(← isInductivePredicate typeName) then
    let indInfo ← getConstInfoInduct typeName
    unless indInfo.isUnsafe do
      let fns ← mkSizeOfFns typeName
      for indTypeName in indInfo.all, fn in fns do
        let indInfo ← getConstInfoInduct indTypeName
        forallTelescopeReducing indInfo.type fun xs _ =>
          let params := xs[:indInfo.numParams]
          let indices := xs[indInfo.numParams:]
          mkLocalInstances params fun localInsts => do
            let us := indInfo.levelParams.map mkLevelParam
            let indType := mkAppN (mkConst indTypeName us) xs
            let sizeOfIndType ← mkAppM ``SizeOf #[indType]
            withLocalDeclD `m indType fun m => do
              let v ← mkLambdaFVars #[m] <| mkAppN (mkConst fn us) (params ++ localInsts ++ indices ++ #[m])
              let sizeOfMk ← mkAppM ``SizeOf.mk #[v]
              let instDeclName := indTypeName ++ `_sizeOf_inst
              let instDeclType ← mkForallFVars (xs ++ localInsts) sizeOfIndType
              let instDeclValue ← mkLambdaFVars (xs ++ localInsts) sizeOfMk
              addDecl <| Declaration.defnDecl {
                name        := instDeclName
                levelParams := indInfo.levelParams
                type        := instDeclType
                value       := instDeclValue
                safety      := DefinitionSafety.safe
                hints       := ReducibilityHints.abbrev
              }
              addInstance instDeclName AttributeKind.global (evalPrio! default)
      if generateSizeOfSpec (← getOptions) then
        mkSizeOfSpecTheorems indInfo.all.toArray fns

builtin_initialize
  registerTraceClass `Meta.sizeOf

end Lean.Meta
