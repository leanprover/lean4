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

builtin_initialize
  registerOption `genSizeOf { defValue := true, group := "", descr := "generate `SizeOf` instance for inductive types and structures" }

def generateSizeOfInstance (opts : Options) : Bool :=
  opts.get `genSizeOf true

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

builtin_initialize
  registerTraceClass `Meta.sizeOf

end Lean.Meta
