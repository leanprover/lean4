/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.List.BasicAux
import Lean.AddDecl
import Lean.Meta.AppBuilder
import Lean.Meta.Instances

namespace Lean.Meta

/-- Create `SizeOf` local instances for applicable parameters, and execute `k` using them. -/
private partial def mkLocalInstances (params : Array Expr) (k : Array Expr → MetaM α) : MetaM α :=
  loop 0 #[]
where
  loop (i : Nat) (insts : Array Expr) : MetaM α := do
    if h : i < params.size then
      let param := params[i]
      let paramType ← inferType param
      let instType? ← forallTelescopeReducing paramType fun xs _ => do
        let type := mkAppN param xs
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
      if fvar == fvar'.getAppFn then
        return some idx
    idx := idx + 1
  return none

private partial def mkSizeOfMotives (motiveFVars : Array Expr) (k : Array Expr → MetaM α) : MetaM α :=
  loop 0 #[]
where
  loop (i : Nat) (motives : Array Expr) : MetaM α := do
    if h : i < motiveFVars.size then
      let type ← inferType motiveFVars[i]
      let motive ← forallTelescopeReducing type fun xs _ => do
        mkLambdaFVars xs <| mkConst ``Nat
      trace[Meta.sizeOf] "motive: {motive}"
      loop (i+1) (motives.push motive)
    else
      k motives

private partial def ignoreFieldType (type : Expr) : MetaM Bool := do
  let type ← whnf type
  if type.isForall then
    -- TODO: add support for finite domains
    if type.isArrow && type.bindingDomain!.isConstOf ``Unit then
      ignoreFieldType type.bindingBody!
    else
      return true
  else
    return false

private def ignoreField (x : Expr) : MetaM Bool := do
  let type ← inferType x
  ignoreFieldType type

/-- See `ignoreField`. We have support for functions of the form `Unit → ...` -/
private partial def mkSizeOfRecFieldFormIH (ih : Expr) : MetaM Expr := do
  if (← whnf (← inferType ih)).isForall then
     mkSizeOfRecFieldFormIH (mkApp ih (mkConst ``Unit.unit))
  else
     return ih

private partial def mkSizeOfMinors (motiveFVars : Array Expr) (minorFVars : Array Expr) (minorFVars' : Array Expr) (k : Array Expr → MetaM α) : MetaM α :=
  assert! minorFVars.size == minorFVars'.size
  loop 0 #[]
where
  loop (i : Nat) (minors : Array Expr) : MetaM α := do
    if i < minorFVars.size then
      forallTelescopeReducing (← inferType minorFVars[i]!) fun xs _ => do
      forallBoundedTelescope (← inferType minorFVars'[i]!) xs.size fun xs' _ => do
        let mut minor ← mkNumeral (mkConst ``Nat) 1
        for x in xs, x' in xs' do
          unless (← isInductiveHypothesis motiveFVars x) do
          unless (← ignoreField x) do -- we suppress higher-order fields
            match (← isRecField? motiveFVars xs x) with
            | some idx => minor ← mkAdd minor (← mkSizeOfRecFieldFormIH xs'[idx]!)
            | none     => minor ← mkAdd minor (← mkAppM ``SizeOf.sizeOf #[x'])
        minor ← mkLambdaFVars xs' minor
        trace[Meta.sizeOf] "minor: {minor}"
        loop (i+1) (minors.push minor)
    else
      k minors

/--
  Create a "sizeOf" function with name `declName` using the recursor `recName`.
-/
partial def mkSizeOfFn (recName : Name) (declName : Name): MetaM Unit := do
  trace[Meta.sizeOf] "recName: {recName}"
  let recInfo : RecursorVal ← getConstInfoRec recName
  forallTelescopeReducing recInfo.type fun xs _ =>
    let levelParams := recInfo.levelParams.tail! -- universe parameters for declaration being defined
    let params := xs[:recInfo.numParams]
    let motiveFVars := xs[recInfo.numParams : recInfo.numParams + recInfo.numMotives]
    let minorFVars := xs[recInfo.getFirstMinorIdx : recInfo.getFirstMinorIdx + recInfo.numMinors]
    let indices := xs[recInfo.getFirstIndexIdx : recInfo.getFirstIndexIdx + recInfo.numIndices]
    let major := xs[recInfo.getMajorIdx]!
    let nat := mkConst ``Nat
    mkLocalInstances params fun localInsts =>
    mkSizeOfMotives motiveFVars fun motives => do
      let us := levelOne :: levelParams.map mkLevelParam -- universe level parameters for `rec`-application
      let recFn := mkConst recName us
      let val := mkAppN recFn (params ++ motives)
      forallBoundedTelescope (← inferType val) recInfo.numMinors fun minorFVars' _ =>
      mkSizeOfMinors motiveFVars minorFVars minorFVars' fun minors => do
        withInstImplicitAsImplict params do
          let sizeOfParams := params ++ localInsts ++ indices ++ #[major]
          let sizeOfType ← mkForallFVars sizeOfParams nat
          let val := mkAppN val (minors ++ indices ++ #[major])
          let sizeOfValue ← mkLambdaFVars sizeOfParams val
          trace[Meta.sizeOf] "declName: {declName}"
          trace[Meta.sizeOf] "type: {sizeOfType}"
          trace[Meta.sizeOf] "val: {sizeOfValue}"
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
  The resulting array contains the generated functions names. The `NameMap` maps recursor names into the generated function names.
  There is a function for each element of the mutual inductive declaration, and for auxiliary recursors for nested inductive types.
-/
def mkSizeOfFns (typeName : Name) : MetaM (Array Name × NameMap Name) := do
  let indInfo ← getConstInfoInduct typeName
  let mut result := #[]
  let baseName := indInfo.all.head! ++ `_sizeOf -- we use the first inductive type as the base name for `sizeOf` functions
  let mut i := 1
  let mut recMap : NameMap Name := {}
  for indTypeName in indInfo.all do
    let sizeOfName := baseName.appendIndexAfter i
    let recName := mkRecName indTypeName
    mkSizeOfFn recName sizeOfName
    recMap := recMap.insert recName sizeOfName
    result := result.push sizeOfName
    i := i + 1
  for j in [:indInfo.numNested] do
    let recName := (mkRecName indInfo.all.head!).appendIndexAfter (j+1)
    let sizeOfName := baseName.appendIndexAfter i
    mkSizeOfFn recName sizeOfName
    recMap := recMap.insert recName sizeOfName
    result := result.push sizeOfName
    i := i + 1
  return (result, recMap)

def mkSizeOfSpecLemmaName (ctorName : Name) : Name :=
  ctorName ++ `sizeOf_spec

def mkSizeOfSpecLemmaInstance (ctorApp : Expr) : MetaM Expr :=
  matchConstCtor ctorApp.getAppFn (fun _ => throwError "failed to apply 'sizeOf' spec, constructor expected{indentExpr ctorApp}") fun ctorInfo _ => do
    let ctorArgs     := ctorApp.getAppArgs
    let ctorParams   := ctorArgs[:ctorInfo.numParams]
    let ctorFields   := ctorArgs[ctorInfo.numParams:]
    let lemmaName  := mkSizeOfSpecLemmaName ctorInfo.name
    let lemmaInfo  ← getConstInfo lemmaName
    let lemmaArity ← forallTelescopeReducing lemmaInfo.type fun xs _ => return xs.size
    let lemmaArgMask := ctorParams.toArray.map some
    let lemmaArgMask := lemmaArgMask ++ .replicate (lemmaArity - ctorInfo.numParams - ctorInfo.numFields) (none (α := Expr))
    let lemmaArgMask := lemmaArgMask ++ ctorFields.toArray.map some
    mkAppOptM lemmaName lemmaArgMask

/-! # SizeOf spec theorem for nested inductive types -/
namespace SizeOfSpecNested

structure Context where
  indInfo    : InductiveVal
  sizeOfFns  : Array Name
  ctorName   : Name
  params     : Array Expr
  localInsts : Array Expr
  recMap     : NameMap Name -- mapping from recursor name into `_sizeOf_<idx>` function name (see `mkSizeOfFns`)

abbrev M := ReaderT Context MetaM

def throwUnexpected {α} (msg : MessageData) : M α := do
  throwError "failed to generate sizeOf theorem for {(← read).ctorName} (use `set_option genSizeOfSpec false` to disable theorem generation), {msg}"

def throwFailed {α} : M α := do
  throwError "failed to generate sizeOf theorem for {(← read).ctorName}, (use `set_option genSizeOfSpec false` to disable theorem generation)"

/-- Convert a recursor application into a `_sizeOf_<idx>` application. -/
private def recToSizeOf (e : Expr) : M Expr := do
  matchConstRec e.getAppFn (fun _ => throwFailed) fun info us => do
    match (← read).recMap.find? info.name with
    | none => throwUnexpected m!"expected recursor application {indentExpr e}"
    | some sizeOfName =>
      let args    := e.getAppArgs
      let indices := args[info.getFirstIndexIdx : info.getFirstIndexIdx + info.numIndices]
      let major   := args[info.getMajorIdx]!
      return mkAppN (mkConst sizeOfName us.tail!) ((← read).params ++ (← read).localInsts ++ indices ++ #[major])

mutual
  /-- Construct minor premise proof for `mkSizeOfAuxLemmaProof`. `ys` contains fields and inductive hypotheses for the minor premise. -/
  private partial def mkMinorProof (ys : Array Expr) (lhs rhs : Expr) : M Expr := do
    trace[Meta.sizeOf.minor] "{lhs} =?= {rhs}"
    if (← isDefEq lhs rhs) then
      mkEqRefl rhs
    else
      match (← whnfI lhs).natAdd?, (← whnfI rhs).natAdd? with
      | some (a₁, b₁), some (a₂, b₂) =>
        let p₁ ← mkMinorProof ys a₁ a₂
        let p₂ ← mkMinorProofStep ys b₁ b₂
        mkCongr (← mkCongrArg (mkConst ``Nat.add) p₁) p₂
      | _, _ =>
        throwUnexpected m!"expected 'Nat.add' application, lhs is {indentExpr lhs}\nrhs is{indentExpr rhs}"

  /--
    Helper method for `mkMinorProof`. The proof step is one of the following
    - Reflexivity
    - Assumption (i.e., using an inductive hypotheses from `ys`)
    - `mkSizeOfAuxLemma` application. This case happens when we have multiple levels of nesting
  -/
  private partial def mkMinorProofStep (ys : Array Expr) (lhs rhs : Expr) : M Expr := do
    if (← isDefEq lhs rhs) then
      mkEqRefl rhs
    else
      let lhs ← recToSizeOf lhs
      trace[Meta.sizeOf.minor.step] "{lhs} =?= {rhs}"
      let target ← mkEq lhs rhs
      for y in ys do
        if (← isDefEq (← inferType y) target) then
          return y
      mkSizeOfAuxLemma lhs rhs

  /-- Construct proof of auxiliary lemma. See `mkSizeOfAuxLemma` -/
  private partial def mkSizeOfAuxLemmaProof (info : InductiveVal) (lhs : Expr) : M Expr := do
    let lhsArgs := lhs.getAppArgs
    let sizeOfBaseArgs := lhsArgs[:lhsArgs.size - info.numIndices - 1]
    let indicesMajor := lhsArgs[lhsArgs.size - info.numIndices - 1:]
    let sizeOfLevels := lhs.getAppFn.constLevels!
    let rec
      /-- Auxiliary function for constructing an `_sizeOf_<idx>` for `ys`,
        where `ys` are the indices + major.
        Recall that if `info.name` is part of a mutually inductive declaration, then the resulting application
        is not necessarily a `lhs.getAppFn` application.
        The result is an application of one of the `(← read),sizeOfFns` functions.
        We use this auxiliary function to builtin the motive of the recursor. -/
      mkSizeOf (ys : Array Expr) : M Expr := do
      for sizeOfFn in (← read).sizeOfFns do
        let candidate := mkAppN (mkAppN (mkConst sizeOfFn sizeOfLevels) sizeOfBaseArgs) ys
        if (← isTypeCorrect candidate) then
          return candidate
      throwFailed
    let major := lhs.appArg!
    let majorType ← whnf (← inferType major)
    let majorTypeArgs := majorType.getAppArgs
    match majorType.getAppFn.const? with
    | none => throwFailed
    | some (_, us) =>
      let recName := mkRecName info.name
      let recInfo ← getConstInfoRec recName
      let r := mkConst recName (levelZero :: us)
      let r := mkAppN r majorTypeArgs[:info.numParams]
      forallBoundedTelescope (← inferType r) recInfo.numMotives fun motiveFVars _ => do
        let mut r := r
        -- Add motives
        for motiveFVar in motiveFVars do
          let motive ← forallTelescopeReducing (← inferType motiveFVar) fun ys _ => do
            let lhs ← mkSizeOf ys
            let rhs ← mkAppM ``SizeOf.sizeOf #[ys.back!]
            mkLambdaFVars ys (← mkEq lhs rhs)
          r := mkApp r motive
        forallBoundedTelescope (← inferType r) recInfo.numMinors fun minorFVars _ => do
          let mut r := r
          -- Add minors
          for minorFVar in minorFVars do
            let minor ← forallTelescopeReducing (← inferType minorFVar) fun ys target => do
              let target ← whnf target
              match target.eq? with
              | none => throwFailed
              | some (_, lhs, rhs) =>
                if (← isDefEq lhs rhs) then
                  mkLambdaFVars ys (← mkEqRefl rhs)
                else
                  let lhs ← unfoldDefinition lhs -- Unfold `_sizeOf_<idx>`
                  -- rhs is of the form `sizeOf (ctor ...)`
                  let ctorApp := rhs.appArg!
                  let specLemma ← mkSizeOfSpecLemmaInstance ctorApp
                  let specEq ← whnf (← inferType specLemma)
                  match specEq.eq? with
                  | none => throwFailed
                  | some (_, _, rhsExpanded) =>
                    let lhs_eq_rhsExpanded ← mkMinorProof ys lhs rhsExpanded
                    let rhsExpanded_eq_rhs ← mkEqSymm specLemma
                    mkLambdaFVars ys (← mkEqTrans lhs_eq_rhsExpanded rhsExpanded_eq_rhs)
            r := mkApp r minor
          -- Add indices and major
          return mkAppN r indicesMajor

  /--
    Generate proof for `C._sizeOf_<idx> t = sizeOf t` where `C._sizeOf_<idx>` is a auxiliary function
    generated for a nested inductive type in `C`.
    For example, given
    ```lean
    inductive Expr where
      | app (f : String) (args : List Expr)
    ```
    We generate the auxiliary function `Expr._sizeOf_1 : List Expr → Nat`.
    To generate the `sizeOf` spec lemma
    ```
    sizeOf (Expr.app f args) = 1 + sizeOf f + sizeOf args
    ```
    we need an auxiliary lemma for showing `Expr._sizeOf_1 args = sizeOf args`.
    Recall that `sizeOf (Expr.app f args)` is definitionally equal to `1 + sizeOf f + Expr._sizeOf_1 args`, but
    `Expr._sizeOf_1 args` is **not** definitionally equal to `sizeOf args`. We need a proof by induction.
  -/
  private partial def mkSizeOfAuxLemma (lhs rhs : Expr) : M Expr := do
    trace[Meta.sizeOf.aux] "{lhs} =?= {rhs}"
    match lhs.getAppFn.const? with
    | none => throwFailed
    | some (fName, us) =>
      let thmLevelParams ← us.mapM fun
        | Level.param n => return n
        | _ => throwFailed
      let thmName  := fName.appendAfter "_eq"
      if (← getEnv).contains thmName then
        -- Auxiliary lemma has already been defined
        return mkAppN (mkConst thmName us) lhs.getAppArgs
      else
        -- Define auxiliary lemma
        -- First, generalize indices
        let x := lhs.appArg!
        let xType ← whnf (← inferType x)
        matchConstInduct xType.getAppFn (fun _ => throwFailed) fun info _ => do
          let params := xType.getAppArgs[:info.numParams]
          forallTelescopeReducing (← inferType (mkAppN xType.getAppFn params)) fun indices _ => do
            let majorType := mkAppN (mkAppN xType.getAppFn params) indices
            withLocalDeclD `x majorType fun major => do
              let lhsArgs := lhs.getAppArgs
              let lhsArgsNew := lhsArgs[:lhsArgs.size - 1 - indices.size] ++ indices ++ #[major]
              let lhsNew := mkAppN lhs.getAppFn lhsArgsNew
              let rhsNew ← mkAppM ``SizeOf.sizeOf #[major]
              let eq ← mkEq lhsNew rhsNew
              let thmParams := lhsArgsNew
              let thmType ← mkForallFVars thmParams eq
              let thmValue ← mkSizeOfAuxLemmaProof info lhsNew
              let thmValue ← mkLambdaFVars thmParams thmValue
              trace[Meta.sizeOf] "thmValue: {thmValue}"
              addDecl <| Declaration.thmDecl {
                name        := thmName
                levelParams := thmLevelParams
                type        := thmType
                value       := thmValue
              }
              return mkAppN (mkConst thmName us) lhs.getAppArgs

end

/- Prove SizeOf spec lemma of the form `sizeOf <ctor-application> = 1 + sizeOf <field_1> + ... + sizeOf <field_n> -/
partial def main (lhs rhs : Expr) : M Expr := do
  if (← isDefEq lhs rhs) then
    mkEqRefl rhs
  else
    /- Expand lhs and rhs to obtain `Nat.add` applications -/
    let lhs ← whnfI lhs            -- Expand `sizeOf (ctor ...)` into `_sizeOf_<idx>` application
    let lhs ← unfoldDefinition lhs -- Unfold `_sizeOf_<idx>` application into `HAdd.hAdd` application
    loop lhs rhs
where
  loop (lhs rhs : Expr) : M Expr := do
    trace[Meta.sizeOf.loop] "{lhs} =?= {rhs}"
    if (← isDefEq lhs rhs) then
      mkEqRefl rhs
    else
      match (← whnfI lhs).natAdd?, (← whnfI rhs).natAdd? with
      | some (a₁, b₁), some (a₂, b₂) =>
        let p₁ ← loop a₁ a₂
        let p₂ ← step b₁ b₂
        mkCongr (← mkCongrArg (mkConst ``Nat.add) p₁) p₂
      | _, _ =>
        throwUnexpected m!"expected 'Nat.add' application, lhs is {indentExpr lhs}\nrhs is{indentExpr rhs}"

  step (lhs rhs : Expr) : M Expr := do
    if (← isDefEq lhs rhs) then
      mkEqRefl rhs
    else
      let lhs ← recToSizeOf lhs
      mkSizeOfAuxLemma lhs rhs

end SizeOfSpecNested

private def mkSizeOfSpecTheorem (indInfo : InductiveVal) (sizeOfFns : Array Name) (recMap : NameMap Name) (ctorName : Name) : MetaM Unit := do
  let ctorInfo ← getConstInfoCtor ctorName
  let us := ctorInfo.levelParams.map mkLevelParam
  let simpAttr ← ofExcept <| getAttributeImpl (← getEnv) `simp
  forallTelescopeReducing ctorInfo.type fun xs _ => do
    let params := xs[:ctorInfo.numParams]
    let fields := xs[ctorInfo.numParams:]
    let ctorApp := mkAppN (mkConst ctorName us) xs
    mkLocalInstances params fun localInsts => do
      let lhs ← mkAppM ``SizeOf.sizeOf #[ctorApp]
      let mut rhs ← mkNumeral (mkConst ``Nat) 1
      for field in fields do
        unless (← ignoreField field) do
          rhs ← mkAdd rhs (← mkAppM ``SizeOf.sizeOf #[field])
      let target ← mkEq lhs rhs
      trace[Meta.sizeOf] "ctor: {ctorInfo.name}, target: {target}"
      let thmName   := mkSizeOfSpecLemmaName ctorName
      let thmParams := params ++ localInsts ++ fields
      let thmType ← mkForallFVars thmParams target
      let thmValue ← if indInfo.isNested then
        SizeOfSpecNested.main lhs rhs |>.run {
          indInfo, sizeOfFns, ctorName, params, localInsts, recMap
        }
      else
        mkEqRefl rhs
      let thmValue ← mkLambdaFVars thmParams thmValue
      trace[Meta.sizeOf] "sizeOf spec theorem name: {thmName}"
      trace[Meta.sizeOf] "sizeOf spec theorem type: {thmType}"
      trace[Meta.sizeOf] "sizeOf spec theorem value: {thmValue}"
      unless (← isDefEq (← inferType thmValue) thmType) do
        throwError "type mismatch"
      addDecl <| Declaration.thmDecl {
        name        := thmName
        levelParams := ctorInfo.levelParams
        type        := thmType
        value       := thmValue
      }
      simpAttr.add thmName default AttributeKind.global

private def mkSizeOfSpecTheorems (indTypeNames : Array Name) (sizeOfFns : Array Name) (recMap : NameMap Name) : MetaM Unit := do
  for indTypeName in indTypeNames do
    let indInfo ← getConstInfoInduct indTypeName
    for ctorName in indInfo.ctors do
      mkSizeOfSpecTheorem indInfo sizeOfFns recMap ctorName
  return ()

register_builtin_option genSizeOf : Bool := {
  defValue := true
  descr    := "generate `SizeOf` instance for inductive types and structures"
}

register_builtin_option genSizeOfSpec : Bool := {
  defValue := true
  descr    := "generate `SizeOf` specification theorems for automatically generated instances"
}

def mkSizeOfInstances (typeName : Name) : MetaM Unit := do
  if (← getEnv).contains ``SizeOf && genSizeOf.get (← getOptions) && !(← isInductivePredicate typeName) then
    withTraceNode `Meta.sizeOf (fun _ => return m!"{typeName}") do
      let indInfo ← getConstInfoInduct typeName
      unless indInfo.isUnsafe do
        let (fns, recMap) ← mkSizeOfFns typeName
        for indTypeName in indInfo.all, fn in fns do
          let indInfo ← getConstInfoInduct indTypeName
          forallTelescopeReducing indInfo.type fun xs _ =>
            let params := xs[:indInfo.numParams]
            withInstImplicitAsImplict params do
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
                  trace[Meta.sizeOf] ">> {instDeclName} : {instDeclType}"
                  addDecl <| Declaration.defnDecl {
                    name        := instDeclName
                    levelParams := indInfo.levelParams
                    type        := instDeclType
                    value       := instDeclValue
                    safety      := .safe
                    hints       := .abbrev
                  }
                  addInstance instDeclName AttributeKind.global (eval_prio default)
        if genSizeOfSpec.get (← getOptions) then
          mkSizeOfSpecTheorems indInfo.all.toArray fns recMap

builtin_initialize
  registerTraceClass `Meta.sizeOf
  registerTraceClass `Meta.sizeOf.minor
  registerTraceClass `Meta.sizeOf.minor.step
  registerTraceClass `Meta.sizeOf.aux
  registerTraceClass `Meta.sizeOf.loop

end Lean.Meta
