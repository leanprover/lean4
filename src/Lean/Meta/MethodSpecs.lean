/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module
prelude
public import Init.System.IO
public import Lean.Attributes
public import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Basic
import Lean.Structure
import Lean.Meta.CtorRecognizer
import Lean.Meta.InferType
import Lean.Meta.AppBuilder
import Lean.ReservedNameAction
import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Tactic.Simp.Types
import Lean.Meta.Tactic.Simp.Main

namespace Lean

open Meta

structure MethodSpecTheorem where
  /-- Name of the implementation function -/
  name : Name
  levelParams : List Name
  /-- `opImpl = Cls.op instClsT` -/
  type : Expr

structure MethodSpecsInfo where
  clsName : Name
  /-- Array mapping field names to implementation functions. -/
  fieldImpls : Array (Name × Name)
  /-- rewrite rules to apply -/
  thms  : Array MethodSpecTheorem

/--
This function checks the `instName` for eligibility and collects the information to rewrite.
It is run twice: when setting the `@[specs]` attribute as a preflight check, and when actually realizing
the constants.
-/
def getMethodSpecsInfo (instName : Name) : MetaM MethodSpecsInfo := do
  let instInfo ← getConstInfoDefn instName
  let some clsName ← isClass? instInfo.type
    | throwError "expected `{.ofConstName instName}` to be a type class instance, but its's \
         type{inlineExpr instInfo.type}does not look like a class."
  let instArity ← forallTelescopeReducing instInfo.type fun xs _ => pure xs.size
  let some structInfo := getStructureInfo? (← getEnv) clsName
    | throwError "`{.ofConstName clsName}` is not a structure"

  lambdaTelescope instInfo.value fun xs body => do
    let inst := mkAppN (mkConst instInfo.name (instInfo.levelParams.map mkLevelParam)) xs
    let clsApp ← instantiateForall instInfo.type xs
    unless xs.size == instArity && (← isConstructorApp body) do
      throwError "the definition of `{.ofConstName instName}` does not have the expected shape"

    let mut fieldImpls := #[]
    let mut thms := #[]

    for field in structInfo.fieldNames, arg in body.getAppArgsN structInfo.fieldNames.size do
      if (← isProof arg) then continue
      let arg := arg.eta
      let f := arg.getAppFn
      let ys := arg.getAppArgs
      unless f.isConst do
        throwError "field `{field}` of the instance is not an application of a constant"
      unless f.constLevels! == instInfo.levelParams.map mkLevelParam do
        throwError "function `{f}` gets universe parameters\n  {f.constLevels!}\nwhich differs from \
          the instances' universe parameters\n  {instInfo.levelParams.map mkLevelParam}"
      unless xs == ys do
        throwError "function `{f}` does not take its arguments in the same order as the instance"
      -- Construct the replacement theorems
      let some fieldInfo := getFieldInfo? (← getEnv) clsName field
        | throwError "internal error: could not find field {field} in structure {clsName}"
      let lhs := arg
      let projFn := mkConst fieldInfo.projFn clsApp.getAppFn.constLevels!
      let rhs := mkAppN projFn (clsApp.getAppArgs ++ #[inst])
      let eq ← mkEq lhs rhs
      let thm ← mkForallFVars xs eq
      unless (← isDefEq lhs rhs) do
        throwError "internal error: equation `{eq}` does not hold definitionally"
      fieldImpls := fieldImpls.push (field, f.constName!)
      thms := thms.push { name := f.constName!, levelParams := instInfo.levelParams, type := thm }
    trace[Meta.MethodSpecs] "MethodSpecs for {instName}:\n{fieldImpls}\nthms: {thms.map (·.type)}"

    return {clsName, fieldImpls, thms}

public structure MethodSpecsAttrData where
  clsName : Name
deriving Inhabited

def getParam (instName : Name) (_stx : Syntax) : AttrM MethodSpecsAttrData := do
  -- Preflight check
  let specsInfo ← (getMethodSpecsInfo instName).run'
  return {
    clsName := specsInfo.clsName
  }

/--
Generate method specification theorems for the methods of the given type class instance.

This expects all (non-proof) methods of the instance to be defined via separate helper functions,
which must take the same arguments as the instance itself, in the same order.

If it is applied to an instance
```
instance instClsT : Cls T where op := opImpl
```
it produces a theorem `instClsT.op_spec` based on `opImpl.eq_def`, but phrased in terms of the
overloaded `Cls.op` operation, and similarly `instClsT.op_spec_<n>` based on the equational theorems
`opImpl.eq_<n>`.
-/
@[builtin_doc]
builtin_initialize methodSpecsAttr : ParametricAttribute MethodSpecsAttrData ←
  registerParametricAttribute {
    name := `method_specs
    descr := "generate method specification theorems"
    getParam
  }

builtin_initialize methodSpecsSimpExtension : SimpExtension ←
  registerSimpAttr `method_specs_simp
    "simp lemma used to post-process the theorem created by `@[method_specs]`."

def rewriteThm (ctx : Simp.Context) (simprocs : Simprocs)
    (eqThmName destThmName : Name) : MetaM Unit := do
  let thmInfo ← getConstVal eqThmName
  let (result, _) ← simp thmInfo.type ctx (simprocs := #[simprocs])
  trace[Meta.MethodSpecs] "type for {destThmName}:{indentExpr result.expr}"
  let value ← result.mkEqMPR <| mkConst eqThmName (thmInfo.levelParams.map mkLevelParam)
  addDecl <| Declaration.thmDecl {
    name          := destThmName
    levelParams   := thmInfo.levelParams
    type          := result.expr
    value         := value
  }

def genSpecs (instName : Name) : MetaM Unit := do
  let methodSpecsInfo ← getMethodSpecsInfo instName
  let key := instName.str s!"{methodSpecsInfo.fieldImpls[0]!.1}_spec"
  realizeConst instName key doRealize
where
  doRealize := do
    let methodSpecsInfo ← getMethodSpecsInfo instName
    let mut s ← methodSpecsSimpExtension.getTheorems
    for thm in methodSpecsInfo.thms do
      trace[Meta.MethodSpecs] "adding simp theorem for {thm.name} : {thm.type}"
      s := s.addSimpTheorem <| ← mkDSimpTheorem (.other thm.name) thm.levelParams.toArray thm.type
    let ctx ← Simp.mkContext
      (simpTheorems  := #[s])
      (congrTheorems := (← getSimpCongrTheorems))
      (config        := { } ) -- Simp.neutralConfig with dsimp := true, letToHave := false })
    let simprocs ← Simp.getSimprocs

    for (fieldName, implName) in methodSpecsInfo.fieldImpls do
      let some unfoldThm ← getUnfoldEqnFor? implName (nonRec := true)
        | throwError "failed to generate unfolding theorem for {.ofConstName implName}"
      rewriteThm ctx simprocs unfoldThm (instName.str s!"{fieldName}_spec")

      if let some eqnThms ← getEqnsFor? implName then
        for eqnThm in eqnThms, i in [:eqnThms.size] do
          rewriteThm ctx simprocs eqnThm (instName.str s!"{fieldName}_spec_{i+1}")

def startsWithFollowedByNumber (s p : String) : Bool :=
  s.startsWith p && (s.drop p.length).isNat

def isSpecThmNameFor (env : Environment) (name : Name) : Option Name := do
  let .str p n := name | none
  let attrData ← methodSpecsAttr.getParam? env p
  for fieldName in getStructureFields env attrData.clsName do
    if n == s!"{fieldName}_spec" || startsWithFollowedByNumber n s!"{fieldName}_spec_" then
      return p
  none

public partial def getMethodSpecTheorem (instName : Name) (op : String) : MetaM (Option Name) := do
  let env ← getEnv
  let some _ := methodSpecsAttr.getParam? env instName | return none
  realizeGlobalConstNoOverloadCore (instName.str s!"{op}_spec")

public partial def getMethodSpecTheorems (instName : Name) (op : String) : MetaM (Option (Array Name)) := do
  let some _ := methodSpecsAttr.getParam? (← getEnv) instName | return none
  -- Realize spec theorems
  let _ ← realizeGlobalConstNoOverloadCore (instName.str s!"{op}_spec")
  -- Now collect the generated ones
  let mut i := 0
  let mut thms := #[]
  let env ← getEnv
  while true do
    let thmName := instName.str s!"{op}_spec_{i+1}"
    if env.containsOnBranch thmName then
      thms := thms.push thmName
      i := i + 1
    else
      break
  return some thms

builtin_initialize
  registerReservedNamePredicate fun env name => isSpecThmNameFor env name |>.isSome

  registerReservedNameAction fun name => do
    if let some instName := isSpecThmNameFor (← getEnv) name then
      (genSpecs instName).run'
      return true
    return false


builtin_initialize
   Lean.registerTraceClass `Meta.MethodSpecs
