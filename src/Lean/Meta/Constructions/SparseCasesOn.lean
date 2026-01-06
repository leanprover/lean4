/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module
prelude
public import Lean.Meta.Basic
import Lean.AddDecl
import Lean.Meta.Constructions.CtorIdx
import Lean.Meta.AppBuilder
import Lean.Meta.HasNotBit
import Lean.Meta.WHNF
/-!  See `mkSparseCasesOn` below.  -/

namespace Lean.Meta


private structure SparseCasesOnKey where
  indName : Name
  ctors   : Array Name
  -- When this is created in a private context and thus may contain private references, we must
  -- not reuse it in an exported context.
  isPrivate : Bool
deriving BEq, Hashable

private builtin_initialize sparseCasesOnCacheExt : EnvExtension (PHashMap SparseCasesOnKey Name) ←
  registerEnvExtension (pure {}) (asyncMode := .local)  -- mere cache, keep it local

/-- Information necessary to recognize and split on sparse casesOn (in particular in MatchEqs) -/
public structure SparseCasesOnInfo where
  indName : Name
  majorPos : Nat
  arity : Nat
  insterestingCtors : Array Name
deriving Inhabited

private builtin_initialize sparseCasesOnInfoExt : MapDeclarationExtension SparseCasesOnInfo ←
  mkMapDeclarationExtension (exportEntriesFn := fun env s _ =>
    -- Do not export for non-exposed defs
    s.filter (fun n _ => env.find? n |>.any (·.hasValue)) |>.toArray)

/--
This module creates sparse variants of `casesOn` that have arms only for some of the constructors,
offering a catch-all.

The minor arguments come in the order of the given `ctors` array.

The catch-all provides a `Nat.hasNotBit mask x.ctorIdx` hypothesis to express that these constructors
were not matched. Using a single hypothesis like this, rather than many hypotheses of the form
`x.ctorIdx ≠ i`, is important to avoid quadratic overhead in code like match splitter generation.

This function is implemented with a simple call to `.rec`, i.e. no clever branching on the constructor
index. The compiler has native support for these sparse matches anyways, and kernel reduction would
not benefit from a more sophisticated implementation unless it has itself native support for
`.ctorIdx` and constructor elimination functions.
-/
public def mkSparseCasesOn (indName : Name) (ctors : Array Name) : MetaM Name := do
  let env ← getEnv
  let key := { indName, ctors , isPrivate := env.header.isModule && !env.isExporting}
  if let some name := (sparseCasesOnCacheExt.getState env).find? key then
    return name

  let declName ← mkAuxDeclName (kind := `_sparseCasesOn)

  let indInfo ← getConstInfoInduct indName
  for ctor in ctors do
    unless indInfo.ctors.contains ctor do
      throwError "mkSparseCasesOn: constructor {ctor} is not a constructor of {indName}"
  if ctors.size = indInfo.ctors.length then
      throwError "mkSparseCasesOn: requested casesOn combinator is not sparse"


  let casesOnName := mkCasesOnName indName
  let casesOnInfo ← getConstInfo casesOnName
  let ctorIdxName := mkCtorIdxName indName

  unless casesOnInfo.levelParams.length = indInfo.levelParams.length + 1 do
    throwError "mkSparseCasesOn: unexpected number of universe parameters in `{.ofConstName casesOnName}`"
  let _::lps := casesOnInfo.levelParams | unreachable!
  let us := lps.map mkLevelParam

  let (value : Expr) ← forallTelescope casesOnInfo.type fun xs _ => do
    unless xs.size = indInfo.numParams + 1 + indInfo.numIndices + 1 + indInfo.ctors.length do
      throwError "mkSparseCasesOn: unexpected number of parameters in type of `{.ofConstName casesOnName}`"
    let params := xs[:indInfo.numParams]
    let motive := xs[indInfo.numParams]!
    let indices := xs[indInfo.numParams+1:indInfo.numParams+1+indInfo.numIndices]
    let major := xs[indInfo.numParams+1+indInfo.numIndices]!
    let ism := indices ++ #[major]
    let minors := xs[indInfo.numParams+1+indInfo.numIndices+1:]

    let minors' ← ctors.mapM fun ctor => do
      let ctorInfo ← getConstInfoCtor ctor
      let minor := minors[ctorInfo.cidx]!
      pure minor

    let overlappingIdxs ← ctors.mapM fun ctor => return (← getConstInfoCtor ctor).cidx
    let catchAllType ← id do
      let ctorIdxApp := mkAppN (mkConst ctorIdxName us) (params ++ indices ++ #[major])
      let hyp := mkHasNotBit ctorIdxApp overlappingIdxs
      withLocalDeclD `h hyp fun h =>
        mkForallFVars #[h] (mkAppN motive ism)

    let e := casesOnInfo.value!
    let e := mkAppN e params
    let motive' ← id do
      mkLambdaFVars ism (mkForall (← mkFreshUserName `else) BinderInfo.default catchAllType (mkAppN motive ism))
    let e := mkApp e motive'
    let e := mkAppN e indices
    let e := mkApp e major
    let altTypes ← inferArgumentTypesN indInfo.ctors.length e
    let e := mkAppN e <| ← indInfo.ctors.toArray.zipWithM (bs := altTypes) fun ctor t =>
      forallTelescope t fun ys _ => do
        let fields := ys.pop
        let elseMinor := ys.back!
        if let some idx := ctors.idxOf? ctor then
          mkLambdaFVars ys (mkAppN minors'[idx]! fields)
        else
          let ctorInfo ← getConstInfoCtor ctor
          let idx := ctorInfo.cidx
          mkLambdaFVars ys (mkApp elseMinor (← mkHasNotBitProof (mkRawNatLit idx) overlappingIdxs))
    -- Unfold the `casesOn` to `rec` for faster reduction
    let e ← Core.betaReduce e
    mkLambdaFVars (params ++ #[motive] ++ indices ++ #[major] ++ minors') e

  -- logInfo m!"mkSparseCasesOn {declName} : {value}"
  let decl ← mkDefinitionValInferringUnsafe
    (name        := declName)
    (levelParams := casesOnInfo.levelParams)
    (type        := (← inferType value))
    (value       := value)
    (hints       := ReducibilityHints.abbrev)
  addDecl (.defnDecl decl)
  modifyEnv fun env => sparseCasesOnCacheExt.modifyState env fun s => s.insert key declName
  setReducibleAttribute declName
  modifyEnv fun env => markSparseCasesOn env declName
  modifyEnv fun env => sparseCasesOnInfoExt.insert env declName {
    indName
    majorPos := indInfo.numParams + 1 + indInfo.numIndices,
    arity := indInfo.numParams + 1 + indInfo.numIndices + 1 + ctors.size + 1
    insterestingCtors := ctors
  }
  enableRealizationsForConst declName
  pure declName

public def getSparseCasesOnInfoCore (env : Environment) (sparseCasesOnName : Name) : (Option SparseCasesOnInfo) := do
  sparseCasesOnInfoExt.find? env sparseCasesOnName

public def getSparseCasesOnInfo (sparseCasesOnName : Name) : CoreM (Option SparseCasesOnInfo) := do
  let env ← getEnv
  return sparseCasesOnInfoExt.find? env sparseCasesOnName
