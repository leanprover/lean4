/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.AddDecl
public import Lean.Meta.Basic

public section

namespace Lean

@[extern "lean_mk_cases_on"] opaque mkCasesOnImp (env : Kernel.Environment) (declName : @& Name) : Except Kernel.Exception Declaration

open Meta

/-- The first of `u`, `u_1`, `u_2`, … that is not in `lparams`. -/
private def mkUnusedLevelParamName (lparams : List Name) : Name :=
  let cands := (List.range (lparams.length + 1)).map fun i =>
    if i == 0 then `u else (`u).appendIndexAfter i
  (cands.find? (!lparams.contains ·)).getD `u

/--
Builds a `casesOn`-shaped eliminator for `declName` out of structure projections, under the name
`elimName`, or returns `none` if that is not possible.

The kernel restricts the recursor of a single-constructor inductive type whose resulting universe
can be `Prop` (such as `PSigma`, which lives in `Sort (max u v)`) to motives in `Prop`. Projections
remain available for such a type, and together with eta for structures they yield an eliminator at
an arbitrary motive universe. This is only used when the recursor is restricted; otherwise the
recursor-based construction is the one that runs.

The result has the same shape as `mkCasesOnImp` produces: parameters, motive, major premise, minor
premise. It also matches `recOn`, since the type is not recursive.
-/
def mkCasesOnViaProjs? (declName : Name) (elimName : Name) : MetaM (Option DefinitionVal) := do
  let .inductInfo indVal ← getConstInfo declName | return none
  unless indVal.numCtors == 1 && indVal.numIndices == 0 && !indVal.isRec do return none
  let recInfo ← getConstInfoRec (mkRecName declName)
  -- A large-eliminating recursor carries one more level parameter than the type: its motive universe.
  unless recInfo.levelParams.length == indVal.levelParams.length do return none
  -- A `Prop` may have fields that are not proofs (as in `Exists`), and then it has no projections.
  if (← isPropFormerType indVal.type) then return none
  let ctorVal ← getConstInfoCtor indVal.ctors.head!
  let w := mkUnusedLevelParamName indVal.levelParams
  withLCtx {} {} do
    -- `recInfo.type` is `∀ params (motive : I params → Prop) (minor : …) (t : I params), motive t`
    forallBoundedTelescope recInfo.type (some (indVal.numParams + 2)) fun xs majorType => do
      let params := xs.extract 0 indVal.numParams
      let motiveDecl ← xs[indVal.numParams]!.fvarId!.getDecl
      let minorDecl ← xs[indVal.numParams + 1]!.fvarId!.getDecl
      let .forallE majorName selfType _ majorBI := majorType | return none
      withLocalDecl motiveDecl.userName motiveDecl.binderInfo (← mkArrow selfType (.sort (.param w)))
          fun motive => do
        let minorType := minorDecl.type.replaceFVar motiveDecl.toExpr motive
        withLocalDecl minorDecl.userName minorDecl.binderInfo minorType fun minor => do
          withLocalDecl majorName majorBI selfType fun major => do
            let fields := (Array.range ctorVal.numFields).map (Expr.proj declName · major)
            let ys := params ++ #[motive, major, minor]
            let type ← mkForallFVars ys (mkApp motive major)
            let value ← mkLambdaFVars ys (mkAppN minor fields)
            return some (← mkDefinitionValInferringUnsafe elimName
              (w :: indVal.levelParams) type value .abbrev)

def mkCasesOn (declName : Name) : MetaM Unit := do
  withTraceNode `Meta.mkCasesOn (fun _ => return m!"{declName}") do
  let name := mkCasesOnName declName
  let decl ←
    match ← mkCasesOnViaProjs? declName name with
    | some decl => pure (.defnDecl decl)
    | none => ofExceptKernelException (mkCasesOnImp (← getEnv).toKernelEnv declName)
  addDecl decl
  setReducibleAttribute name
  modifyEnv fun env => markAuxRecursor env name
  enableRealizationsForConst name

builtin_initialize
  registerTraceClass `Meta.mkCasesOn

end Lean
