/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.AddDecl
public import Lean.Meta.Basic
public import Lean.Meta.InferType

public section

namespace Lean

@[extern "lean_mk_cases_on"] opaque mkCasesOnImp (env : Kernel.Environment) (declName : @& Name) : Except Kernel.Exception Declaration

open Meta

/--
Builds a `casesOn`-shaped eliminator for `declName` out of structure projections, under the name
`elimName`, or returns `none` if that is not possible.

`I.casesOn … t minor` as built from `I.rec` reduces only once `t` reduces to a constructor
application, which for a proposition it may never do: proofs are opaque. Applying the minor premise
to the projections of `t` instead sidesteps that. The minor premise expects the fields of
`I.mk x₁ … xₙ` rather than those of `t`, but both are proofs of the same proposition, so proof
irrelevance identifies them.

A single constructor and no indices make the type structure-like, and large elimination then forces
every field to be a proof, which is what makes the projections available: projecting data out of a
proposition is what `Exists` may not do.

The result has the same shape as `mkCasesOnImp` produces: parameters, motive, major premise, minor
premise. It also matches `recOn`, since the type is not recursive.
-/
def mkCasesOnViaProjs? (declName : Name) (elimName : Name) : MetaM (Option DefinitionVal) := do
  let .inductInfo indVal ← getConstInfo declName | return none
  -- For a recursive inductive the minor premise of `I.rec` also takes induction hypotheses
  unless indVal.numCtors == 1 && indVal.numIndices == 0 && !indVal.isRec do return none
  unless (← isPropFormerType indVal.type) do return none
  unless (← isLargeEliminating declName) do return none
  let recInfo ← getConstInfoRec (mkRecName declName)
  let ctorVal ← getConstInfoCtor indVal.ctors.head!
  withLCtx {} {} do
    -- `recInfo.type` is `∀ params (motive : I params → Sort u) (minor : …) (t : I params), motive t`
    forallBoundedTelescope recInfo.type (some (indVal.numParams + 2)) fun xs majorType => do
      let params := xs.extract 0 indVal.numParams
      let motive := xs[indVal.numParams]!
      let minor := xs[indVal.numParams + 1]!
      let .forallE majorName selfType _ majorBI := majorType | return none
      withLocalDecl majorName majorBI selfType fun major => do
        let fields := (Array.range ctorVal.numFields).map (Expr.proj declName · major)
        let ys := params ++ #[motive, major, minor]
        let type ← mkForallFVars ys (mkApp motive major)
        let value ← mkLambdaFVars ys (mkAppN minor fields)
        return some (← mkDefinitionValInferringUnsafe elimName recInfo.levelParams type value .abbrev)

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
