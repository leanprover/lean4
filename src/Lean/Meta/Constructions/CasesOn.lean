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
Whether `casesOn` for `declName` is built by `mkCasesOnViaProjs?` rather than from the recursor.

A single constructor and no indices make the type structure-like, and large elimination then forces
every field to be a proof, which is what makes the projections available: projecting data out of a
proposition is what `Exists` may not do.
-/
def isCasesOnViaProjs (declName : Name) : MetaM Bool := do
  let .inductInfo indVal ← getConstInfo declName | return false
  -- For a recursive inductive the minor premise of `I.rec` also takes induction hypotheses
  unless indVal.numCtors == 1 && indVal.numIndices == 0 && !indVal.isRec do return false
  unless (← isPropFormerType indVal.type) do return false
  isLargeEliminating declName

/--
Builds a `casesOn`-shaped eliminator for `declName` out of structure projections, or returns `none`
if `isCasesOnViaProjs` does not hold.

`I.casesOn … t minor` as built from `I.rec` reduces only once `t` reduces to a constructor
application, which for a proposition it may never do: proofs are opaque. Applying the minor premise
to the projections of `t` instead sidesteps that. The minor premise expects the fields of
`I.mk x₁ … xₙ` rather than those of `t`, but both are proofs of the same proposition, so proof
irrelevance identifies them.

The result has the same shape as `mkCasesOnImp` produces: parameters, motive, major premise, minor
premise. It also matches `recOn`, since the type is not recursive.
-/
def mkCasesOnViaProjs? (declName : Name) : MetaM (Option DefinitionVal) := do
  unless (← isCasesOnViaProjs declName) do return none
  let indVal ← getConstInfoInduct declName
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
        -- The kernel infers the type of a projection by walking the constructor's telescope up to
        -- the projected field, so checking this is quadratic in the number of fields. Applying the
        -- projection functions instead would be linear, but they do not exist yet at this point.
        let fields := (Array.range ctorVal.numFields).map (Expr.proj declName · major)
        let ys := params ++ #[motive, major, minor]
        let type ← mkForallFVars ys (mkApp motive major)
        let value ← mkLambdaFVars ys (mkAppN minor fields)
        return some (← mkDefinitionValInferringUnsafe (mkCasesOnName declName) recInfo.levelParams
          type value .abbrev)

def mkCasesOn (declName : Name) : MetaM Unit := do
  withTraceNode `Meta.mkCasesOn (fun _ => return m!"{declName}") do
  let name := mkCasesOnName declName
  let decl ←
    match ← mkCasesOnViaProjs? declName with
    | some decl => pure (.defnDecl decl)
    | none => ofExceptKernelException (mkCasesOnImp (← getEnv).toKernelEnv declName)
  addDecl decl
  setReducibleAttribute name
  modifyEnv fun env => markAuxRecursor env name
  enableRealizationsForConst name

builtin_initialize
  registerTraceClass `Meta.mkCasesOn

end Lean
