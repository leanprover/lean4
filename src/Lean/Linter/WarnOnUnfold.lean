/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Lean.Elab.Command
public import Lean.Server.InfoUtils
import Lean.Linter.Basic
import Lean.ReducibilityAttrs

public section
set_option linter.missingDocs true

namespace Lean.Linter.WarnOnUnfold

/--
`set_option linter.warnOnUnfold true` enables a linter that warns when code relies on the
definitional equality `Id α = α` rather than using `Id.run` or monadic operations.
-/
register_builtin_option linter.warnOnUnfold : Bool := {
  defValue := true
  descr := "Warn when code relies on `Id α` being definitionally equal to `α`."
}

/-- Check if an expression contains a reference to the `Id` constant. -/
private def mentionsId (e : Expr) : Bool :=
  e.find? (·.isConstOf ``Id) |>.isSome

/-- A linter that warns when code relies on the definitional unfolding of `Id`. -/
def warnOnUnfoldLinter : Linter where
  run := fun _ => do
    let enabled := getLinterValue linter.warnOnUnfold (← getLinterOptions)
    unless enabled do return
    let trees ← Elab.getInfoTrees
    let warnedRanges : IO.Ref (Std.HashSet Lean.Syntax.Range) ← IO.mkRef {}
    for tree in trees do
      tree.visitM' (m := Elab.Command.CommandElabM) (postNode := fun ci info _ => do
        match info with
        | .ofTermInfo ti =>
          let some expectedType := ti.expectedType? | return
          let some range := info.range? | return
          -- Skip macro-generated syntax
          let .original .. := ti.stx.getHeadInfo | return
          -- Skip already-warned ranges
          if (← warnedRanges.get).contains range then return
          -- Check if linter is disabled locally
          if !linter.warnOnUnfold.get ci.options then return
          -- Run the check in an isolated MetaM context
          let reliesOnIdUnfold : Bool ← try
            ti.runMetaM ci do
              let actualType ← Meta.inferType ti.expr
              let actualType ← instantiateMVars actualType
              let expectedType ← instantiateMVars expectedType
              -- Skip partially-applied functions: if the inferred type is a function
              -- but the expected type is not, this is a TermInfo for a function head
              -- where the expectedType reflects the result, not the function type
              if actualType.isForall && !expectedType.isForall then return false
              -- Quick check: if neither type mentions Id, skip
              unless mentionsId actualType || mentionsId expectedType do return false
              -- Check 1: types must be defEq with normal (default) transparency.
              -- If not, they were matched via coercion/lifting, not Id unfolding.
              let eqNormally ← Meta.withoutModifyingMCtx <|
                Meta.isDefEq actualType expectedType
              unless eqNormally do return false
              -- Check 2: temporarily make `Id` irreducible and test again.
              -- `addLocalEntry` creates a new env value with a local override (pure, no
              -- shared-state mutation).  We swap it into the isolated `CoreM` state created
              -- by `ti.runMetaM ci` (via `ContextInfo.runCoreM` / `toIO`), so `modifyEnv`
              -- only touches a local ref—no concurrency issues.
              let env ← getEnv
              let modifiedEnv :=
                reducibilityExtraExt.addLocalEntry env (``Id, .irreducible)
              modifyEnv fun _ => modifiedEnv
              let eqWithIdIrreducible ← Meta.withoutModifyingMCtx <|
                Meta.isDefEq actualType expectedType
              modifyEnv fun _ => env
              return !eqWithIdIrreducible
          catch _ => pure false
          if reliesOnIdUnfold then
            warnedRanges.modify (·.insert range)
            logLint linter.warnOnUnfold ti.stx
              m!"This code relies on the definitional equality `Id α = α`."
        | _ => pure ())

builtin_initialize addLinter warnOnUnfoldLinter

end Lean.Linter.WarnOnUnfold
