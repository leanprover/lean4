/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Lean.Elab.Command
public import Lean.Server.InfoUtils
import Lean.Linter.Basic
import Lean.Linter.Deprecated
import all Lean.Elab.Term.TermElabM

public section
set_option linter.missingDocs true -- keep it documented

namespace Lean.Linter.Coe

/--
`set_option linter.deprecatedCoercions true` enables a linter emitting warnings on deprecated
coercions.
-/
register_builtin_option linter.deprecatedCoercions : Bool := {
  defValue := true
  descr := "Validate that no deprecated coercions are used."
}

/--
Checks whether the "deprecated coercions" linter is enabled.
-/
def shouldWarnOnDeprecatedCoercions [Monad m] [MonadOptions m] : m Bool :=
  return (← getOptions).get linter.deprecatedCoercions.name true

/-- A list of coercion names that must not be used in core. -/
def coercionsBannedInCore : Array Name := #[``optionCoe, ``instCoeSubarrayArray]

/-- Validates that no coercions are used that are either deprecated or are banned in core. -/
def coeLinter : Linter where
  run := fun _ => do
    let mainModule ← getMainModule
    let isCoreModule := mainModule = `lean.run.linterCoe ∨ (mainModule.getRoot ∈ [`Init, `Std])
    let shouldWarnOnDeprecated := getLinterValue linter.deprecatedCoercions (← getLinterOptions)
    let trees ← Elab.getInfoTrees
    for tree in trees do
      tree.visitM' (m := Elab.Command.CommandElabM) (fun _ info _ => do
        match info with
        | .ofCustomInfo ci =>
          if let some trace := ci.value.get? Elab.Term.CoeExpansionTrace then
            for coeDecl in trace.expandedCoeDecls do
              if isCoreModule && coeDecl ∈ coercionsBannedInCore then
                logWarningAt ci.stx m!"This term uses the coercion `{coeDecl}`, which is banned in Lean's core library."
              if shouldWarnOnDeprecated then
                let some attr := deprecatedAttr.getParam? (← getEnv) coeDecl | pure ()
                logLint linter.deprecatedCoercions ci.stx <| .tagged ``deprecatedAttr <|
                  m!"This term uses the deprecated coercion `{.ofConstName coeDecl true}`."
        | _ => pure ()
        return true) (fun _ _ _ _ => return)

builtin_initialize addLinter coeLinter

end Lean.Linter.Coe
