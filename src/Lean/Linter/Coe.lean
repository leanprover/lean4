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

def shouldWarnOnDeprecatedCoercions [Monad m] [MonadOptions m] : m Bool :=
  return (← getOptions).get linter.deprecatedCoercions.name true

def coercionsBannedInCore : List Name := [``optionCoe, ``instCoeSubarrayArray]

def coeLinter : Linter where
  run := fun _ => do
    let mainModule ← getMainModule
    let isCoreModule := mainModule = `lean.run.coeLinter ∨ (mainModule.getRoot ∈ [`Init, `Std])
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
              if true then
                let some attr := deprecatedAttr.getParam? (← getEnv) coeDecl | pure ()
                logWarningAt ci.stx <| .tagged ``deprecatedAttr <|
                  m!"This term uses the deprecated coercion `{.ofConstName coeDecl true}`."
        | _ => pure ()
        return true) (fun _ _ _ _ => return)

builtin_initialize addLinter coeLinter

end Lean.Linter.Coe
