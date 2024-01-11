/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Linter.Basic
import Lean.Attributes
import Lean.Elab.InfoTree.Main

namespace Lean.Linter

register_builtin_option linter.deprecated : Bool := {
  defValue := true
  descr := "if true, generate deprecation warnings"
}

builtin_initialize deprecatedAttr : ParametricAttribute (Option Name) ←
  registerParametricAttribute {
    name := `deprecated
    descr := "mark declaration as deprecated",
    getParam := fun _ stx => do
     match stx with
     | `(attr| deprecated $[$id?]?) =>
       let some id := id? | return none
       let declNameNew ← Elab.resolveGlobalConstNoOverloadWithInfo id
       return some declNameNew
     | _  => throwError "invalid `[deprecated]` attribute"
  }

def isDeprecated (env : Environment) (declName : Name) : Bool :=
  Option.isSome <| deprecatedAttr.getParam? env declName

def _root_.Lean.MessageData.isDeprecationWarning (msg : MessageData) : Bool :=
  msg.hasTag (· == ``deprecatedAttr)

def getDeprecatedNewName (env : Environment) (declName : Name) : Option Name :=
  (deprecatedAttr.getParam? env declName).getD none

def checkDeprecated [Monad m] [MonadEnv m] [MonadLog m] [AddMessageContext m] [MonadOptions m] (declName : Name) : m Unit := do
  if getLinterValue linter.deprecated (← getOptions) then
    match deprecatedAttr.getParam? (← getEnv) declName with
    | none => pure ()
    | some none => logWarning <| .tagged ``deprecatedAttr m!"`{declName}` has been deprecated"
    | some (some newName) => logWarning <| .tagged ``deprecatedAttr m!"`{declName}` has been deprecated, use `{newName}` instead"
