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

-- The following deprecations are have their replacements defined in earlier files,
-- and as `deprecated` can not be applied to imported declarations,
-- we have moved the old versions here.

/-- Deprecated synyonym for `congr_arg`. -/
@[deprecated congr_arg]
theorem congrArg {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β) (h : Eq a₁ a₂) : Eq (f a₁) (f a₂) :=
  h ▸ rfl


/-- Deprecated synyonym for `congr_fun`. -/
@[deprecated congr_fun]
theorem congrFun {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x} (h : Eq f g) (a : α) : Eq (f a) (g a) :=
  h ▸ rfl
