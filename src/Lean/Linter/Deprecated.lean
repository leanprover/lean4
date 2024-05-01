/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Linter.Basic
import Lean.Attributes
import Lean.Elab.InfoTree.Main

namespace Lean.Linter

register_builtin_option linter.deprecated : Bool := {
  defValue := true
  descr := "if true, generate deprecation warnings"
}

structure DeprecationEntry where
  newName? : Option Name := none
  text? : Option String := none
  since? : Option String := none
  deriving Inhabited

builtin_initialize deprecatedAttr : ParametricAttribute DeprecationEntry ←
  registerParametricAttribute {
    name := `deprecated
    descr := "mark declaration as deprecated",
    getParam := fun _ stx => do
      let `(attr| deprecated $[$id?]? $[$text?]? $[(since := $since?)]?) := stx
        | throwError "invalid `[deprecated]` attribute"
      let newName? ← id?.mapM Elab.realizeGlobalConstNoOverloadWithInfo
      let text? := text?.map TSyntax.getString
      let since? := since?.map TSyntax.getString
      return { newName?, text?, since? }
  }

def isDeprecated (env : Environment) (declName : Name) : Bool :=
  Option.isSome <| deprecatedAttr.getParam? env declName

def _root_.Lean.MessageData.isDeprecationWarning (msg : MessageData) : Bool :=
  msg.hasTag (· == ``deprecatedAttr)

def getDeprecatedNewName (env : Environment) (declName : Name) : Option Name := do
  (← deprecatedAttr.getParam? env declName).newName?

def checkDeprecated [Monad m] [MonadEnv m] [MonadLog m] [AddMessageContext m] [MonadOptions m] (declName : Name) : m Unit := do
  if getLinterValue linter.deprecated (← getOptions) then
    let some attr := deprecatedAttr.getParam? (← getEnv) declName | pure ()
    logWarning <| .tagged ``deprecatedAttr <| attr.text?.getD <|
      match attr.newName? with
      | none => s!"`{declName}` has been deprecated"
      | some newName => s!"`{declName}` has been deprecated, use `{newName}` instead"
