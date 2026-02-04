/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Basic
import Lean.Linter.Basic
import Lean.Elab.InfoTree.Main
import Lean.ExtraModUses
import Init.Data.Int.Order
import Init.Omega

public section

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
        | throwError "Invalid `[deprecated]` attribute syntax"
      let newName? ← id?.mapM Elab.realizeGlobalConstNoOverloadWithInfo
      if let some newName := newName? then
        recordExtraModUseFromDecl (isMeta := false) newName
      let text? := text?.map TSyntax.getString
      let since? := since?.map TSyntax.getString
      if id?.isNone && text?.isNone then
        logWarning "`[deprecated]` attribute should specify either a new name or a deprecation message"
      if since?.isNone then
        logWarning "`[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := \"...\")`"
      return { newName?, text?, since? }
  }

def setDeprecated {m} [Monad m] [MonadEnv m] [MonadError m] (declName : Name) (entry : DeprecationEntry) : m Unit := do
  let env ← getEnv
  match deprecatedAttr.setParam env declName entry with
  | Except.ok env   => setEnv env
  | Except.error ex => throwError ex

def isDeprecated (env : Environment) (declName : Name) : Bool :=
  Option.isSome <| deprecatedAttr.getParam? env declName

def _root_.Lean.MessageData.isDeprecationWarning (msg : MessageData) : Bool :=
  msg.hasTag (· == ``deprecatedAttr)

def getDeprecatedNewName (env : Environment) (declName : Name) : Option Name := do
  (← deprecatedAttr.getParam? env declName).newName?

open Meta in
def checkDeprecated (declName : Name) : MetaM Unit := do
  if getLinterValue linter.deprecated (← getLinterOptions) then
    let some attr := deprecatedAttr.getParam? (← getEnv) declName | pure ()
    let extraMsg ← match attr.text?, attr.newName? with
      | some text, _ => pure m!": {text}"
      | none, none => pure m!""
      | none, some newName => do
        let mut msg := m!": Use `{.ofConstName newName true}` instead"
        let env ← getEnv
        let oldPfx := declName.getPrefix
        let newPfx := newName.getPrefix
        let some oldDecl := env.find? declName | pure msg
        let some newDecl := env.find? newName | pure msg
        if !(← withReducible <| isDefEqGuarded oldDecl.type newDecl.type) then
          msg := msg ++ .note m!"The updated constant has a different type:{indentExpr newDecl.type}\
            \ninstead of{indentExpr oldDecl.type}"
        unless oldPfx.isAnonymous do
          -- Check namespace, then visibility, exclusively and in this order, to avoid redundancy
          if oldPfx != newPfx then
            let changeEx := if let .str _ oldRoot := declName then
              m!" (e.g., from `x.{oldRoot}` to `{.ofConstName newName} x`)"
            else .nil
            msg := msg ++ .note m!"The updated constant is in a different namespace. \
              Dot notation may need to be changed{changeEx}."
          else if !(isProtected env declName) && isProtected env newName then
            let pfxComps := newPfx.componentsRev
            let pfxCompStr := if _ : pfxComps.length > 1 then m!"at least the last component `{pfxComps[0]}` of " else ""
            msg := msg ++ .note m!"`{.ofConstName newName true}` is protected. References to this \
              constant must include {pfxCompStr}its prefix `{newPfx}` even when inside its namespace."
        pure msg
    logWarning <| .tagged ``deprecatedAttr <|
      m!"`{.ofConstName declName true}` has been deprecated" ++ extraMsg
