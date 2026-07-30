/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Basic
import Lean.Linter.Init
import Lean.Elab.InfoTree.Main
import Lean.ExtraModUses
import Lean.Meta.Hint
import Init.Data.List.MapIdx
import Init.Omega

public section

namespace Lean.Linter

open Meta

register_builtin_option linter.deprecated : Bool := {
  defValue := true
  descr := "if true, generate deprecation warnings"
}

structure DeprecationEntry where
  newName? : Option Name := none
  text? : Option String := none
  since? : Option String := none
  deriving Inhabited

/--
This is the predicate we use to decide whether the old and new type of a declaration differ for the
purpose of error reporting.
-/
private def areTypesReduciblyDefEq (decl₁ decl₂ : ConstantInfo) : MetaM Bool := do
  if decl₁.numLevelParams != decl₂.numLevelParams then
    return false
  let levels := decl₁.levelParams.mapIdx fun i _ => mkLevelParam <| Name.num `_deprecated i
  let type₁ := decl₁.instantiateTypeLevelParams levels
  let type₂ := decl₂.instantiateTypeLevelParams levels
  withReducible <| isDefEqGuarded type₁ type₂

builtin_initialize deprecatedAttr : ParametricAttribute DeprecationEntry ←
  registerParametricAttribute {
    name := `deprecated
    descr := "mark declaration as deprecated",
    getParam := fun declName stx => do
      let `(attr| deprecated $[$id?]? $[$text?]? $[$typeChanged?]? $[(since := $since?)]?) := stx
        | throwError "Invalid `[deprecated]` attribute syntax"
      let newName? ← id?.mapM Elab.realizeGlobalConstNoOverloadWithInfo
      if newName? == some declName then
        throwError "Invalid `[deprecated]` attribute: `{.ofConstName declName true}` cannot be deprecated in favor of itself"
      if let some newName := newName? then
        recordExtraModUseFromDecl (isMeta := false) newName
        if getLinterValue linter.deprecated (← getLinterOptions) then
          let env ← getEnv
          if let some oldDecl := env.find? declName then
            if let some newDecl := env.find? newName then
              if ← MetaM.run' <| areTypesReduciblyDefEq oldDecl newDecl then
                if typeChanged?.isSome then
                  logWarning "The `+typeChanged` marker is not needed because the updated constant has the same type."
              else if typeChanged?.isNone then
                let insertPos? := text?.bind (·.raw.getTailPos? (canonicalOnly := true)) <|>
                  id?.bind (·.raw.getTailPos? (canonicalOnly := true))
                let hint ← if let some insertPos := insertPos? then
                  MessageData.hint "Add `+typeChanged`:" #[{
                    suggestion := " +typeChanged"
                    messageData? := some "+typeChanged"
                    span? := Syntax.ofRange ⟨insertPos, insertPos⟩
                    diffGranularity := .none
                    toCodeActionTitle? := some fun _ => "Try this: +typeChanged"
                  }]
                else
                  pure <| MessageData.hint' "Add `+typeChanged` to silence this warning."
                logWarning <|
                  m!"The updated constant has a different type:\
                    {indentExpr newDecl.type}\ninstead of{indentExpr oldDecl.type}\n\n\
                    This suggests that addressing the deprecation might be more involved than \
                    simply replacing the old name with the new name. This is often excepected, but \
                    sometimes it indicates that the deprecation is in favor of the wrong \
                    declaration, or that there is a mistake in one of the statements.\n\n\
                    If the type difference is intentional, use `+typeChanged` to silence this \
                    warning." ++ hint
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
        if !(← areTypesReduciblyDefEq oldDecl newDecl) then
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
