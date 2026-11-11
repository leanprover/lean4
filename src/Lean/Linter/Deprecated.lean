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
import Std.Time.Format
import Std.Time.Zoned

public section

namespace Lean.Linter

open Meta

register_builtin_option linter.deprecated : Bool := {
  defValue := true
  descr := "if true, generate deprecation warnings"
}

register_builtin_option linter.deprecated.deprecatedTarget : Bool := {
  defValue := true
  descr := "if true, warn when a `@[deprecated]` attribute points at a declaration that is \
    itself deprecated"
}

structure DeprecationEntry where
  newName? : Option Name := none
  text? : Option String := none
  since? : Option String := none
  deriving Inhabited

/-- The current date in the local time zone, falling back to UTC if the time zone is unavailable. -/
private def currentDate : IO Std.Time.PlainDate := do
  try Std.Time.PlainDate.now catch _ =>
    return (Std.Time.DateTime.ofTimestamp (← Std.Time.Timestamp.now) .UTC).toPlainDate

/--
Creates a hint for a missing `(since := "...")` clause that offers to append one with the current
date to the deprecation syntax `stx`. Returns the empty message if `stx` has no source position.
-/
def mkSinceHint (stx : Syntax) : CoreM MessageData := do
  let some insertPos := stx.getTailPos? (canonicalOnly := true) | return .nil
  let since := s!"(since := \"{(← currentDate).toLeanDateString}\")"
  MessageData.hint "Add the current date:" (ref? := stx) #[{
    suggestion := " " ++ since
    messageData? := some since
    span? := Syntax.ofRange ⟨insertPos, insertPos⟩
    diffGranularity := .none
    toCodeActionTitle? := some fun _ => s!"Try this: {since}"
  }]

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
  let ext ← registerParametricAttributeExt (α := DeprecationEntry) `Lean.Linter.deprecatedAttr
    (preserveOrder := false)
  registerParametricAttributeForExt (ext := ext) {
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
          if linter.deprecated.deprecatedTarget.get (← getOptions) then
            let disableNote : MessageData := .note m!"This warning can be disabled with \
              `set_option {linter.deprecated.deprecatedTarget.name} false`"
            if let some entry := ParametricAttribute.getParamFromExt? ext (preserveOrder := false) env newName then
              match entry.newName? with
              | none =>
                logWarning <| m!"`{.ofConstName newName true}` is itself deprecated, but without an \
                  explicit replacement; `{.ofConstName declName true}` is being deprecated in favor \
                  of a deprecated declaration" ++ disableNote
              | some next =>
                if next != newName then
                  let mut msg := m!"`{.ofConstName newName true}` is itself deprecated in favor of \
                    `{.ofConstName next true}`; consider deprecating `{.ofConstName declName true}` \
                    in favor of `{.ofConstName next true}` instead" ++ disableNote
                  if let some id := id? then
                    if (id.raw.getRange? (canonicalOnly := true)).isSome then
                      if let some replacement ← MetaM.run' <| unresolveNameGlobalAvoidingLocals? next then
                        msg := msg ++ (← MessageData.hint
                          m!"Deprecate in favor of `{.ofConstName next true}` instead:"
                          #[replacement.toString] (ref? := some id.raw))
                  logWarning msg
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
                    simply replacing the old name with the new name. This is often expected, but \
                    sometimes it indicates that the deprecation is in favor of the wrong \
                    declaration, or that there is a mistake in one of the statements.\n\n\
                    If the type difference is intentional, use `+typeChanged` to silence this \
                    warning." ++ hint
      let text? := text?.map TSyntax.getString
      let since? := since?.map TSyntax.getString
      if id?.isNone && text?.isNone then
        logWarning "`[deprecated]` attribute should specify either a new name or a deprecation message"
      if since?.isNone then
        logWarning <| m!"`[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := \"...\")`" ++
          (← mkSinceHint stx)
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

/--
How a deprecation warning for a constant with a replacement suggests switching to the replacement.
Suggestions are only made when the replacement has the same type as the deprecated constant.
-/
inductive DeprecationHint where
  /-- No suggestion. -/
  | none
  /--
  If the current ref is an identifier that resolves to the deprecated constant, offers to replace it
  with the shortest name that resolves to the replacement.
  -/
  | ident
  /--
  Appends the message computed from the name of the replacement, such as a hint for syntax other
  than a plain identifier, or a note explaining why no hint is offered.
  -/
  | custom (mk : Name → MetaM MessageData)

/--
Creates a hint that offers to replace `ref` by `replacement`. Returns the empty message if `ref`
has no source position.
-/
def mkReplacementHint (ref : Syntax) (replacement : String) : MetaM MessageData := do
  unless (ref.getRange? (canonicalOnly := true)).isSome do return .nil
  m!"Replace the deprecated name:".hint #[replacement] (ref? := some ref)

/--
Creates the hint offered by `DeprecationHint.ident`: if the current ref is an identifier that
resolves to `declName`, offers to replace it with the shortest name that resolves to `newName`.
-/
def mkIdentHint (declName newName : Name) : MetaM MessageData := do
  let ref ← getRef
  let .ident _ _ writtenName _ := ref | return .nil
  if writtenName.hasMacroScopes then return .nil
  unless (← resolveGlobalName writtenName) == [(declName, [])] do return .nil
  let some replacement ← unresolveNameGlobalAvoidingLocals? newName | return .nil
  mkReplacementHint ref replacement.toString

/--
Reports a use of `declName` at the current ref if it is deprecated. Callers should usually use
`checkDeprecatedAt`, which respects `Core.Context.checkDeprecated`.
-/
def checkDeprecated (declName : Name) (hint : DeprecationHint) : MetaM Unit := do
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
        let typesReduciblyDefEq ← areTypesReduciblyDefEq oldDecl newDecl
        if !typesReduciblyDefEq then
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
        if typesReduciblyDefEq then
          match hint with
          | .none => pure ()
          | .ident => msg := msg ++ (← mkIdentHint declName newName)
          | .custom mk => msg := msg ++ (← mk newName)
        pure msg
    logWarning <| .tagged ``deprecatedAttr <|
      m!"`{.ofConstName declName true}` has been deprecated" ++ extraMsg

/--
Reports a use of `declName` at `ref` if it is deprecated, unless deprecation checks are disabled at
`ref` (see `Core.Context.checkDeprecated`).
-/
def checkDeprecatedAt (ref : Syntax) (declName : Name) (hint : DeprecationHint := .ident) :
    MetaM Unit :=
  withRef ref do
    if (← Core.shouldCheckDeprecated ref) then
      checkDeprecated declName hint
