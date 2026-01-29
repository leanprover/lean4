/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
import Lean.DocString
public import Lean.Elab.Command
public import Lean.Parser.Tactic.Doc

public section

namespace Lean.Elab.Tactic.Doc
open Lean.Parser.Tactic.Doc
open Lean.Elab.Command
open Lean.Parser.Command

@[builtin_command_elab «tactic_extension»] def elabTacticExtension : CommandElab
  | `(«tactic_extension»|tactic_extension%$cmd $_) => do
    throwErrorAt cmd "Missing documentation comment"
  | `(«tactic_extension»|$docs:docComment tactic_extension $tac:ident) => do
    let tacName ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo tac

    if let some tgt' := alternativeOfTactic (← getEnv) tacName then
        throwErrorAt tac "`{.ofConstName tacName}` is an alternative form of `{.ofConstName tgt'}`"
    if !(isTactic (← getEnv) tacName) then
      throwErrorAt tac "`{.ofConstName tacName}` is not a tactic"

    modifyEnv (tacticDocExtExt.addEntry · (tacName, docs.getDocString))
    pure ()
  | _ => throwError "Malformed tactic extension command"

@[builtin_command_elab «register_tactic_tag»] def elabRegisterTacticTag : CommandElab
  | `(«register_tactic_tag»|$[$doc:docComment]? register_tactic_tag $tag:ident $user:str) => do
    let docstring ← doc.mapM getDocStringText
    modifyEnv (knownTacticTagExt.addEntry · (tag.getId, user.getString, docstring))
  | _ => throwError "Malformed 'register_tactic_tag' command"

/--
Computes a table that heuristically maps parser syntax kinds to their first tokens by inspecting the
Pratt parsing tables for the `tactic syntax kind. If a custom name is provided for the tactic, then
it is returned instead.
-/
def firstTacticTokens [Monad m] [MonadEnv m] : m (NameMap String) := do
  let env ← getEnv

  let some tactics := (Lean.Parser.parserExtension.getState env).categories.find? `tactic
    | return {}

  let mut firstTokens : NameMap String :=
    tacticNameExt.toEnvExtension.getState env
      |>.importedEntries
      |>.push (tacticNameExt.exportEntriesFn env (tacticNameExt.getState env) .exported)
      |>.foldl (init := {}) fun names inMods =>
        inMods.foldl (init := names) fun names (k, n) =>
          names.insert k n

  firstTokens := addFirstTokens tactics tactics.tables.leadingTable firstTokens
  firstTokens := addFirstTokens tactics tactics.tables.trailingTable firstTokens

  return firstTokens
where
  addFirstTokens tactics table firsts : NameMap String := Id.run do
    let mut firsts := firsts
    for (tok, ps) in table do
      -- Skip antiquotes
      if tok == `«$» then continue
      for (p, _) in ps do
        for (k, ()) in p.info.collectKinds {} do
          if tactics.kinds.contains k then
            let tok := tok.toString (escape := false)
            -- It's important here that the already-existing mapping is preserved, because it will
            -- contain any user-provided custom name, and these shouldn't be overridden.
            firsts := firsts.alter k (·.getD tok)
    return firsts

/--
Creates some `MessageData` for a parser name.

If the parser name maps to a description with an
identifiable leading token, then that token is shown. Otherwise, the underlying name is shown
without an `@`. The name includes metadata that makes infoview hovers and the like work. This
only works for global constants, as the local context is not included.
-/
private def showParserName [Monad m] [MonadEnv m] (firsts : NameMap String) (n : Name) : m MessageData := do
  let env ← getEnv
  let params :=
    env.constants.find?' n |>.map (·.levelParams.map Level.param) |>.getD []

  let tok := ((← customTacticName n) <|> firsts.get? n).map Std.Format.text |>.getD (format n)
  pure <| .ofFormatWithInfos {
    fmt := "`" ++ .tag 0 tok ++ "`",
    infos :=
      .ofList [(0, .ofTermInfo {
        lctx := .empty,
        expr := .const n params,
        stx := .ident .none (toString n).toRawSubstring n [.decl n []],
        elaborator := `Delab,
        expectedType? := none
      })] _
  }

/--
Displays all available tactic tags, with documentation.
-/
@[builtin_command_elab printTacTags] def elabPrintTacTags : CommandElab := fun _stx => do
  let all :=
    tacticTagExt.toEnvExtension.getState (← getEnv)
      |>.importedEntries |>.push (tacticTagExt.exportEntriesFn (← getEnv) (tacticTagExt.getState (← getEnv)) .exported)
  let mut mapping : NameMap NameSet := {}
  for arr in all do
    for (tac, tag) in arr do
      mapping := mapping.insert tag (mapping.getD tag {} |>.insert tac)

  let firsts ← firstTacticTokens

  let showDocs : Option String → MessageData
    | none => .nil
    | some d => Format.line ++ MessageData.joinSep ((d.split '\n').map (toMessageData ∘ String.Slice.copy)).toList Format.line

  let showTactics (tag : Name) : CommandElabM MessageData := do
    match mapping.find? tag with
    | none => pure .nil
    | some tacs =>
      if tacs.isEmpty then pure .nil
      else
        let tacs := tacs.toArray.qsort (·.toString < ·.toString) |>.toList
        pure (Format.line ++ MessageData.joinSep (← tacs.mapM (showParserName firsts)) ", ")

  let tagDescrs ← (← allTagsWithInfo).mapM fun (name, userName, docs) => do
    pure <| m!"• " ++
      MessageData.nestD (m!"`{name}`" ++
        (if name.toString != userName then m!" — \"{userName}\"" else MessageData.nil) ++
        showDocs docs ++
        (← showTactics name))

  let tagList : MessageData :=
    m!"Available tags: {MessageData.nestD (Format.line ++ .joinSep tagDescrs Format.line)}"

  logInfo tagList

/--
The information needed to display all documentation for a tactic.
-/
structure TacticDoc where
  /-- The name of the canonical parser for the tactic -/
  internalName : Name
  /-- The user-facing name to display (typically the first keyword token) -/
  userName : String
  /-- The tags that have been applied to the tactic -/
  tags : NameSet
  /-- The docstring for the tactic -/
  docString : Option String
  /-- Any docstring extensions that have been specified -/
  extensionDocs : Array String

def allTacticDocs (includeUnnamed : Bool := true) : MetaM (Array TacticDoc) := do
  let env ← getEnv
  let allTags :=
    tacticTagExt.toEnvExtension.getState env |>.importedEntries
      |>.push (tacticTagExt.exportEntriesFn env (tacticTagExt.getState env) .exported)
  let mut tacTags : NameMap NameSet := {}
  for arr in allTags do
    for (tac, tag) in arr do
      tacTags := tacTags.insert tac (tacTags.getD tac {} |>.insert tag)

  let mut docs := #[]

  let some tactics := (Lean.Parser.parserExtension.getState env).categories.find? `tactic
    | return #[]

  let firstTokens ← firstTacticTokens

  for (tac, _) in tactics.kinds do
    -- Skip noncanonical tactics
    if let some _ := alternativeOfTactic env tac then continue

    let userName? : Option String := firstTokens.get? tac
    let userName ←
      if let some n := userName? then pure n
      else if includeUnnamed then pure tac.toString
      else continue

    docs := docs.push {
      internalName := tac,
      userName := userName,
      tags := tacTags.getD tac {},
      docString := ← findDocString? env tac,
      extensionDocs := getTacticExtensions env tac
    }
  return docs
