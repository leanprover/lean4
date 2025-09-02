/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Lean.DocString
public import Lean.Elab.Command

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
        throwErrorAt tac "`{tacName}` is an alternative form of `{tgt'}`"
    if !(isTactic (← getEnv) tacName) then
      throwErrorAt tac "`{tacName}` is not a tactic"

    modifyEnv (tacticDocExtExt.addEntry · (tacName, docs.getDocString))
    pure ()
  | _ => throwError "Malformed tactic extension command"

@[builtin_command_elab «register_tactic_tag»] def elabRegisterTacticTag : CommandElab
  | `(«register_tactic_tag»|$[$doc:docComment]? register_tactic_tag $tag:ident $user:str) => do
    let docstring ← doc.mapM getDocStringText
    modifyEnv (knownTacticTagExt.addEntry · (tag.getId, user.getString, docstring))
  | _ => throwError "Malformed 'register_tactic_tag' command"

/--
Gets the first string token in a parser description. For example, for a declaration like
`syntax "squish " term " with " term : tactic`, it returns `some "squish "`, and for a declaration
like `syntax tactic " <;;;> " tactic : tactic`, it returns `some " <;;;> "`.

Returns `none` for syntax declarations that don't contain a string constant.
-/
private partial def getFirstTk (e : Expr) : MetaM (Option String) := do
  match (← Meta.whnf e).getAppFnArgs with
  | (``ParserDescr.node, #[_, _, p]) => getFirstTk p
  | (``ParserDescr.trailingNode, #[_, _, _, p]) => getFirstTk p
  | (``ParserDescr.unary, #[.app _ (.lit (.strVal "withPosition")), p]) => getFirstTk p
  | (``ParserDescr.unary, #[.app _ (.lit (.strVal "atomic")), p]) => getFirstTk p
  | (``ParserDescr.binary, #[.app _ (.lit (.strVal "andthen")), p, _]) => getFirstTk p
  | (``ParserDescr.nonReservedSymbol, #[.lit (.strVal tk), _]) => pure (some tk)
  | (``ParserDescr.symbol, #[.lit (.strVal tk)]) => pure (some tk)
  | (``Parser.withAntiquot, #[_, p]) => getFirstTk p
  | (``Parser.leadingNode, #[_, _, p]) => getFirstTk p
  | (``HAndThen.hAndThen, #[_, _, _, _, p1, p2]) =>
    if let some tk ← getFirstTk p1 then pure (some tk)
    else getFirstTk (.app p2 (.const ``Unit.unit []))
  | (``Parser.nonReservedSymbol, #[.lit (.strVal tk), _]) => pure (some tk)
  | (``Parser.symbol, #[.lit (.strVal tk)]) => pure (some tk)
  | _ => pure none


/--
Creates some `MessageData` for a parser name.

If the parser name maps to a description with an
identifiable leading token, then that token is shown. Otherwise, the underlying name is shown
without an `@`. The name includes metadata that makes infoview hovers and the like work. This
only works for global constants, as the local context is not included.
-/
private def showParserName (n : Name) : MetaM MessageData := do
  let env ← getEnv
  let params :=
    env.constants.find?' n |>.map (·.levelParams.map Level.param) |>.getD []
  let tok ←
    if let some descr := env.find? n |>.bind (·.value?) then
      if let some tk ← getFirstTk descr then
        pure <| Std.Format.text tk.trim
      else pure <| format n
    else pure <| format n
  pure <| .ofFormatWithInfos {
    fmt := "'" ++ .tag 0 tok ++ "'",
    infos :=
      .ofList [(0, .ofTermInfo {
        lctx := .empty,
        expr := .const n params,
        stx := .ident .none (toString n).toSubstring n [.decl n []],
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

  let showDocs : Option String → MessageData
    | none => .nil
    | some d => Format.line ++ MessageData.joinSep ((d.splitOn "\n").map toMessageData) Format.line

  let showTactics (tag : Name) : MetaM MessageData := do
    match mapping.find? tag with
    | none => pure .nil
    | some tacs =>
      if tacs.isEmpty then pure .nil
      else
        let tacs := tacs.toArray.qsort (·.toString < ·.toString) |>.toList
        pure (Format.line ++ MessageData.joinSep (← tacs.mapM showParserName) ", ")

  let tagDescrs ← liftTermElabM <| (← allTagsWithInfo).mapM fun (name, userName, docs) => do
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

def allTacticDocs : MetaM (Array TacticDoc) := do
  let env ← getEnv
  let all :=
    tacticTagExt.toEnvExtension.getState (← getEnv)
      |>.importedEntries |>.push (tacticTagExt.exportEntriesFn (← getEnv) (tacticTagExt.getState (← getEnv)) .exported)
  let mut tacTags : NameMap NameSet := {}
  for arr in all do
    for (tac, tag) in arr do
      tacTags := tacTags.insert tac (tacTags.getD tac {} |>.insert tag)

  let mut docs := #[]

  let some tactics := (Lean.Parser.parserExtension.getState env).categories.find? `tactic
    | return #[]
  for (tac, _) in tactics.kinds do
    -- Skip noncanonical tactics
    if let some _ := alternativeOfTactic env tac then continue
    let userName : String ←
      if let some descr := env.find? tac |>.bind (·.value?) then
        if let some tk ← getFirstTk descr then
          pure tk.trim
        else pure tac.toString
      else pure tac.toString

    docs := docs.push {
      internalName := tac,
      userName := userName,
      tags := tacTags.getD tac {},
      docString := ← findDocString? env tac,
      extensionDocs := getTacticExtensions env tac
    }
  return docs
