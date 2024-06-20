/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
prelude
import Lean.DocString
import Lean.Elab.Command
import Lean.Parser.Tactic.Doc
import Lean.Parser.Command

namespace Lean.Elab.Tactic.Doc
open Lean.Parser.Tactic.Doc
open Lean.Elab.Command

-- TODO Replace the parsing in this file with proper quotations after a stage0 update

/-- Find out whether the result of a docComment? is present; if so, return it -/
private partial def asDocComment?
    (stx : Syntax) : Option (TSyntax ``Lean.Parser.Command.docComment) :=
  if stx.getKind == ``Lean.Parser.Command.docComment then
    some ⟨stx⟩
  else if let .node _ k #[c] := stx then
    if k == nullKind then asDocComment? c else none
  else none

/-- If syntax is a string literal, return it -/
private def asStrLit? : Syntax → Option StrLit
  | `($s:str) => some s
  | _ => none

@[builtin_command_elab tactic_extension] def elabTacticExtension : CommandElab
  | .node _ _ #[.node _ _ #[], cmd@(.atom _ "tactic_extension"), _] => do
    throwErrorAt cmd "Missing documentation comment"
  | .node _ _ #[.node _ _ #[docComment], cmd@(.atom _ "tactic_extension"), tac] => do
    let some docComment := asDocComment? docComment
      | throwErrorAt cmd "Malformed documentation comment ({docComment})"
    let tacName ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo tac
    if let some tgt' := aliasOfTactic (← getEnv) tacName then
        throwErrorAt tac "'{tacName}' is an alias of '{tgt'}'"
    if !(isTactic (← getEnv) tacName) then throwErrorAt tac "'{tacName}' is not a tactic"

    modifyEnv (tacticDocExtExt.addEntry · (tacName, docComment.getDocString))
    pure ()
  | _ => throwError "Malformed tactic extension command"

@[builtin_command_elab register_tactic_tag] def elabRegisterTacticTag : CommandElab
  | .node _ _ #[doc, .atom _ "register_tactic_tag", tag, user] => do
    let docstring ← (asDocComment? doc).mapM getDocStringText
    let some user := asStrLit? user
      | throwErrorAt user "expected string literal"
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
      .fromList [(0, .ofTermInfo {
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
      |>.importedEntries |>.push (tacticTagExt.exportEntriesFn (tacticTagExt.getState (← getEnv)))
  let mut mapping : NameMap NameSet := {}
  for arr in all do
    for (tac, tag) in arr do
      mapping := mapping.insert tag (mapping.findD tag {} |>.insert tac)

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
      MessageData.nestD (m!"'{name}'" ++
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
      |>.importedEntries |>.push (tacticTagExt.exportEntriesFn (tacticTagExt.getState (← getEnv)))
  let mut tacTags : NameMap NameSet := {}
  for arr in all do
    for (tac, tag) in arr do
      tacTags := tacTags.insert tac (tacTags.findD tac {} |>.insert tag)

  let mut docs := #[]

  let some tactics := (Lean.Parser.parserExtension.getState env).categories.find? `tactic
    | return #[]
  for (tac, _) in tactics.kinds do
    -- Skip noncanonical tactics
    if let some _ := aliasOfTactic env tac then continue
    let userName : String ←
      if let some descr := env.find? tac |>.bind (·.value?) then
        if let some tk ← getFirstTk descr then
          pure tk.trim
        else pure tac.toString
      else pure tac.toString

    docs := docs.push {
      internalName := tac,
      userName := userName,
      tags := tacTags.findD tac {},
      docString := ← findDocString? env tac,
      extensionDocs := getTacticExtensions env tac
    }
  return docs
