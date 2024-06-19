/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
prelude
import Lean.Elab.Command
import Lean.Parser.Tactic.Doc

namespace Lean.Elab.Tactic.Doc
open Lean.Parser.Tactic.Doc

open Lean Elab Command in
elab_rules : command
  | `(tactic_extension $_) => throwError "Missing documentation comment"
  | `($doc:docComment tactic_extension $tac) => do
    let tacName ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo tac
    if let some tgt' := aliasOfTactic (← getEnv) tacName then
        throwError "'{tacName}' is an alias of '{tgt'}'"
    modifyEnv (tacticDocExtExt.addEntry · (tacName, doc.getDocString))

elab_rules : command
  | `($[$doc:docComment]? register_tactic_tag $tag $user) => do
    let docstring ← doc.mapM getDocStringText
    modifyEnv (knownTacticTagExt.addEntry · (tag.getId, user.getString, docstring))


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

open Lean Elab Command in
/--
Displays all available tactic tags, with documentation.
-/
elab withPosition("#print" colGt &"tactic" colGt &"tags") : command => do
  let all :=
    tacticTagExt.toEnvExtension.getState (← getEnv)
      |>.importedEntries |>.push (tacticTagExt.getState (← getEnv))
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
