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
    if let some tgt' ← aliasOfTactic tacName then
        throwError "'{tacName}' is an alias of '{tgt'}'"
    modifyEnv (tacticDocExtExt.addEntry · (tacName, doc.getDocString))

elab_rules : command
  | `($[$doc:docComment]? register_tactic_tag $tag $user) => do
    let docstring ← doc.mapM getDocStringText
    modifyEnv (knownTacticTagExt.addEntry · (tag.getId, user.getString, docstring))


-- Create some `MessageData` for a name that shows it without an `@`, but with the metadata that
-- makes infoview hovers and the like work. This technique only works because the names are known
-- to be global constants, so we don't need the local context.
private def showName (env : Environment) (n : Name) : MessageData :=
  let params :=
    env.constants.find?' n |>.map (·.levelParams.map Level.param) |>.getD []
  .ofFormatWithInfos {
    fmt := "'" ++ .tag 0 (format n) ++ "'",
    infos :=
      .fromList [(0, .ofTermInfo {
        lctx := .empty,
        expr := .const n params,
        stx := .ident .none (toString n).toSubstring n [.decl n []],
        elaborator := `Delab,
        expectedType? := none
      })] _
  }

elab "#print" &"tactic" &"tags" : command => do
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

  let env ← getEnv

  let showTactics (tag : Name) : MessageData :=
    match mapping.find? tag with
    | none => .nil
    | some tacs =>
      if tacs.isEmpty then .nil
      else
        let tacs := tacs.toArray.qsort (·.toString < ·.toString) |>.toList
        Format.line ++ MessageData.joinSep (tacs.map (showName env)) ", "

  let tagDescrs := (← allTagsWithInfo).map fun (name, userName, docs) =>
    m!"• " ++
    MessageData.nestD (m!"'{name}'" ++
      (if name.toString != userName then m!" — \"{userName}\"" else MessageData.nil) ++
      showDocs docs ++
      showTactics name)

  let tagList : MessageData := m!"Available tags:" ++ MessageData.nestD (Format.line ++ .joinSep tagDescrs Format.line)

  logInfo tagList
