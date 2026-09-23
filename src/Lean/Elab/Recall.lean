/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Kyle Miller
-/
module

prelude
public import Lean.Elab.Command
public import Lean.Elab.DeclUtil
public import Lean.Meta.Tactic.TryThis
public import Lean.PrettyPrinter.Delaborator

/-!
# `recall` command
-/

public section

namespace Lean.Elab.Recall

open Lean Meta Elab Command Term

/-- Format a `recall` suggestion string for the given constant name. -/
private def mkRecallSuggestion (declName : Name) : MetaM String := do
  let decl ← getConstInfo declName
  let e := Expr.const declName (decl.levelParams.map Level.param)
  let (stx, _) ← PrettyPrinter.delabCore e
    (delab := PrettyPrinter.Delaborator.delabConstWithSignature (universes := false))
  let sig := toString (← PrettyPrinter.ppTerm ⟨stx⟩)
  return s!"recall {sig}"

@[builtin_command_elab Lean.Parser.Command.recallQuestionCmd]
def elabRecall? : CommandElab
  | `(Parser.Command.recallQuestionCmd| recall?%$tk $id:ident) => withoutModifyingEnv do
    let declName := id.getId
    addConstInfo id declName
    let _ ← getConstInfo declName
    let suggestion ← liftTermElabM <| mkRecallSuggestion declName
    liftTermElabM <|
      Tactic.TryThis.addSuggestion tk (suggestion : String) (origSpan? := ← getRef)
  | _ => throwUnsupportedSyntax

@[builtin_command_elab Lean.Parser.Command.recallCmd]
def elabRecall : CommandElab
  | `(Parser.Command.recallCmd|
      $[$_doc?:docComment]? recall $id:ident $sig:optDeclSig $[$val?:declVal]?) =>
    -- `recall` doesn't introduce new definitions, so suppress the unused variable linter.
    withScope (fun sc => { sc with opts := sc.opts.set `linter.unusedVariables false }) <|
    withoutModifyingEnv do
    let declName ← resolveGlobalConstNoOverload id
    addConstInfo id declName
    let info ← getConstInfo declName
    let declConst : Expr := mkConst declName <| info.levelParams.map Level.param
    let stxRef ← getRef
    let recallName := Name.mkSimple
      s!"_recall_{(← liftTermElabM Lean.mkFreshId)}"
    let newId := mkIdentFrom id recallName
    if let some val := val? then
      let some infoVal := info.value? (allowOpaque := true)
        | throwErrorAt val "constant '{declName}' has no defined value"
      withScope (fun sc => { sc with opts := Elab.async.set sc.opts false }) do
        elabCommand <| ← `(noncomputable def $newId $sig:optDeclSig $val)
      let newName ← resolveGlobalConstNoOverload newId
      let newInfo ← getConstInfo newName
      liftTermElabM do
        let mvs ← newInfo.levelParams.mapM fun _ => mkFreshLevelMVar
        let newType := newInfo.type.instantiateLevelParams newInfo.levelParams mvs
        unless ← isDefEq info.type newType do
          let suggestion ← mkRecallSuggestion declName
          Tactic.TryThis.addSuggestion stxRef (suggestion : String) (origSpan? := stxRef)
          throwTypeMismatchError none info.type newInfo.type declConst
        let newVal := newInfo.value?.get!.instantiateLevelParams newInfo.levelParams mvs
        unless ← isDefEq infoVal newVal do
          let err := m!"\
            value mismatch{indentExpr declConst}\nhas value{indentExpr newVal}\n\
            but is expected to have value{indentExpr infoVal}"
          throwErrorAt val err
    else
      let (binders, type?) := expandOptDeclSig sig
      if let some type := type? then
        runTermElabM fun vars => do
          withAutoBoundImplicit do
            elabBinders binders.getArgs fun xs => do
              let xs ← addAutoBoundImplicits xs none
              let type ← elabType type
              Term.synthesizeSyntheticMVarsNoPostponing
              let type ← mkForallFVars xs type
              let type ← mkForallFVars vars type (usedOnly := true)
              let infoType ← do
                let mvs ← info.levelParams.mapM fun _ => mkFreshLevelMVar
                pure <| info.type.instantiateLevelParams info.levelParams mvs
              unless ← isDefEq infoType type do
                let suggestion ← mkRecallSuggestion declName
                Tactic.TryThis.addSuggestion stxRef (suggestion : String) (origSpan? := stxRef)
                throwTypeMismatchError none info.type type declConst
      else
        unless binders.getNumArgs == 0 do
          throwError "expected type after ':'"
  | _ => throwUnsupportedSyntax

end Lean.Elab.Recall
