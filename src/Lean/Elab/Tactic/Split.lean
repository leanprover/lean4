/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Hint
import Lean.Meta.Tactic.Split
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Location

namespace Lean.Elab.Tactic
open Meta

@[builtin_tactic Lean.Parser.Tactic.split] def evalSplit : Tactic := fun stx => do
  let traceHint : MessageData := .ofLazyM do
    if ! (← getBoolOption `trace.split.failure) then
      return .hint' m!"Use `set_option trace.split.failure true` to display additional diagnostic information."
    else return .nil
  if let `(tactic|split $t:term $[at $loc]?) := stx then
    withMainContext do
      let mut error := m!"Tactic `split` failed: Specifying a term to split is not supported yet"
      if t.raw.isIdent then
        let name := t.raw.getId
        let lctx ← getLCtx
        if name.isStr && loc.isNone then
          if let some decl := lctx.findFromUserName? name then
            let e := decl.toExpr
            let tgtHint ← MessageData.hint
              m!"If you intended to apply `split` at the hypothesis `{e}`, use `split at {e}`:"
              #[{ suggestion := (← `(tactic|split at $(mkIdent name):ident)) }]
            error := error ++ tgtHint
      throwErrorAt stx error
  let loc := expandOptLocation stx[2]
  match loc with
  | Location.targets hyps simplifyTarget =>
    if (hyps.size > 0 && simplifyTarget) || hyps.size > 1 then
      let goalStr := if simplifyTarget then "the goal and " else ""
      let hypsStr :=
        (if hyps.size == 1 then m!"hypothesis" else m!"hypotheses") ++
        MessageData.andList (hyps.toList.map (m!"`{·}`"))
      let hint := .hint' m!"Specify a single target to split, or use `split at *` to split the first target that can be automatically split"
      throwErrorAt stx[2] m!"Tactic `split` failed: Specifying multiple targets ({goalStr ++ hypsStr}) is not supported" ++ hint
    if simplifyTarget then
      liftMetaTactic fun mvarId => do
       let some mvarIds ← splitTarget? mvarId
        | Meta.throwTacticEx `split mvarId <| m!"Could not split an `if` or `match` expression in the goal" ++ traceHint
        return mvarIds
    else
      let fvarId ← getFVarId hyps[0]!
      liftMetaTactic fun mvarId => do
        let some mvarIds ← splitLocalDecl? mvarId fvarId
          | Meta.throwTacticEx `split mvarId <| m!"Could not split an `if` or `match` expression in the type of `{Expr.fvar fvarId}`" ++ traceHint
        return mvarIds
  | Location.wildcard =>
    liftMetaTactic fun mvarId => do
      let fvarIds ← mvarId.getNondepPropHyps
      for fvarId in fvarIds do
        if let some mvarIds ← splitLocalDecl? mvarId fvarId then
          return mvarIds
      let some mvarIds ← splitTarget? mvarId
        | let splitAtNoteText := "It may still be possible to manually split a hypothesis using `split at`"
          if fvarIds.size > 0 then
            let fvarMsgs := fvarIds.toList.map (m!"`{Expr.fvar ·}`")
            let fvarMsgs := MessageData.joinSep fvarMsgs ", "
            let splitAtNoteText := s!"`split at *` does not attempt to split at non-propositional hypotheses or those on which other hypotheses depend. {splitAtNoteText}."
            Meta.throwTacticEx `split mvarId <|
              m!"Could not split the goal or any of the following hypotheses: {fvarMsgs}." ++ .note splitAtNoteText ++ traceHint
          else
            Meta.throwTacticEx `split mvarId <|
              m!"Could not split the goal, and no hypotheses that could be automatically split were found." ++ splitAtNoteText ++ traceHint

      return mvarIds

end Lean.Elab.Tactic
