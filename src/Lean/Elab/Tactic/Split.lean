/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Tactic.Split
public import Lean.Elab.Tactic.Location

public section

namespace Lean.Elab.Tactic
open Meta

@[builtin_tactic Lean.Parser.Tactic.split] def evalSplit : Tactic := fun stx => do
  if let `(tactic|split $t:term $[at $loc]?) := stx then
    throwTermUnsupported t loc
  let loc := expandOptLocation stx[2]
  match loc with
  | Location.targets hyps simplifyTarget =>
    if (hyps.size > 0 && simplifyTarget) || hyps.size > 1 then
      throwMultipleLocationsAt stx[2] simplifyTarget hyps
    if simplifyTarget then
      liftMetaTactic fun mvarId => do
       let some mvarIds ← splitTarget? mvarId | throwCouldNotSplitGoal mvarId
        return mvarIds
    else
      let fvarId ← getFVarId hyps[0]!
      liftMetaTactic fun mvarId => do
        let some mvarIds ← splitLocalDecl? mvarId fvarId | throwCouldNotSplitHyp fvarId mvarId
        return mvarIds
  | Location.wildcard =>
    liftMetaTactic fun mvarId => do
      let fvarIds ← mvarId.getNondepPropHyps
      for fvarId in fvarIds do
        if let some mvarIds ← splitLocalDecl? mvarId fvarId then
          return mvarIds
      let some mvarIds ← splitTarget? mvarId
        | throwCouldNotSplitWildcard fvarIds mvarId
      return mvarIds
where
  traceHint : MessageData := .ofLazyM do
    if ! (← getBoolOption `trace.split.failure) then
      return .hint' m!"Use `set_option trace.split.failure true` to display additional diagnostic information"
    else return .nil

  throwTermUnsupported (t : Term) (loc : Option Syntax) := do
    withMainContext do
      let mut error := m!"Tactic `split` failed: Specifying a term to split is not supported yet"
      if t.raw.isIdent then
        let name := t.raw.getId
        let lctx ← getLCtx
        if name.isStr && loc.isNone then
          if let some decl := lctx.findFromUserName? name then
            let e := decl.toExpr
            let hint ← MessageData.hint
              m!"To apply `split` at the hypothesis `{e}`, use `split at {e}`:"
              #[{ suggestion := (← `(tactic|split at $(mkIdent name):ident)) }]
            error := error ++ hint
      throwErrorAt t error

  throwMultipleLocationsAt (stx : Syntax) (simplifyTarget : Bool) (hyps : Array Syntax) {α} : MetaM α := do
    let goalStr := if simplifyTarget then "the goal and " else ""
    let hypsStr :=
      (if hyps.size == 1 then m!"hypothesis" else m!"hypotheses") ++
      MessageData.andList (hyps.toList.map (m!"`{·}`"))
    throwErrorAt stx m!"Tactic `split` failed: Specifying multiple targets ({goalStr ++ hypsStr}) is not supported"
      ++ .hint' m!"Specify a single target to split, or use `split at *` to split the first target that can be automatically split"

  throwCouldNotSplitGoal (mvarId : MVarId) := do
    Meta.throwTacticEx `split mvarId <| m!"Could not split an `if` or `match` expression in the goal"
      ++ (← mkCasesHint <$> mvarId.getType) ++ traceHint

  throwCouldNotSplitHyp (fvarId : FVarId) (mvarId: MVarId) := do
    let fvarType ← fvarId.getType
    Meta.throwTacticEx `split mvarId <| m!"Could not split an `if` or `match` expression in \
      the type{inlineExpr fvarType}of `{Expr.fvar fvarId}`" ++ mkCasesHint fvarType ++ traceHint

  throwCouldNotSplitWildcard {α} (fvarIds : Array FVarId) (mvarId : MVarId) : MetaM α := do
    let note := .note "`split at *` does not attempt to split at non-propositional hypotheses \
      or those on which other hypotheses depend. It may still be possible to manually split a \
      hypothesis using `split at`"
    if fvarIds.size > 0 then
      let fvarMsgs := fvarIds.toList.map (m!"`{Expr.fvar ·}`")
      let fvarMsgs := MessageData.joinSep fvarMsgs ", "
      Meta.throwTacticEx `split mvarId <|
        m!"Could not split the goal or any of the following hypotheses: {fvarMsgs}" ++ note ++ traceHint
    else
      Meta.throwTacticEx `split mvarId <|
        m!"Could not split the goal, and no hypotheses that could be automatically split were found" ++ note ++ traceHint

  mkCasesHint (type : Expr) : MessageData := MessageData.ofLazyM do
    let isFnStructureConst (t : Expr) : MetaM Bool := do
      if let .const c _ := t.getAppFn then
        let env ← getEnv
        return isStructure env c && (getStructureFields env c).size > 0
      else
        return false
    let kind? ←
      if type.isAppOf ``And then pure <| some "conjunction"
      else if type.isAppOf ``Prod then pure <| some "pair"
      else if (← isFnStructureConst type.getAppFn) then pure <| some "structure"
      else pure <| none
    if let some kind := kind? then
      return .hint' m!"If you meant to destruct this {kind}, use the `cases` tactic instead"
    else
      return .nil

end Lean.Elab.Tactic
