/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Elab.Tactic.ElabTerm

public section

namespace Lean.Elab.Tactic

/-- Denotes a set of locations where a tactic should be applied for the main goal. See also `withLocation`. -/
inductive Location where
  /-- Apply the tactic everywhere. -/
  | wildcard
  /-- `hypotheses` are hypothesis names in the main goal that the tactic should be applied to.
  If `type` is true, then the tactic should also be applied to the target type. -/
  | targets (hypotheses : Array Syntax) (type : Bool)

/-
Recall that
```
syntax locationWildcard := " *"
syntax locationType     := patternIgnore(atomic("|" noWs "-") <|> "⊢")
syntax locationHyp      := (ppSpace colGt (term:max <|> locationType))+
syntax location         := withPosition(ppGroup(" at" (locationWildcard <|> locationHyp)))
```
-/
def expandLocation (stx : Syntax) : Location :=
  let arg := stx[1]
  if arg.getKind == ``Parser.Tactic.locationWildcard then
    Location.wildcard
  else
    let locationHyps := arg[0].getArgs
    let hypotheses := locationHyps.filter (·.getKind != ``Parser.Tactic.locationType)
    let numTurnstiles := locationHyps.size - hypotheses.size
    Location.targets hypotheses (numTurnstiles > 0)

def expandOptLocation (stx : Syntax) : Location :=
  if stx.isNone then
    Location.targets #[] true
  else
    expandLocation stx[0]

open Meta

/--
Runs the given `atLocal` and `atTarget` methods on each of the locations selected by the given `loc`.
* If `loc` is a list of locations, runs at each specified hypothesis (and finally the goal if `⊢` is included),
  and fails if any of the tactic applications fail.
* If `loc` is `*`, runs at the target first and then the hypotheses in reverse order.
  If `atTarget` closes the main goal, `withLocation` does not run `atLocal`.
  If all tactic applications fail, `withLocation` with call `failed` with the main goal mvar.
-/
def withLocation (loc : Location) (atLocal : FVarId → TacticM Unit) (atTarget : TacticM Unit) (failed : MVarId → TacticM Unit) : TacticM Unit := do
  match loc with
  | Location.targets hyps type =>
    hyps.forM fun hyp => withMainContext do
      let fvarId ← getFVarId hyp
      atLocal fvarId
    if type then
      withMainContext atTarget
  | Location.wildcard =>
    let worked ← tryTactic <| withSaveInfoContext <| withMainContext <| atTarget
    let g ← try getMainGoal catch _ => return () -- atTarget closed the goal
    g.withContext do
      let mut worked := worked
      -- We must traverse backwards because the given `atLocal` may use the revert/intro idiom
      for fvarId in (← getLCtx).getFVarIds.reverse do
        if (← fvarId.getDecl).isImplementationDetail then
          continue
        worked := worked || (← tryTactic <| withSaveInfoContext <| withMainContext <| atLocal fvarId)
      unless worked do
        failed (← getMainGoal)

end Lean.Elab.Tactic
