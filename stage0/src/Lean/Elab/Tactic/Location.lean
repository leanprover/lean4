/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.ElabTerm

namespace Lean.Elab.Tactic

inductive Location where
  | wildcard
  | targets (hypotheses : Array Syntax) (type : Bool)

/-
Recall that
```
syntax locationWildcard := "*"
syntax locationHyp      := (colGt term:max)+ ("⊢" <|> "|-")?
syntax location         := withPosition("at " locationWildcard <|> locationHyp)
```
-/
def expandLocation (stx : Syntax) : Location :=
  let arg := stx[1]
  if arg.getKind == ``Parser.Tactic.locationWildcard then
    Location.wildcard
  else
    Location.targets arg[0].getArgs (!arg[1].isNone)

def expandOptLocation (stx : Syntax) : Location :=
  if stx.isNone then
    Location.targets #[] true
  else
    expandLocation stx[0]

open Meta

def withLocation (loc : Location) (atLocal : FVarId → TacticM Unit) (atTarget : TacticM Unit) (failed : MVarId → TacticM Unit) : TacticM Unit := do
  match loc with
  | Location.targets hyps type =>
    hyps.forM fun hyp => withMainContext do
      let fvarId ← getFVarId hyp
      atLocal fvarId
    if type then
      atTarget
  | Location.wildcard =>
    let worked ← tryTactic <| withMainContext <| atTarget
    withMainContext do
      let mut worked := worked
      -- We must traverse backwards because the given `atLocal` may use the revert/intro idiom
      for fvarId in (← getLCtx).getFVarIds.reverse do
        worked := worked || (← tryTactic <| withMainContext <| atLocal fvarId)
      unless worked do
        failed (← getMainGoal)

end Lean.Elab.Tactic
