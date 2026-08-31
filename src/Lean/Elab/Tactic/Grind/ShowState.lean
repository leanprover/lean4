/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Elab.Tactic.Grind.Filter
import Lean.Meta.Tactic.Grind.PP
import Lean.Meta.Tactic.Grind.EMatchTheoremParam
import Lean.Meta.Tactic.Grind.Split
namespace Lean.Elab.Tactic.Grind
open Meta
open Meta.Grind

def ppAsserted? (filter : Filter) (collapsed := false) : GrindTacticM (Option MessageData) := do
    let facts ← liftGoalM do (← get).facts.toArray.filterM fun e => filter.eval e
    if facts.isEmpty then
      return none
    return some <| Grind.ppExprArray `facts "Asserted facts" facts (collapsed := collapsed)

@[builtin_grind_tactic showAsserted] def evalShowAsserted : GrindTactic := fun stx => withMainContext do
  let `(grind| show_asserted $[$filter?]?) := stx | throwUnsupportedSyntax
  let filter ← elabFilter filter?
  let some msg ← ppAsserted? filter | throwError "no facts"
  logInfo msg

def ppProps? (filter : Filter) (isTrue : Bool) (collapsed := false) : GrindTacticM (Option MessageData) := do
  let props ← liftGoalM do
    let eqc ← getEqc (← if isTrue then getTrueExpr else getFalseExpr)
    eqc.toArray.filterM fun e => return (← filter.eval e) && !e.isTrue && !e.isFalse
  if props.isEmpty then
    return none
  return some <| Grind.ppExprArray `props s!"{if isTrue then "True" else "False"} propositions" props (collapsed := collapsed)

def showProps (filter? : Option (TSyntax `grind_filter)) (isTrue : Bool) : GrindTacticM Unit := withMainContext do
  let filter ← elabFilter filter?
  let some msg ← ppProps? filter isTrue
    | throwError s!"no {if isTrue then "true" else "false"} propositions"
  logInfo msg

@[builtin_grind_tactic showTrue] def evalShowTrue : GrindTactic := fun stx => do
  let `(grind| show_true $[$filter?]?) := stx | throwUnsupportedSyntax
  showProps filter? true

@[builtin_grind_tactic showFalse] def evalShowFalse : GrindTactic := fun stx => do
  let `(grind| show_false $[$filter?]?) := stx | throwUnsupportedSyntax
  showProps filter? false

def ppEqcs? (filter : Filter) (collapsed := false) : GrindTacticM (Option MessageData) := liftGoalM do
  let mut regularEqcs : Array MessageData := #[]
  let mut otherEqcs   : Array MessageData := #[]
  let goal ← get
  for eqc in goal.getEqcs (sort := true) do
    if Option.isSome <| eqc.find? (·.isTrue) then
      pure ()
    else if Option.isSome <| eqc.find? (·.isFalse) then
      pure ()
    else if let e :: _ :: _ := eqc then
      -- We may want to add a flag to pretty print equivalence classes of nested proofs
      unless (← isProof e) do
      /-
      **Note**: If one element of the equivalence class satisfies the filter, we consider
      the whole equivalence class to be relevant. Reason: you can view an equivalence
      class `{a, b, c}` as a bunch of equations. Thus, if only `b` satisfies the filter,
      then "morally" the equations `b = a` and `b = c` would also satisfy it.
      -/
      if (← eqc.anyM fun e => filter.eval e) then
        let mainEqc ← eqc.filterM fun e => return !(← isSupportApp e)
        if mainEqc.length <= 1 then
          otherEqcs := otherEqcs.push <| ppEqc eqc
        else
          let supportEqc ← eqc.filterM fun e => isSupportApp e
          if supportEqc.isEmpty then
            regularEqcs := regularEqcs.push <| ppEqc mainEqc
          else
            regularEqcs := regularEqcs.push <| ppEqc mainEqc #[ppEqc supportEqc]
  unless otherEqcs.isEmpty do
    regularEqcs := regularEqcs.push <| .trace { cls := `eqc } "others" otherEqcs
  if regularEqcs.isEmpty then
    return none
  else
    return MessageData.trace { cls := `eqc, collapsed } "Equivalence classes" regularEqcs

@[builtin_grind_tactic showEqcs] def evalShowEqcs : GrindTactic := fun stx => withMainContext do
  let `(grind| show_eqcs $[$filter?]?) := stx | throwUnsupportedSyntax
  let filter ← elabFilter filter?
  let some msg ← ppEqcs? filter | throwError "no equivalence classes"
  logInfo msg

def pushIfSome (msgs : Array MessageData) (msg? : Option MessageData) : Array MessageData :=
  if let some msg := msg? then msgs.push msg else msgs

public def showState (filter : Filter) (isSilent := false) : GrindTacticM Unit := do
  let msgs := #[]
  let msgs := pushIfSome msgs (← ppAsserted? filter (collapsed := true))
  let msgs := pushIfSome msgs (← ppProps? filter true (collapsed := false))
  let msgs := pushIfSome msgs (← ppProps? filter false (collapsed := false))
  let msgs := pushIfSome msgs (← ppEqcs? filter (collapsed := false))
  logAt (← getRef) (severity := .information) (isSilent := isSilent) <| MessageData.trace { cls := `grind, collapsed := false } "Grind state" msgs

@[builtin_grind_tactic Parser.Tactic.Grind.showState] def evalShowState : GrindTactic := fun stx => withMainContext do
  let `(grind| show_state $[$filter?]?) := stx | throwUnsupportedSyntax
  let filter ← elabFilter filter?
  showState filter

@[builtin_grind_tactic showCases] def evalShowCases : GrindTactic := fun stx => withMainContext do
  let `(grind| show_cases $[$filter?]?) := stx | throwUnsupportedSyntax
  let filter ← elabFilter filter?
  let { candidates, numDigits } ← liftGoalM <| getSplitCandidateAnchors filter.eval
  if candidates.isEmpty then
    throwError "no case splits"
  let msgs := candidates.map fun { anchor,  e, .. } =>
    .trace { cls := `split } m!"#{anchorToString numDigits anchor} := {e}" #[]
  let msg := MessageData.trace { cls := `splits, collapsed := false } "Case split candidates" msgs
  logInfo msg

@[builtin_grind_tactic showLocalThms] def evalShowLocalThms : GrindTactic := fun _ => withMainContext do
  let goal ← getMainGoal
  let entries ← liftGrindM <| getLocalTheoremAnchors goal
  let numDigits := getNumDigitsForAnchors entries
  let msgs := entries.map fun { anchor, e } =>
    .trace { cls := `thm } m!"#{anchorToString numDigits anchor} := {e}" #[]
  let msg := MessageData.trace { cls := `thms, collapsed := false } "Local theorems" msgs
  logInfo msg

@[builtin_grind_tactic showTerm] def evalShowTerm : GrindTactic := fun stx => do
  let `(grind| show_term $seq:grindSeq) := stx | throwUnsupportedSyntax
  let mvarId := (← getMainGoal).mvarId
  evalGrindTactic seq
  mvarId.withContext do logInfo (← instantiateMVars (mkMVar mvarId))

end Lean.Elab.Tactic.Grind
