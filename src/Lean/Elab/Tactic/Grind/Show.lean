/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Elab.Tactic.Grind.Basic
import Init.Grind.Interactive
import Lean.Meta.Tactic.Grind.PP
import Lean.Meta.Tactic.Grind.Anchor
namespace Lean.Elab.Tactic.Grind
open Meta

inductive Filter where
  | true
  | const (declName : Name)
  | fvar (fvarId : FVarId)
  | gen (pred : Nat → Bool)
  | or (a b : Filter)
  | and (a b : Filter)
  | not (a : Filter)

partial def elabFilter (filter? : Option (TSyntax `show_filter)) : GrindTacticM Filter := do
  let some filter := filter? | return .true
  go filter
where
  go (filter : TSyntax `show_filter) : GrindTacticM Filter := do
    match filter with
    | `(show_filter| $id:ident) =>
      match (← Term.resolveId? id) with
      | some (.const declName _) => return .const declName
      | some (.fvar fvarId) => return .fvar fvarId
      | _ => throwErrorAt id "invalid identifier"
    | `(show_filter| $a:show_filter && $b:show_filter) => return .and (← go a) (← go b)
    | `(show_filter| $a:show_filter || $b:show_filter) => return .or (← go a) (← go b)
    | `(show_filter| ! $a:show_filter) => return .not (← go a)
    | `(show_filter| ($a:show_filter)) => go a
    | `(show_filter| gen = $n:num)  => let n := n.getNat; return .gen fun x => x == n
    | `(show_filter| gen > $n:num)  => let n := n.getNat; return .gen fun x => x > n
    | `(show_filter| gen ≥ $n:num)  => let n := n.getNat; return .gen fun x => x ≥ n
    | `(show_filter| gen >= $n:num) => let n := n.getNat; return .gen fun x => x ≥ n
    | `(show_filter| gen ≤ $n:num)  => let n := n.getNat; return .gen fun x => x ≤ n
    | `(show_filter| gen <= $n:num) => let n := n.getNat; return .gen fun x => x ≤ n
    | `(show_filter| gen < $n:num)  => let n := n.getNat; return .gen fun x => x < n
    | `(show_filter| gen != $n:num) => let n := n.getNat; return .gen fun x => x != n
    | _ => throwUnsupportedSyntax

open Meta.Grind

-- **Note**: facts may not have been internalized if they are equalities.
def getGen (e : Expr) : GoalM Nat := do
  if (← alreadyInternalized e) then
    getGeneration e
  else match_expr e with
   | Eq _ lhs rhs => return max (← getGeneration lhs) (← getGeneration rhs)
   | _ => return 0

def Filter.eval (filter : Filter) (e : Expr) : GoalM Bool := do
  go filter
where
  go (filter : Filter) : GoalM Bool := do
  match filter with
  | .true => return .true
  | .and a b => go a <&&> go b
  | .or a b => go a <||> go b
  | .not a => return !(← go a)
  | .const declName => return Option.isSome <| e.find? fun e => e.isConstOf declName
  | .fvar fvarId => return Option.isSome <| e.find? fun e => e.isFVar && e.fvarId! == fvarId
  | .gen pred => let gen ← getGen e; return pred gen

def ppAsserted? (filter : Filter) (collapsed := false) : GrindTacticM (Option MessageData) := do
    let facts ← liftGoalM do (← get).facts.toArray.filterM fun e => filter.eval e
    if facts.isEmpty then
      return none
    return some <| Grind.ppExprArray `facts "Asserted facts" facts (collapsed := collapsed)

@[builtin_grind_tactic showAsserted] def evalShowAsserted : GrindTactic := fun stx => withMainContext do
  match stx with
  | `(grind| show_asserted $[$filter?]?) =>
    let filter ← elabFilter filter?
    let some msg ← ppAsserted? filter | throwError "no facts"
    logInfo msg
  | _ => throwUnsupportedSyntax

def ppProps? (filter : Filter) (isTrue : Bool) (collapsed := false) : GrindTacticM (Option MessageData) := do
  let props ← liftGoalM do
    let eqc ← getEqc (← if isTrue then getTrueExpr else getFalseExpr)
    eqc.toArray.filterM fun e => return (← filter.eval e) && !e.isTrue && !e.isFalse
  if props.isEmpty then
    return none
  return some <| Grind.ppExprArray `props s!"{if isTrue then "True" else "False"} propositions" props (collapsed := collapsed)

def showProps (filter? : Option (TSyntax `show_filter)) (isTrue : Bool) : GrindTacticM Unit := withMainContext do
  let filter ← elabFilter filter?
  let some msg ← ppProps? filter isTrue
    | throwError s!"no {if isTrue then "true" else "false"} propositions"
  logInfo msg

@[builtin_grind_tactic showTrue] def evalShowTrue : GrindTactic := fun stx => do
  match stx with
  | `(grind| show_true $[$filter?]?) => showProps filter? true
  | _ => throwUnsupportedSyntax

@[builtin_grind_tactic showFalse] def evalShowFalse : GrindTactic := fun stx => do
  match stx with
  | `(grind| show_false $[$filter?]?) => showProps filter? false
  | _ => throwUnsupportedSyntax

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
  match stx with
  | `(grind| show_eqcs $[$filter?]?) =>
    let filter ← elabFilter filter?
    let some msg ← ppEqcs? filter | throwError "no equivalence classes"
    logInfo msg
  | _ => throwUnsupportedSyntax

def pushIfSome (msgs : Array MessageData) (msg? : Option MessageData) : Array MessageData :=
  if let some msg := msg? then msgs.push msg else msgs

@[builtin_grind_tactic showState] def evalShowState : GrindTactic := fun stx => withMainContext do
  match stx with
  | `(grind| show_state $[$filter?]?) =>
    let filter ← elabFilter filter?
    let msgs := #[]
    let msgs := pushIfSome msgs (← ppAsserted? filter (collapsed := true))
    let msgs := pushIfSome msgs (← ppProps? filter true (collapsed := true))
    let msgs := pushIfSome msgs (← ppProps? filter false (collapsed := true))
    let msgs := pushIfSome msgs (← ppEqcs? filter (collapsed := true))
    logInfo <| MessageData.trace { cls := `grind, collapsed := false } "Grind state" msgs
  | _ => throwUnsupportedSyntax

def truncateAnchors (es : Array (Expr × UInt64)) : Array (Expr × UInt64) × Nat :=
  go 4
where
  go (numDigits : Nat) : Array (Expr × UInt64) × Nat := Id.run do
    if 4*numDigits  < 64 then
      let shift := 64 - 4*numDigits
      let mut found : Std.HashSet UInt64 := {}
      let mut result := #[]
      for (e, a) in es do
        let a' := a >>> shift.toUInt64
        if found.contains a' then
          return (← go (numDigits+1))
        else
          found  := found.insert a'
          result := result.push (e, a')
      return (result, numDigits)
    else
      return (es, numDigits)
  termination_by 64 - 4*numDigits

def anchorToString (numDigits : Nat) (anchor : UInt64) : String :=
  let cs := Nat.toDigits 16 anchor.toNat
  let n := cs.length
  let zs := List.replicate (numDigits - n) '0'
  let cs := zs ++ cs
  cs.asString

@[builtin_grind_tactic showSplits] def evalShowSplits : GrindTactic := fun stx => withMainContext do
  match stx with
  | `(grind| show_splits $[$filter?]?) =>
    let filter ← elabFilter filter?
    let goal ← getMainGoal
    let candidates := goal.split.candidates
    let candidates ← liftGrindM <| candidates.toArray.mapM fun c => do
      let e := c.getExpr
      let anchor ← getAnchor e
      return (e, anchor)
    let (candidates, numDigits) := truncateAnchors candidates
    let candidates ← liftGoalM <| candidates.filterM fun (e, _) => filter.eval e
    if candidates.isEmpty then
      throwError "no case splits"
    let msgs := candidates.map fun (e, a) =>
      .trace { cls := `split } m!"#{anchorToString numDigits a} := {e}" #[]
    let msg := MessageData.trace { cls := `splits, collapsed := false } "Case split candidates" msgs
    logInfo msg
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Grind
