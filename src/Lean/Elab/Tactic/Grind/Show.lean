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

@[builtin_grind_tactic showAsserted] def evalShowAsserted : GrindTactic := fun stx => withMainContext do
  match stx with
  | `(grind| show_asserted $[$filter?]?) =>
    let filter ← elabFilter filter?
    let facts ← liftGoalM do (← get).facts.toArray.filterM fun e => filter.eval e
    if facts.isEmpty then
      throwError "no facts"
    logInfo <| Grind.ppExprArray `facts "Asserted facts" facts (collapsed := false)
  | _ => throwUnsupportedSyntax

def showProps (filter? : Option (TSyntax `show_filter)) (isTrue : Bool) : GrindTacticM Unit := withMainContext do
  let filter ← elabFilter filter?
  let props ← liftGoalM do
    let eqc ← getEqc (← if isTrue then getTrueExpr else getFalseExpr)
    eqc.toArray.filterM fun e => return (← filter.eval e) && !e.isTrue && !e.isFalse
  if props.isEmpty then
    throwError s!"no {if isTrue then "true" else "false"} propositions"
  logInfo <| Grind.ppExprArray `props s!"{if isTrue then "True" else "False"} propositions" props (collapsed := false)

@[builtin_grind_tactic showTrue] def evalShowTrue : GrindTactic := fun stx => do
  match stx with
  | `(grind| show_true $[$filter?]?) => showProps filter? true
  | _ => throwUnsupportedSyntax

@[builtin_grind_tactic showFalse] def evalShowFalse : GrindTactic := fun stx => do
  match stx with
  | `(grind| show_false $[$filter?]?) => showProps filter? false
  | _ => throwUnsupportedSyntax

@[builtin_grind_tactic showEqcs] def evalShowEqcs : GrindTactic := fun stx => withMainContext do
  match stx with
  | `(grind| show_eqcs $[$filter?]?) =>
    let filter ← elabFilter filter?
    let info ← liftGoalM do
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
            let eqc ← eqc.filterM fun e => filter.eval e
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
        throwError "no equivalence classes"
      return MessageData.trace { cls := `eqc, collapsed := false } "Equivalence classes" regularEqcs
    logInfo info
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Grind
