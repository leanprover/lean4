/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
prelude
import Lean.Elab.Tactic.Do.ProofMode.MGoal

namespace Lean.Elab.Tactic.Do.ProofMode
open Std.Do
open Lean Expr Meta PrettyPrinter Delaborator SubExpr

syntax mgoalHyp := ident " : " term

syntax mgoalStx := ppDedent(ppLine mgoalHyp)* ppDedent(ppLine "⊢ₛ " term)

@[app_delab MGoalEntails]
partial def delabMGoal : Delab := do
  let expr ← instantiateMVars <| ← getExpr

  -- extract environment
  let some goal := parseMGoal? expr | failure

  -- delaborate
  let (_, hyps) ← withAppFn ∘ withAppArg <| delabHypotheses goal.σs ({}, #[])
  let target ← SPred.Notation.unpack (← withAppArg <| delab)

  -- build syntax
  return ⟨← `(mgoalStx| $hyps.reverse* ⊢ₛ $target:term)⟩
where
  delabHypotheses (σs : Expr)
      (acc : NameMap Nat × Array (TSyntax ``mgoalHyp)) :
      DelabM (NameMap Nat × Array (TSyntax ``mgoalHyp)) := do
    let hyps ← getExpr
    if let some _ := parseEmptyHyp? hyps then
      return acc
    if let some hyp := parseHyp? hyps then
      let mut (map, lines) := acc
      let (idx, name') :=
        if let some idx := map.find? hyp.name then
          (idx + 1, hyp.name.appendAfter <| if idx == 0 then "✝" else "✝" ++ idx.toSuperscriptString)
        else
          (0, hyp.name)
      let name' := mkIdent name'
      let stx ← `(mgoalHyp| $name' : $(← SPred.Notation.unpack (← withMDataExpr <| delab)))
      return (map.insert hyp.name idx, lines.push stx)
    if (parseAnd? hyps).isSome then
      let acc_rhs ← withAppArg <| delabHypotheses σs acc
      let acc_lhs ← withAppFn ∘ withAppArg <| delabHypotheses σs acc_rhs
      return acc_lhs
    else
      failure

@[app_delab HypMarker]
def delabHypMarker : Delab := do SPred.Notation.unpack (← withAppArg delab)
