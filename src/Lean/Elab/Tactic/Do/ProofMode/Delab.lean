/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
prelude
import Lean.Elab.Tactic.Do.ProofMode.MGoal
import Lean.PrettyPrinter.Delaborator.Basic

namespace Lean.Elab.Tactic.Do.ProofMode
open Std.Do
open Std.Tactic.Do
open Lean Expr Meta PrettyPrinter Delaborator SubExpr

@[builtin_delab app.Std.Tactic.Do.MGoalEntails]
private partial def delabMGoal : Delab := do
  -- delaborate
  let (_, hyps) ← withAppFn ∘ withAppArg <| delabHypotheses ({}, #[])
  let target ← SPred.Notation.unpack (← withAppArg <| delab)

  -- build syntax
  return ⟨← `(Std.Tactic.Do.mgoalStx| $hyps.reverse* ⊢ₛ $target:term)⟩
where
  delabHypotheses
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
      let stx ← `(Std.Tactic.Do.mgoalHyp| $name' : $(← SPred.Notation.unpack (← withMDataExpr <| delab)))
      return (map.insert hyp.name idx, lines.push stx)
    if (parseAnd? hyps).isSome then
      let acc_rhs ← withAppArg <| delabHypotheses acc
      let acc_lhs ← withAppFn ∘ withAppArg <| delabHypotheses acc_rhs
      return acc_lhs
    else
      failure

@[builtin_delab app.Std.Tactic.Do.MGoalHypMarker]
private def delabHypMarker : Delab := do SPred.Notation.unpack (← withAppArg delab)
