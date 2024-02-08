/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
prelude
import Init.Tactics
import Init.NotationExtra

/-!
Extra tactics and implementation for some tactics defined at `Init/Tactic.lean`
-/
namespace Lean.Parser.Tactic

private def expandIfThenElse
    (ifTk thenTk elseTk pos neg : Syntax)
    (mkIf : Term → Term → MacroM Term) : MacroM (TSyntax `tactic) := do
  let mkCase tk holeOrTacticSeq mkName : MacroM (Term × Array (TSyntax `tactic)) := do
    if holeOrTacticSeq.isOfKind `Lean.Parser.Term.syntheticHole then
      pure (⟨holeOrTacticSeq⟩, #[])
    else if holeOrTacticSeq.isOfKind `Lean.Parser.Term.hole then
      pure (← mkName, #[])
    else
      let hole ← withFreshMacroScope mkName
      let holeId := hole.raw[1]
      let case ← (open TSyntax.Compat in `(tactic|
          case $holeId:ident =>%$tk
            -- annotate `then/else` with state after `case`
            with_annotate_state $tk skip
            $holeOrTacticSeq))
      pure (hole, #[case])
  let (posHole, posCase) ← mkCase thenTk pos `(?pos)
  let (negHole, negCase) ← mkCase elseTk neg `(?neg)
  `(tactic| (open Classical in refine%$ifTk $(← mkIf posHole negHole); $[$(posCase ++ negCase)]*))

macro_rules
  | `(tactic| if%$tk $h : $c then%$ttk $pos else%$etk $neg) =>
    expandIfThenElse tk ttk etk pos neg fun pos neg => `(if $h : $c then $pos else $neg)

macro_rules
  | `(tactic| if%$tk $c then%$ttk $pos else%$etk $neg) =>
    expandIfThenElse tk ttk etk pos neg fun pos neg => `(if h : $c then $pos else $neg)

end Lean.Parser.Tactic
