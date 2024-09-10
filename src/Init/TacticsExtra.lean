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
  `(tactic| ((open Classical in refine%$ifTk $(← mkIf posHole negHole)); $[$(posCase ++ negCase)]*))

macro_rules
  | `(tactic| if%$tk $h : $c then%$ttk $pos else%$etk $neg) =>
    -- Limit ref variability for incrementality; see Note [Incremental Macros]
    withRef tk do
      expandIfThenElse tk ttk etk pos neg fun pos neg => `(if $h : $c then $pos else $neg)

macro_rules
  | `(tactic| if%$tk $c then%$ttk $pos else%$etk $neg) =>
    -- Limit ref variability for incrementality; see Note [Incremental Macros]
    withRef tk do
      expandIfThenElse tk ttk etk pos neg fun pos neg => `(if h : $c then $pos else $neg)

/--
`iterate n tac` runs `tac` exactly `n` times.
`iterate tac` runs `tac` repeatedly until failure.

`iterate`'s argument is a tactic sequence,
so multiple tactics can be run using `iterate n (tac₁; tac₂; ⋯)` or
```lean
iterate n
  tac₁
  tac₂
  ⋯
```
-/
syntax "iterate" (ppSpace num)? ppSpace tacticSeq : tactic
macro_rules
  | `(tactic| iterate $seq:tacticSeq) =>
    `(tactic| try ($seq:tacticSeq); iterate $seq:tacticSeq)
  | `(tactic| iterate $n $seq:tacticSeq) =>
    match n.1.toNat with
    | 0 => `(tactic| skip)
    | n+1 => `(tactic| ($seq:tacticSeq); iterate $(quote n) $seq:tacticSeq)

/--
Rewrites with the given rules, normalizing casts prior to each step.
-/
syntax "rw_mod_cast" (config)? rwRuleSeq (location)? : tactic
macro_rules
  | `(tactic| rw_mod_cast $[$config]? [$rules,*] $[$loc]?) => do
    let tacs ← rules.getElems.mapM fun rule =>
      `(tactic| (norm_cast at *; rw $[$config]? [$rule] $[$loc]?))
    `(tactic| ($[$tacs]*))

/--
Normalize casts in the goal and the given expression, then close the goal with `exact`.
-/
macro "exact_mod_cast " e:term : tactic => `(tactic| exact mod_cast ($e : _))

/--
Normalize casts in the goal and the given expression, then `apply` the expression to the goal.
-/
macro "apply_mod_cast " e:term : tactic => `(tactic| apply mod_cast ($e : _))

end Lean.Parser.Tactic
