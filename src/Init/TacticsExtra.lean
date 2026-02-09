/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

prelude
public meta import Init.Meta
public import Init.Tactics
import Init.Data.Array.Basic

public section

/-!
Extra tactics and implementation for some tactics defined at `Init/Tactic.lean`
-/
namespace Lean.Parser.Tactic

private meta def expandIfThenElse
    (ifTk thenTk elseTk pos neg : Syntax)
    (mkIf : Term → Term → MacroM Term) : MacroM (TSyntax `tactic) := do
  let mkCase tk holeOrTacticSeq mkName : MacroM (Term × Array (TSyntax `tactic)) := do
    if holeOrTacticSeq.isOfKind `Lean.Parser.Term.syntheticHole then
      pure (⟨holeOrTacticSeq⟩, #[])
    else if holeOrTacticSeq.isOfKind `Lean.Parser.Term.hole then
      pure (← mkName, #[])
    else if tk.isMissing then
      pure (← `(sorry), #[])
    else
      let hole ← withFreshMacroScope mkName
      let holeId : Ident := ⟨hole.raw[1]⟩
      let tacticSeq : TSyntax `Lean.Parser.Tactic.tacticSeq := ⟨holeOrTacticSeq⟩
      -- Use `missing` for ref to ensure that the source range is the same as `holeOrTacticSeq`'s.
      let tacticSeq : TSyntax `Lean.Parser.Tactic.tacticSeq ← MonadRef.withRef .missing `(tacticSeq|
        with_annotate_state $tk skip
        ($tacticSeq))
      let case ← withRef tk <| `(tactic| case $holeId:ident =>%$tk $tacticSeq:tacticSeq)
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
syntax "rw_mod_cast" optConfig rwRuleSeq (location)? : tactic
macro_rules
  | `(tactic| rw_mod_cast $cfg:optConfig [$rules,*] $[$loc]?) => do
    let tacs ← rules.getElems.mapM fun rule =>
      `(tactic| (norm_cast at *; rw $cfg [$rule] $[$loc]?))
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
