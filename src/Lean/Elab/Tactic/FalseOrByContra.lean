/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
prelude
import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Intro

/-!
# `false_or_by_contra` tactic

Changes the goal to `False`, retaining as much information as possible:

* If the goal is `False`, do nothing.
* If the goal is an implication or a function type, introduce the argument and restart.
  (In particular, if the goal is `x ≠ y`, introduce `x = y`.)
* Otherwise, for a propositional goal `P`, replace it with `¬ ¬ P`
  (attempting to find a `Decidable` instance, but otherwise falling back to working classically)
  and introduce `¬ P`.
* For a non-propositional goal use `False.elim`.
-/

namespace Lean.MVarId

open Lean Meta Elab Tactic

@[inherit_doc Lean.Parser.Tactic.falseOrByContra]
-- When `useClassical` is `none`, we try to find a `Decidable` instance when replacing `P` with `¬ ¬ P`,
-- but fall back to a classical instance. When it is `some true`, we always use the classical instance.
-- When it is `some false`, if there is no `Decidable` instance we don't introduce the double negation,
-- and fall back to `False.elim`.
partial def falseOrByContra (g : MVarId) (useClassical : Option Bool := none) : MetaM MVarId := do
  let ty ← whnfR (← g.getType)
  match ty with
  | .const ``False _ => pure g
  | .forallE _ _ _ _
  | .app (.const ``Not _) _ => falseOrByContra (← g.intro1).2
  | _ =>
    let gs ← if ← isProp ty then
      match useClassical with
      | some true => some <$> g.applyConst ``Classical.byContradiction
      | some false =>
        try some <$> g.applyConst ``Decidable.byContradiction
        catch _ => pure none
      | none =>
        try some <$> g.applyConst ``Decidable.byContradiction
        catch _ => some <$> g.applyConst ``Classical.byContradiction
    else
      pure none
    if let some gs := gs then
      let [g] := gs | panic! "expected one subgoal"
      pure (← g.intro1).2
    else
      let [g] ← g.applyConst ``False.elim | panic! "expected one sugoal"
      pure g

@[builtin_tactic falseOrByContra]
def elabFalseOrByContra : Tactic
   | `(tactic| false_or_by_contra) => do liftMetaTactic1 (falseOrByContra ·)
   | _ => no_error_if_unused% throwUnsupportedSyntax

end Lean.MVarId
