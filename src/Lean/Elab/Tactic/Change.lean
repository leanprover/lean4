/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
prelude
import Lean.Meta.Tactic.Replace
import Lean.Elab.Tactic.Location

namespace Lean.Elab.Tactic
open Meta
/-!
# Implementation of the `change` tactic
-/

/-- `change` can be used to replace the main goal or its hypotheses with
different, yet definitionally equal, goal or hypotheses.

For example, if `n : Nat` and the current goal is `⊢ n + 2 = 2`, then
```lean
change _ + 1 = _
```
changes the goal to `⊢ n + 1 + 1 = 2`.

The tactic also applies to hypotheses. If `h : n + 2 = 2` and `h' : n + 3 = 4`
are hypotheses, then
```lean
change _ + 1 = _ at h h'
```
changes their types to be `h : n + 1 + 1 = 2` and `h' : n + 2 + 1 = 4`.

Change is like `refine` in that every placeholder needs to be solved for by unification,
but using named placeholders or `?_` results in `change` creating new goals.

In the absense of such placeholders, the tactic `show e` is interchangeable with `change e`, where
the pattern `e` is applied to the main goal.
-/
@[builtin_tactic change] elab_rules : tactic
  | `(tactic| change $newType:term $[$loc:location]?) => do
    withLocation (expandOptLocation (Lean.mkOptionalNode loc))
      (atLocal := fun h => do
        let hTy ← h.getType
        let mvar ← mkFreshExprMVar none
        let (_, mvars) ← elabTermWithHoles
                          (← `(term | (id $(← Term.exprToSyntax mvar) : $newType))) hTy `change
        liftMetaTactic fun mvarId => do
          return (← mvarId.changeLocalDecl h (← inferType mvar)) :: mvars)
      (atTarget := evalTactic <| ← `(tactic| refine_lift (id ?_ : $newType)))
      (failed := fun _ => throwError "change tactic failed")

end Lean.Elab.Tactic
