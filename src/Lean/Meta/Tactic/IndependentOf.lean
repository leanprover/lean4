/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Jannis Limperg
-/
prelude
import Lean.Meta.CollectMVars
import Lean.Meta.Tactic.Util

namespace Lean.MVarId

open Meta

/--
Check if a goal is "independent" of a list of other goals.
We say a goal is independent of other goals if assigning a value to it
can not change the assignability of the other goals.

Examples:
* `?m_1 : Type` is not independent of `?m_2 : ?m_1`,
  because we could assign `true : Bool` to `?m_2`,
  but if we first assign `Nat` to `?m_1` then that is no longer possible.
* `?m_1 : Nat` is not independent of `?m_2 : Fin ?m_1`,
  because we could assign `37 : Fin 42` to `?m_2`,
  but if we first assign `2` to `?m_1` then that is no longer possible.
* `?m_1 : ?m_2` is not independent of `?m_2 : Type`, because we could assign `Bool` to ?m_2`,
  but if we first assign `0 : Nat` to `?m_1` then that is no longer possible.
* Given `P : Prop` and `f : P → Type`, `?m_1 : P` is independent of `?m_2 : f ?m_1`
  by proof irrelevance.
* Similarly given `f : Fin 0 → Type`, `?m_1 : Fin 0` is independent of `?m_2 : f ?m_1`,
  because `Fin 0` is a subsingleton.
* Finally `?m_1 : Nat` is independent of `?m_2 : α`,
  as long as `?m_1` does not appear in `Meta.getMVars α`
  (note that `Meta.getMVars` follows delayed assignments).

This function only calculates a conservative approximation of this condition.
That is, it may return `false` when it should return `true`.
(In particular it returns false whenever the type of `g` contains a metavariable,
regardless of whether this is related to the metavariables in `L`.)
-/
def isIndependentOf (L : List MVarId) (g : MVarId) : MetaM Bool := g.withContext do
  let t ← instantiateMVars (← g.getType)
  if t.hasExprMVar then
    -- If the goal's type contains other meta-variables,
    -- we conservatively say that `g` is not independent.
    -- It would be possible to check if `L` depends on these meta-variables.
    return false
  if (← inferType t).isProp then
    -- If the goal is propositional,
    -- proof-irrelevance ensures it is independent of any other goals.
    return true
  if ← g.isSubsingleton then
    -- If the goal is a subsingleton, it is independent of any other goals.
    return true
  -- Finally, we check if the goal `g` appears in the type of any of the goals `L`.
  L.allM fun g' => do pure !((← getMVarDependencies g').contains g)

end Lean.MVarId
