/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.InferType

public section

namespace Lean.Meta

private inductive DecResult where
  /-- The level can be decremented. -/
  | succ (u : Level)
  /-- The level cannot be decremented since it is always zero. -/
  | zero
  /-- The level `u` cannot be decremented due to a metavariable `?v`, and `?v` is the only metavariable
  such that `1 ≤ u` implies `1 ≤ ?v`. Hence, assigning `?v := ?v'+1` where `?v'` is a fresh metavariable
  will make it possible to decrement `u`. -/
  | mvar (mvarId : LMVarId)
  /-- The expression cannot be decremented due to a parameter or metavariable. -/
  | none

private def DecResult.isSucc (r? : DecResult) : Bool := r? matches .succ _

/--
`decAux? u` checks whether `1 ≤ u` by finding a level `u'` such that `u = u'+1`, if possible.
-/
private partial def decAux? : Level → MetaM DecResult
  | Level.zero        => return .zero
  | Level.succ u      => return .succ u
  | Level.param _     => return .none
  | Level.mvar mvarId => do
    match (← getLevelMVarAssignment? mvarId) with
    | some u          => decAux? u
    | none            => return .mvar mvarId
  | Level.max u v     => processMax u v false
  | Level.imax u v    => processMax u v true
where
  /--
  Decrements `max` or `imax` using the rules
  - `max (u+1) (v+1) = (max u v) + 1`
  - `max (u+1) 0 = u+1`
  - `max 0 (v+1) = v+1`
  - `imax (u+1) (v+1) = (max u v) + 1`
  - `imax 0 (v+1) = v+1`

  In general, `1 ≤ max u v` iff `1 ≤ u` or `1 ≤ v`.
  If neither `u` nor `v` is zero, then we need both `1 ≤ u` and `1 ≤ v` to be true to decrement `max u v`.
  If `1 ≤ u` or `1 ≤ v` can be made to be true by metavariable assignments, then we want to determine
  the unique solution, if one exists. This is only possible if both `1 ≤ u` and `1 ≤ v` are obstructed by the same metavariable.

  There is also a special rule for `imax (u+1) ?v`, since `1 ≤ imax (u+1) ?v` is only satisfiable if `1 ≤ ?v`.
  We let `imax ?u ?v` fail since after a `?v := ?v'+1` assignment, `imax ?u (?v'+1) = max ?u (?v'+1)`,
  and `1 ≤ max ?u (?v'+1)` is true even if `?u = 0`.
  -/
  processMax (u v : Level) (imax : Bool) : MetaM DecResult := do
    match (← decAux? u), (← decAux? v) with
    | .succ u',      .succ v'      => return .succ <| mkLevelMax' u' v'
    | u'?,           .zero         => return if imax then .zero else u'?
    | .zero,         v'?           => return v'?
    | .mvar uMVarId, .mvar vMVarId => return if uMVarId == vMVarId then .mvar uMVarId else .none
    | .mvar _,       _             => return .none
    | u'?,           .mvar vMVarId => return if imax && u'?.isSucc then .mvar vMVarId else .none
    | .none,         _             => return .none
    | _,             .none         => return .none

/--
Returns a level `u'` such that `u = u'+1`, if such a level exists.

If there's a metavariable `?v` that obstructs decrementing the level, then it assigns `?v := ?v'+1`
where `?v'` is a fresh metavariable, but only if the inequality `1 ≤ u` implies `1 ≤ ?v`.
-/
def decLevel? (u : Level) : MetaM (Option Level) := do
  match (← decAux? u) with
  | .zero | .none => return none
  | .succ u'      => return u'
  | .mvar mvarId  =>
    if (← mvarId.isReadOnly) then
      return none
    else
      let v ← mkFreshLevelMVar
      trace[Meta.isLevelDefEq.step] "decAux?, {mkLevelMVar mvarId} := {mkLevelSucc v}"
      assignLevelMVar mvarId (mkLevelSucc v)
      match (← decAux? u) with
      | .succ u' => return u'
      | _        => unreachable!

/--
Returns a level `u'` such that `u = u'+1`. Throws an error if no such level exist.

Assigns metavariables to make this possible. See `decLevel?` for details.
-/
def decLevel (u : Level) : MetaM Level := do
  match (← decLevel? u) with
  | some u => return u
  | none   => throwError "invalid universe level, {u} is not greater than 0"

/--
Given a type `α`, infers the universe level `u` such that `α : Type u`. Throws an error if no such level exists.

Assigns metavariables to make this possible. See `decLevel?` for details.

This method is useful for inferring universe level parameters for functions that take arguments such as `{α : Type u}`.
Recall that `Type u` is `Sort (u+1)` in Lean. Thus, given `α`, we must infer its universe level,
and then decrement by one to obtain `u`.
-/
def getDecLevel (type : Expr) : MetaM Level := do
  decLevel (← getLevel type)

/--
Given a type `α`, infers the universe level `u` such that `α : Type u`, if such a level exists.

See `getDecLevel` for details.
-/
def getDecLevel? (type : Expr) : MetaM (Option Level) := do
  decLevel? (← getLevel type)

builtin_initialize
  registerTraceClass `Meta.isLevelDefEq.step

end Lean.Meta
