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

def decLevel? (u : Level) : MetaM (Option Level) := do
  if let some u' := u.dec then
    return u'
  else
    /-
    Recall that `instantiateLevelMVars` effectively uses `mkLevelMax'`/`mkLevelIMax'`,
    which means we do not need any special analysis for `max 0 (u+1)`, etc.
    -/
    let u ← instantiateLevelMVars u
    /-
    If `u` is a metavariable `?m`, then we can assign `?m := ?m'+1` where `?m'` is a fresh
    metavariable to make it decrementable.

    We do not decrement `max` expressions. Consider for example `max ?m (v+1)`.
    There are two ways to make this decrementable: either `?m := 0` or `?m := ?m'+1`,
    where `?m'` is a fresh metavariable. We cannot make this decision here.

    On the other hand, `imax (u+1) ?m` is only decrementable by assigning `?m := ?m'+1`,
    since assigning `?m := 0` would reduce the level to `0`.
    We do not currently make the assignment however. Speculative uses of `decLevel?`
    may prevent arrows from being inferred as propositions.
    -/
    if let Level.mvar mvarId := u then
      if (← mvarId.isReadOnly) then
        return none
      else
        let u' ← mkFreshLevelMVar
        trace[Meta.isLevelDefEq.step] "decAux?, {u} := {Level.succ u'}"
        assignLevelMVar mvarId (Level.succ u')
        return u'
    else
      return u.dec

def decLevel (u : Level) : MetaM Level := do
  match (← decLevel? u) with
  | some u => return u
  | none   => throwError "invalid universe level, {u} is not greater than 0"

/-- This method is useful for inferring universe level parameters for function that take arguments such as `{α : Type u}`.
   Recall that `Type u` is `Sort (u+1)` in Lean. Thus, given `α`, we must infer its universe level,
   instantiate and normalize it, and then decrement 1 to obtain `u`. -/
def getDecLevel (type : Expr) : MetaM Level := do
  let l ← getLevel type
  let l ← normalizeLevel l
  decLevel l

def getDecLevel? (type : Expr) : MetaM (Option Level) := do
  let l ← getLevel type
  let l ← normalizeLevel l
  decLevel? l

builtin_initialize
  registerTraceClass `Meta.isLevelDefEq.step

end Lean.Meta
