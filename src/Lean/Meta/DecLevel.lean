/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Basic
import Lean.Meta.InferType

namespace Lean.Meta

structure DecLevelContext where
  /--
   If `true`, then `decAux? ?m` returns a fresh metavariable `?n` s.t.
   `?m := ?n+1`.
   -/
  canAssignMVars : Bool := true

private partial def decAux? : Level → ReaderT DecLevelContext MetaM (Option Level)
  | Level.zero        => return none
  | Level.param _     => return none
  | Level.mvar mvarId => do
    match (← getLevelMVarAssignment? mvarId) with
    | some u => decAux? u
    | none   =>
      if (← mvarId.isReadOnly) || !(← read).canAssignMVars then
        return none
      else
        let u ← mkFreshLevelMVar
        trace[Meta.isLevelDefEq.step] "decAux?, {mkLevelMVar mvarId} := {mkLevelSucc u}"
        assignLevelMVar mvarId (mkLevelSucc u)
        return u
  | Level.succ u  => return u
  | u =>
    let processMax (u v : Level) : ReaderT DecLevelContext MetaM (Option Level) := do
      /- Remark: this code uses the fact that `max (u+1) (v+1) = (max u v)+1`.
         `decAux? (max (u+1) (v+1)) := max (decAux? (u+1)) (decAux? (v+1))`
         However, we must *not* assign metavariables in the recursive calls since
         `max ?u 1` is not equivalent to `max ?v 0` where `?v` is a fresh metavariable, and `?u := ?v+1`
       -/
      withReader (fun _ => { canAssignMVars := false }) do
        match (← decAux? u) with
        | none   => return none
        | some u => do
          match (← decAux? v) with
          | none   => return none
          | some v => return mkLevelMax' u v
    match u with
    | Level.max u v  => processMax u v
    /- Remark: If `decAux? v` returns `some ...`, then `imax u v` is equivalent to `max u v`. -/
    | Level.imax u v => processMax u v
    | _              => unreachable!

def decLevel? (u : Level) : MetaM (Option Level) := do
  let mctx ← getMCtx
  match (← decAux? u |>.run {}) with
  | some v => return some v
  | none   => do
    modify fun s => { s with mctx := mctx }
    return none

def decLevel (u : Level) : MetaM Level := do
  match (← decLevel? u) with
  | some u => return u
  | none   => throwError "invalid universe level, {u} is not greater than 0"

/-- This method is useful for inferring universe level parameters for function that take arguments such as `{α : Type u}`.
   Recall that `Type u` is `Sort (u+1)` in Lean. Thus, given `α`, we must infer its universe level,
   and then decrement 1 to obtain `u`. -/
def getDecLevel (type : Expr) : MetaM Level := do
  decLevel (← getLevel type)

end Lean.Meta
