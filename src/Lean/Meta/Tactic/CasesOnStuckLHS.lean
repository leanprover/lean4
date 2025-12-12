/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Basic
import Lean.Meta.Tactic.SplitIf

namespace Lean.Meta

/-!
This module provides the `casesOnStuckLHS` tactic, used by
* match equation compilation
* equation compilation for recursive functions
-/

/--
Helper method for `proveCondEqThm`.
Given a goal of the form `C.rec ... xMajor = rhs`,
if `xMajor` is a free variable, apply `cases xMajor`.
(As a corner case, `xMajor := Eq.symm h` where `h` is a free variable is also supported.)
-/
public partial def casesOnStuckLHS (mvarId : MVarId) : MetaM (Array MVarId) := do
  let target ← mvarId.getType
  if let some (_, lhs) ← matchEqHEqLHS? target then
    if let some fvarId ← findFVar? lhs then
      return (←  mvarId.cases fvarId).map fun s => s.mvarId
  throwError "'casesOnStuckLHS' failed"
where
  findFVar? (e : Expr) : MetaM (Option FVarId) := do
    match e.getAppFn with
    | Expr.proj _ _ e => findFVar? e
    | f =>
      if !f.isConst then
        return none
      else
        let declName := f.constName!
        let args := e.getAppArgs
        match (← getProjectionFnInfo? declName) with
        | some projInfo =>
          if projInfo.numParams < args.size then
            findFVar? args[projInfo.numParams]!
          else
            return none
        | none =>
          matchConstRec f (fun _ => return none) fun recVal _ => do
            if recVal.getMajorIdx >= args.size then
              return none
            return getMajorFVar args[recVal.getMajorIdx]!.consumeMData

  getMajorFVar (e : Expr) : Option FVarId := do
    if e.isFVar then
      return e.fvarId!
    else if e.isAppOfArity ``Eq.symm 4 then
      getMajorFVar e.appArg!
    else
      none

public def casesOnStuckLHS? (mvarId : MVarId) : MetaM (Option (Array MVarId)) := do
  try casesOnStuckLHS mvarId catch _ => return none
