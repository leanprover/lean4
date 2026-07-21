/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Tactic.Util

public section

namespace Lean.Meta

/-- Return a local declaration whose type is definitionally equal to `type`, searching most-recent
first. With `lowerBound > 0` and/or `upperBound > 0`, only declarations at context index in
`[lowerBound, upperBound)` are considered (an `upperBound` of `0` means the end of the context), so
the scan is confined to a window of the local context rather than the whole of it. -/
def findLocalDeclWithType? (type : Expr) (lowerBound : Nat := 0) (upperBound : Nat := 0) :
    MetaM (Option FVarId) := do
  let lctx ← getLCtx
  if lowerBound == 0 && upperBound == 0 then
    lctx.findDeclRevM? fun localDecl => do
      if localDecl.isImplementationDetail then
        return none
      else if (← isDefEq type localDecl.type) then
        return some localDecl.fvarId
      else
        return none
  else
    let hi := if upperBound == 0 then lctx.decls.size else min upperBound lctx.decls.size
    let slice := (lctx.decls.foldl (init := (#[] : Array (Option LocalDecl))) (start := lowerBound)
      Array.push).take (hi - lowerBound)
    slice.findSomeRevM? fun localDecl? => do
      let some localDecl := localDecl? | return none
      if localDecl.isImplementationDetail then
        return none
      else if (← isDefEq type localDecl.type) then
        return some localDecl.fvarId
      else
        return none

/-- Return `true` if managed to close goal `mvarId` using an assumption. -/
def _root_.Lean.MVarId.assumptionCore (mvarId : MVarId) : MetaM Bool :=
  mvarId.withContext do
    mvarId.checkNotAssigned `assumption
    match (← findLocalDeclWithType? (← mvarId.getType)) with
    | none => return false
    | some fvarId => mvarId.assign (mkFVar fvarId); return true

/-- Close goal `mvarId` using an assumption. Throw error message if failed. -/
def _root_.Lean.MVarId.assumption (mvarId : MVarId) : MetaM Unit :=
  unless (← mvarId.assumptionCore) do
    throwTacticEx `assumption mvarId

end Lean.Meta
