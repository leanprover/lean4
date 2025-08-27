/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
public import Lean.Meta.Tactic.Grind.AC.Util
import Lean.Meta.Tactic.Grind.AC.DenoteExpr
public section
namespace Lean.Meta.Grind.AC

private def isParentSameOpApp (parent? : Option Expr) (op : Expr) : GoalM Bool := do
  let some e := parent? | return false
  unless e.isApp && e.appFn!.isApp do return false
  return isSameExpr e.appFn!.appFn! op

partial def reify (e : Expr) : ACM Grind.AC.Expr := do
  if let some (a, b) ← isOp? e then
    return .op (← reify a) (← reify b)
  else
    return .var (← mkVar e)

@[export lean_grind_ac_internalize]
def internalizeImpl (e : Expr) (parent? : Option Expr) : GoalM Unit := do
  unless (← getConfig).ac do return ()
  unless e.isApp && e.appFn!.isApp do return ()
  let op := e.appFn!.appFn!
  let some id ← getOpId? op | return ()
  if (← isParentSameOpApp parent? op) then return ()
  ACM.run id do
    if (← getStruct).denote.contains { expr := e } then return ()
    let e' ← reify e
    modifyStruct fun s => { s with denote := s.denote.insert { expr := e } e' }
    trace[grind.ac.internalize] "[{id}] {← e'.denoteExpr}"
    addTermOpId e
    markAsACTerm e

end Lean.Meta.Grind.AC
