/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
public import Lean.Meta.Tactic.Grind.AC.Util
public section
namespace Lean.Meta.Grind.AC

private def isParentSameOpApp (parent? : Option Expr) (op : Expr) : GoalM Bool := do
  let some e := parent? | return false
  unless e.isApp && e.appFn!.isApp do return false
  return isSameExpr e.appFn!.appFn! op

def internalize (e : Expr) (parent? : Option Expr) : GoalM Unit := do
  unless (← getConfig).ac do return ()
  unless e.isApp && e.appFn!.isApp do return ()
  let op := e.appFn!.appFn!
  let some id ← getOpId? op | return ()
  if (← isParentSameOpApp parent? op) then return ()
  trace[grind.ac.internalize] "[{id}] {e}"
  -- TODO: internalize `e`

end Lean.Meta.Grind.AC
