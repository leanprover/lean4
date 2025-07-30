/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.SynthInstance
public import Lean.Meta.Tactic.Grind.Types

public section

namespace Lean.Meta.Grind

def synthInstanceMeta? (type : Expr) : MetaM (Option Expr) := do profileitM Exception "grind typeclass inference" (← getOptions) (decl := type.getAppFn.constName?.getD .anonymous) do
  catchInternalId isDefEqStuckExceptionId
    (synthInstanceCore? type none)
    (fun _ => pure none)

abbrev synthInstance? (type : Expr) : GoalM (Option Expr) :=
  synthInstanceMeta? type

def synthInstance (type : Expr) : GoalM Expr := do
  let some inst ← synthInstance? type
    | throwError "`grind` failed to find instance{indentExpr type}"
  return inst

/--
Helper function for instantiating a type class `type`, and
then using the result to perform `isDefEq x val`.
-/
def synthInstanceAndAssign (x type : Expr) : GoalM Bool := do
  let some val ← synthInstance? type | return false
  isDefEq x val

end Lean.Meta.Grind
