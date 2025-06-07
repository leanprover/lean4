/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Linear.Var
import Lean.Meta.Tactic.Grind.Arith.Linear.StructId

namespace Lean.Meta.Grind.Arith.Linear

def propagateIneq (e : Expr) (eqTrue : Bool) (strict : Bool) : GoalM Unit := do
  trace[grind.linarith] "{e}, {eqTrue}, {strict}"
  let args := e.getAppArgs
  unless args.size == 4 do return ()
  let α := args[0]!
  let some structId ← getStructId? α | return ()
  trace[grind.linarith] "structId: {structId}"
  -- TODO
  return ()

end Lean.Meta.Grind.Arith.Linear
