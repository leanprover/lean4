/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Linear.Var
import Lean.Meta.Tactic.Grind.Arith.Linear.StructId
import Lean.Meta.Tactic.Grind.Arith.Linear.Reify
import Lean.Meta.Tactic.Grind.Arith.Linear.DenoteExpr

namespace Lean.Meta.Grind.Arith.Linear

def isLeInst (struct : Struct) (inst : Expr) : Bool :=
  isSameExpr struct.leFn.appArg! inst
def isLtInst (struct : Struct) (inst : Expr) : Bool :=
  isSameExpr struct.ltFn.appArg! inst

def propagateIneq (e : Expr) (eqTrue : Bool) : GoalM Unit := do
  let numArgs := e.getAppNumArgs
  unless numArgs == 4 do return ()
  let α := e.getArg! 0 numArgs
  let some structId ← getStructId? α | return ()
  LinearM.run structId do
    let inst := e.getArg! 1 numArgs
    let struct ← getStruct
    let strict ← if isLeInst struct inst then
      pure false
    else if isLtInst struct inst then
      pure true
    else
      trace[grind.linarith] "invalid {e}, {(← getStruct).leFn}, {(← getStruct).ltFn}"
      return ()
    let some lhs ← reify? (e.getArg! 2 numArgs) (skipVar := false) | trace[grind.linarith] "lhs failed {e}"; return ()
    let some rhs ← reify? (e.getArg! 3 numArgs) (skipVar := false) | trace[grind.linarith] "rhs failed {e}"; return ()
    let p := (lhs.sub rhs).norm
    -- TODO
    trace[grind.linarith] "{e}, {eqTrue}, strict: {strict}, structId: {structId}"
    trace[grind.linarith] "{← p.denoteExpr}"
    trace[grind.linarith] "structId: {structId}"
    return ()

end Lean.Meta.Grind.Arith.Linear
