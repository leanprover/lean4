/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Offset

namespace Lean.Meta.Grind.Arith

namespace Offset

def internalizeTerm (_e : Expr) (_a : Expr) (_k : Nat) : GoalM Unit := do
  -- TODO
  return ()

def internalizeCnstr (e : Expr) (c : Cnstr Expr) : GoalM Unit := OffsetM.run do
  let c := { c with
    a := (← mkNode c.a)
    b := (← mkNode c.b)
  }
  trace[grind.offset.internalize] "{e} ↦ {c}"
  modify fun s => { s with
    cnstrs := s.cnstrs.insert { expr := e } c
  }

end Offset

def internalize (e : Expr) : GoalM Unit := do
  if let some c := isNatOffsetCnstr? e then
    Offset.internalizeCnstr e c

end Lean.Meta.Grind.Arith
