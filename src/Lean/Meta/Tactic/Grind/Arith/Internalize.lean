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

def internalizeCnstr (e : Expr) : GoalM Unit := do
  let some c := isNatOffsetCnstr? e | return ()
  let u ← mkNode c.u
  let v ← mkNode c.v
  let c := { c with u, v }
  trace[grind.offset.internalize] "{e} ↦ {c}"
  modify' fun s => { s with
    cnstrs   := s.cnstrs.insert { expr := e } c
    cnstrsOf :=
      let cs := if let some cs := s.cnstrsOf.find? (u, v) then (c, e) :: cs else [(c, e)]
      s.cnstrsOf.insert (u, v) cs
  }

end Offset

def internalize (e : Expr) : GoalM Unit := do
  Offset.internalizeCnstr e

end Lean.Meta.Grind.Arith
