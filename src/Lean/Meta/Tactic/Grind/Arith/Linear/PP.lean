/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Linear.Types
import Lean.Meta.Tactic.Grind.Arith.Linear.Model
import Lean.Meta.Tactic.Grind.Arith.Util
import Init.Data.Int.Order
import Init.Omega
public section
namespace Lean.Meta.Grind.Arith.Linear

def ppStruct? (goal : Goal) (s : Struct) : MetaM (Option MessageData) := do
  let model ← mkModel goal s.id
  if model.isEmpty then return none
  let mut ms := #[]
  for (e, val) in model do
    ms := ms.push <| .trace { cls := `assign } m!"{Arith.quoteIfArithTerm e} := {val}" #[]
  return some (.trace { cls := `linarith } m!"Linarith assignment for `{s.type}`" ms)

def pp? (goal : Goal) : MetaM (Option MessageData) := do
  let mut msgs := #[]
  for struct in (← linearExt.getStateCore goal).structs do
    let some msg ← ppStruct? goal struct | pure ()
    msgs := msgs.push msg
  if msgs.isEmpty then
    return none
  else if h : msgs.size = 1 then
    return some msgs[0]
  else
    return some (.trace { cls := `linarith } "Linarith" msgs)

end Lean.Meta.Grind.Arith.Linear
