/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.AC.DenoteExpr
import Init.Omega
public section
namespace Lean.Meta.Grind.AC

private abbrev M := StateT Struct MetaM

private instance : MonadGetStruct M where
  getStruct := get

private def toOption (cls : Name) (header : Thunk MessageData) (msgs : Array MessageData) : Option MessageData :=
  if msgs.isEmpty then
    none
  else
    some (.trace {cls} header.get msgs)

private def push (msgs : Array MessageData) (msg? : Option MessageData) : Array MessageData :=
  if let some msg := msg? then msgs.push msg else msgs

private def ppBasis? : M (Option MessageData) := do
  let mut basis := #[]
  for c in (← getStruct).basis do
    basis := basis.push (toTraceElem (← c.denoteExpr))
  return toOption `basis "Basis" basis

private def ppDiseqs? : M (Option MessageData) := do
  let mut diseqs := #[]
  for d in (← getStruct).diseqs do
    diseqs := diseqs.push (toTraceElem (← d.denoteExpr))
  return toOption `diseqs "Disequalities" diseqs

private def ppStruct? : M (Option MessageData) := do
  let mut msgs := #[]
  msgs := push msgs (← ppBasis?)
  msgs := push msgs (← ppDiseqs?)
  unless msgs.isEmpty do
    let mut info := #[]
    if (← get).commInst?.isSome then
      info := info.push <| toTraceElem "commutative"
    if (← get).idempotentInst?.isSome then
      info := info.push <| toTraceElem "idempotent"
    if let some u := (← get).neutral? then
      info := info.push <| toTraceElem m!"identity: `{u}`"
    msgs := push msgs (toOption `properties "Properties" info)
  return toOption `assoc m!"Operator `{(← getStruct).op}`" msgs

def pp? (goal : Goal) : MetaM (Option MessageData) := do
  let mut msgs := #[]
  for struct in (← acExt.getStateCore goal).structs do
    let some msg ← ppStruct? |>.run' struct | pure ()
    msgs := msgs.push msg
  if msgs.isEmpty then
    return none
  else if h : msgs.size = 1 then
    return some msgs[0]
  else
    return some (.trace { cls := `assoc } "Operators" msgs)

end Lean.Meta.Grind.AC
