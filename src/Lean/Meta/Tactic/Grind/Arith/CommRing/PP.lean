/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
import Lean.Meta.Tactic.Grind.Arith.CommRing.Functions
import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
public section
namespace Lean.Meta.Grind.Arith.CommRing

private abbrev M := StateT Ring MetaM

private instance : MonadRing M where
  getRing := get
  modifyRing := modify
  canonExpr e := return e
  synthInstance? e := Meta.synthInstance? e none

private def toOption (cls : Name) (header : Thunk MessageData) (msgs : Array MessageData) : Option MessageData :=
  if msgs.isEmpty then
    none
  else
    some (.trace {cls} header.get msgs)

private def push (msgs : Array MessageData) (msg? : Option MessageData) : Array MessageData :=
  if let some msg := msg? then msgs.push msg else msgs

private def ppBasis? : M (Option MessageData) := do
  let mut basis := #[]
  for c in (← getRing).basis do
    basis := basis.push (toTraceElem (← c.denoteExpr))
  return toOption `basis "Basis" basis

private def ppDiseqs? : M (Option MessageData) := do
  let mut diseqs := #[]
  for d in (← getRing).diseqs do
    diseqs := diseqs.push (toTraceElem (← d.denoteExpr))
  return toOption `diseqs "Disequalities" diseqs

private def ppRing? : M (Option MessageData) := do
  let msgs := #[]
  let msgs := push msgs (← ppBasis?)
  let msgs := push msgs (← ppDiseqs?)
  return toOption `ring m!"Ring `{(← getRing).type}`" msgs

def pp? (goal : Goal) : MetaM (Option MessageData) := do
  let mut msgs := #[]
  for ring in goal.arith.ring.rings do
    let some msg ← ppRing? |>.run' ring | pure ()
    msgs := msgs.push msg
  if msgs.isEmpty then
    return none
  else if h : msgs.size = 1 then
    return some msgs[0]
  else
    return some (.trace { cls := `ring } "Rings" msgs)

end Lean.Meta.Grind.Arith.CommRing
