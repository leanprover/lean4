/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr

namespace Lean.Meta.Grind.Arith.CommRing

instance : MonadGetRing (ReaderT Ring MetaM) where
  getRing := read

private def M := ReaderT Goal (StateT (Array MessageData) MetaM)

private def toOption (cls : Name) (header : Thunk MessageData) (msgs : Array MessageData) : Option MessageData :=
  if msgs.isEmpty then
    none
  else
    some (.trace {cls} header.get msgs)

private def push (msgs : Array MessageData) (msg? : Option MessageData) : Array MessageData :=
  if let some msg := msg? then msgs.push msg else msgs

def ppBasis? : ReaderT Ring MetaM (Option MessageData) := do
  let mut basis := #[]
  for cs in (← getRing).varToBasis do
    for c in cs do
      basis := basis.push (toTraceElem (← c.denoteExpr))
  return toOption `basis "Basis" basis

def ppDiseqs? : ReaderT Ring MetaM (Option MessageData) := do
  let mut diseqs := #[]
  for d in (← getRing).diseqs do
    diseqs := diseqs.push (toTraceElem (← d.denoteExpr))
  return toOption `diseqs "Disequalities" diseqs

def ppRing? : ReaderT Ring MetaM (Option MessageData) := do
  let msgs := #[]
  let msgs := push msgs (← ppBasis?)
  let msgs := push msgs (← ppDiseqs?)
  return toOption `ring m!"Ring `{(← getRing).type}`" msgs

def pp? (goal : Goal) : MetaM (Option MessageData) := do
  let mut msgs := #[]
  for ring in goal.arith.ring.rings do
    let some msg ← ppRing? ring | pure ()
    msgs := msgs.push msg
  if msgs.isEmpty then
    return none
  else if h : msgs.size = 1 then
    return some msgs[0]
  else
    return some (.trace { cls := `ring } "Rings" msgs)

end Lean.Meta.Grind.Arith.CommRing
