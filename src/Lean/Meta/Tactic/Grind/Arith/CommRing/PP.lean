/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
public import Lean.Meta.Tactic.Grind.Arith.CommRing.Types
public import Lean.Meta.Tactic.Grind.Arith.CommRing.Denote
import Lean.Meta.Sym.Arith.DenoteExpr
import Init.Omega
public section
namespace Lean.Meta.Grind.Arith.CommRing
open Sym.Arith

private abbrev M := StateT (CommRing × CommRingEntry) MetaM

private instance : MonadCanon M where
  canonExpr e := return e
  synthInstance? e := Meta.synthInstance? e none

private instance : MonadCommRing M where
  getCommRing := return (← get).1
  modifyCommRing f := modify fun (r, e) => (f r, e)

private instance : MonadGetVar M where
  getVar x := return (← get).2.vars[x]!

private def toOption (cls : Name) (header : Thunk MessageData) (msgs : Array MessageData) : Option MessageData :=
  if msgs.isEmpty then
    none
  else
    some (.trace {cls} header.get msgs)

private def push (msgs : Array MessageData) (msg? : Option MessageData) : Array MessageData :=
  if let some msg := msg? then msgs.push msg else msgs

private def getCommRingEntry : M CommRingEntry :=
  return (← get).2

private def ppBasis? : M (Option MessageData) := do
  let mut basis := #[]
  for c in (← getCommRingEntry).basis do
    basis := basis.push (toTraceElem (← c.denoteExpr))
  return toOption `basis "Basis" basis

private def ppDiseqs? : M (Option MessageData) := do
  let mut diseqs := #[]
  for d in (← getCommRingEntry).diseqs do
    diseqs := diseqs.push (toTraceElem (← d.denoteExpr))
  return toOption `diseqs "Disequalities" diseqs

private def ppRing? : M (Option MessageData) := do
  let msgs := #[]
  let msgs := push msgs (← ppBasis?)
  let msgs := push msgs (← ppDiseqs?)
  return toOption `ring m!"Ring `{(← getRing).type}`" msgs

def pp? (goal : Goal) : MetaM (Option MessageData) := do
  let mut msgs := #[]
  for ringEntry in (← ringExt.getStateCore goal).rings do
    -- let ring ← getCommRingOfId ringEntry.symId
    -- let some msg ← ppRing? |>.run' (_, ringEntry) | pure ()
    -- msgs := msgs.push msg
    -- TODO: fix
    pure ()
  if msgs.isEmpty then
    return none
  else if h : msgs.size = 1 then
    return some msgs[0]
  else
    return some (.trace { cls := `ring } "Rings" msgs)

def addThresholdMessage (goal : Goal) (c : Grind.Config) (msgs : Array MessageData) : IO (Array MessageData) := do
  let s ← ringExt.getStateCore goal
  if s.steps ≥ c.ringSteps then
    return msgs.push <| .trace { cls := `limit } m!"maximum number of ring steps has been reached, threshold: `(ringSteps := {c.ringSteps})`" #[]
  else
    return msgs

end Lean.Meta.Grind.Arith.CommRing
