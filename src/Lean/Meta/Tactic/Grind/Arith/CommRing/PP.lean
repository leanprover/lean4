/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
public import Lean.Meta.Sym.Arith.Types
import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
import Init.Omega
public section
namespace Lean.Meta.Grind.Arith.CommRing
open Sym.Arith

/-- The two halves of one ring: its `Sym.Arith` classification record and the goal's solver state. -/
private structure RingInfo where
  ring  : Sym.Arith.CommRing
  state : CommRingState

private abbrev M := StateT RingInfo MetaM

private instance : MonadCanon M where
  canonExpr e := return e
  synthInstance? e := Meta.synthInstance? e none

private instance : MonadCommRing M where
  getCommRing := return (← get).ring
  modifyCommRing f := modify fun s => { s with ring := f s.ring }

private instance : MonadCommRingState M where
  getCommRingState := return (← get).state
  modifyCommRingState f := modify fun s => { s with state := f s.state }

private instance : MonadGetVar M where
  getVar x := return (← get).state.vars[x]!

private def toOption (cls : Name) (header : Thunk MessageData) (msgs : Array MessageData) : Option MessageData :=
  if msgs.isEmpty then
    none
  else
    some (.trace {cls} header.get msgs)

private def push (msgs : Array MessageData) (msg? : Option MessageData) : Array MessageData :=
  if let some msg := msg? then msgs.push msg else msgs

private def ppBasis? : M (Option MessageData) := do
  let mut basis := #[]
  for c in (← getCommRingState).basis do
    basis := basis.push (toTraceElem (← c.denoteExpr))
  return toOption `basis "Basis" basis

private def ppDiseqs? : M (Option MessageData) := do
  let mut diseqs := #[]
  for d in (← getCommRingState).diseqs do
    diseqs := diseqs.push (toTraceElem (← d.denoteExpr))
  return toOption `diseqs "Disequalities" diseqs

private def ppRing? : M (Option MessageData) := do
  let msgs := #[]
  let msgs := push msgs (← ppBasis?)
  let msgs := push msgs (← ppDiseqs?)
  return toOption `ring m!"Ring `{(← getRing).type}`" msgs

/--
Prints the ring solver state of `goal`. `rings` are the `Sym.Arith` records of the run
(see `Result.rings`).

Both arrays are indexed by the ring id assigned by `Sym.Arith.classify?`: the goal's state
is written at that id (`RingM.modifyCommRingState`), and the `Sym.Arith` array only grows
during a run, so `rings` is at least as long as `s.rings` and `rings[i]` is the record of
`s.rings[i]`.
-/
def pp? (goal : Goal) (rings : Array Sym.Arith.CommRing) : MetaM (Option MessageData) := do
  let mut msgs := #[]
  let s ← ringExt.getStateCore goal
  for i in [:s.rings.size] do
    let some ring := rings[i]?
      | throwError "`grind` internal error, ring solver state without a `Sym.Arith` record (ring id {i})"
    let some msg ← ppRing? |>.run' { ring, state := s.getRing i } | continue
    msgs := msgs.push msg
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
