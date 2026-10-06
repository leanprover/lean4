/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Linear.Types
public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
public section
namespace Lean.Meta.Grind.Arith.Linear
open Sym.Arith (MonadCanon MonadRing MonadGetVar)

def get' : GoalM State := do
  linearExt.getState

@[inline] def modify' (f : State → State) : GoalM Unit := do
  linearExt.modifyState f

structure LinearM.Context where
  structId : Nat

class MonadGetStruct (m : Type → Type) where
  getStruct : m Struct

export MonadGetStruct (getStruct)

@[always_inline]
instance (m n) [MonadLift m n] [MonadGetStruct m] : MonadGetStruct n where
  getStruct    := liftM (getStruct : m Struct)

/-- We don't want to keep carrying the `StructId` around. -/
abbrev LinearM := ReaderT LinearM.Context GoalM

abbrev LinearM.run (structId : Nat) (x : LinearM α) : GoalM α :=
  x { structId }

abbrev getStructId : LinearM Nat :=
  return (← read).structId

protected def LinearM.getStruct : LinearM Struct := do
  let s ← get'
  let structId ← getStructId
  if h : structId < s.structs.size then
    return s.structs[structId]
  else
    throwError "`grind` internal error, invalid structure id"

instance : MonadGetStruct LinearM where
  getStruct := LinearM.getStruct

open CommRing

def getRingCore? (ringId? : Option Nat) : GoalM (Option Sym.Arith.Ring) := do
  let some ringId := ringId? | return none
  RingM.run ringId do return some (← Sym.Arith.getRing)

def throwNotRing : LinearM α :=
  throwError "`grind linarith` internal error, structure is not a ring"

def throwNotCommRing : LinearM α :=
  throwError "`grind linarith` internal error, structure is not a commutative ring"

def getRing? : LinearM (Option Sym.Arith.Ring) := do
  getRingCore? (← getStruct).ringId?

instance : MonadCanon LinearM where
  canonExpr e := do shareCommon (← canon e)
  synthInstance? e := Grind.synthInstance? e

def LinearM.getRing : LinearM Sym.Arith.Ring := do
  let some ring ← getRing?
    | throwNotCommRing
  return ring

def withRingM (x : RingM α) : LinearM α := do
  let some ringId := (← getStruct).ringId?
    | throwNotCommRing
  RingM.run ringId x

instance : MonadRing LinearM where
  getRing := LinearM.getRing
  modifyRing f := withRingM do Sym.Arith.modifyRing f

instance : MonadRingState LinearM where
  getRingState := withRingM getRingState
  modifyRingState f := withRingM do modifyRingState f

instance : MonadGetVar LinearM where
  getVar x := return (← getRingState).vars[x]!

@[inline] def modifyStruct (f : Struct → Struct) : LinearM Unit := do
  let structId ← getStructId
  modify' fun s => { s with structs := s.structs.modify structId f }

end Lean.Meta.Grind.Arith.Linear
