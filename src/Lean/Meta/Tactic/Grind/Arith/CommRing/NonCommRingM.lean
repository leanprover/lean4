/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
public section
namespace Lean.Meta.Grind.Arith.CommRing

structure NonCommRingM.Context where
  ringId : Nat

/-- We don't want to keep carrying the `RingId` around. -/
abbrev NonCommRingM := ReaderT NonCommRingM.Context GoalM

abbrev NonCommRingM.run (ringId : Nat) (x : NonCommRingM α) : GoalM α :=
  x { ringId }

instance : MonadCanon NonCommRingM where
  canonExpr e := do shareCommon (← canon e)
  synthInstance? e := Grind.synthInstance? e

protected def NonCommRingM.getRing : NonCommRingM Ring := do
  let s ← get'
  let ringId := (← read).ringId
  if h : ringId < s.ncRings.size then
    return s.ncRings[ringId]
  else
    throwError "`grind` internal error, invalid ringId"

protected def NonCommRingM.modifyRing (f : Ring → Ring) : NonCommRingM Unit := do
  let ringId := (← read).ringId
  modify' fun s => { s with ncRings := s.ncRings.modify ringId f }

instance : MonadRing NonCommRingM where
  getRing := NonCommRingM.getRing
  modifyRing := NonCommRingM.modifyRing

instance : MonadMarkTerm NonCommRingM where
  -- **Note**: We only normalize non commutative ring terms. So, we don't need the mark terms
  markTerm _ := return ()

end Lean.Meta.Grind.Arith.CommRing
