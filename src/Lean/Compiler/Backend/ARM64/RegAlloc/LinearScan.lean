/-
Copyright (c) 2025 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Assistant
-/

module

prelude
public import Lean.Compiler.Backend.ARM64.Liveness
public import Lean.Compiler.Backend.ARM64.Affinity
public import Init.Control.State

public section

namespace Lean.Compiler.Backend.ARM64.RegAlloc

/-!
# Linear Scan Register Allocation

This module implements linear scan register allocation following
oxcaml's regalloc_ls pattern with improvements:

1. Proper live interval handling (not conservative all-live)
2. Affinity-guided register selection
3. Better spill heuristics based on use/def frequency
4. Separate GP and FP allocation pools
-/

open Lean.IR

/-- Allocation state for linear scan -/
structure AllocState where
  /-- Current position in the linear scan -/
  currentPos : Nat
  /-- Map from variable index to allocated physical register -/
  allocation : Std.TreeMap Index PhysReg (fun a b => compare a b)
  /-- Active intervals (currently live and in registers), sorted by end point -/
  activeGP : Array LiveInterval
  activeFP : Array LiveInterval
  /-- Available callee-saved GP registers (x19-x28) -/
  freeGPCalleeSaved : Array PhysReg
  /-- Available caller-saved GP registers (x11-x15) -/
  freeGPCallerSaved : Array PhysReg
  /-- Available FP registers -/
  freeFP : Array PhysReg
  /-- Spilled variables -/
  spilled : Array VarId
  /-- Stack slots for spilled variables -/
  stackSlots : Std.TreeMap Index Nat (fun a b => compare a b)
  /-- Next available stack slot -/
  nextStackSlot : Nat
  /-- Affinity information for register preference -/
  affinity : Affinity
  /-- Call positions for determining if intervals span calls -/
  callPositions : Array InstrPos
  /-- Free spill slots available for reuse -/
  freeSpillSlots : Array Nat
  /-- Active spilled intervals (for slot reuse tracking), sorted by end point -/
  activeSpilled : Array LiveInterval
  /-- Parameter variable indices (protected from spilling) -/
  paramVars : Array Index
  /-- Rematerializable constants: variables that hold small constants
      and don't need stack slots (can be recomputed with single instruction) -/
  rematerializable : Std.TreeMap Index UInt64 (fun a b => compare a b) := {}
  deriving Inhabited

namespace AllocState

/-- Initialize allocation state -/
def init (affinity : Affinity) (callPositions : Array InstrPos)
    (rematerializable : Std.TreeMap Index UInt64 (fun a b => compare a b) := {}) : AllocState := {
  currentPos := 0,
  allocation := {},
  activeGP := #[],
  activeFP := #[],
  freeGPCalleeSaved := RegClass.allocatableGPCalleeSaved,
  freeGPCallerSaved := RegClass.allocatableGPCallerSaved,
  freeFP := RegClass.allocatableFP,
  spilled := #[],
  stackSlots := {},
  nextStackSlot := 0,
  affinity,
  callPositions,
  freeSpillSlots := #[],
  activeSpilled := #[],
  paramVars := #[],
  rematerializable
}

/-- Check if an interval spans any function call. -/
def spansCall (s : AllocState) (iv : LiveInterval) : Bool :=
  let start := iv.start
  let end_ := iv.end_
  s.callPositions.any fun callPos => start <= callPos && callPos < end_

/-- Check if a variable is spilled -/
def isSpilled (s : AllocState) (v : VarId) : Bool :=
  s.spilled.any (·.idx == v.idx)

/-- Get physical register for a variable -/
def getPhysReg (s : AllocState) (v : VarId) : Option PhysReg :=
  s.allocation.get? v.idx

/-- Get stack slot for a spilled variable -/
def getStackSlot (s : AllocState) (v : VarId) : Option Nat :=
  s.stackSlots.get? v.idx

end AllocState

abbrev AllocM := StateM AllocState

/-- Expire old intervals that end before current position -/
def expireOldIntervals (pos : Nat) : AllocM Unit := do
  let s ← get

  -- Expire GP intervals
  let (expiredGP, activeGP) := s.activeGP.partition (·.end_ < pos)
  for iv in expiredGP do
    match s.allocation.get? iv.var.idx with
    | some reg =>
      -- Return register to appropriate pool based on whether it's callee-saved
      if RegClass.gpCalleeSaved.contains reg then
        modify fun s => { s with freeGPCalleeSaved := s.freeGPCalleeSaved.push reg }
      else if RegClass.allocatableGPCallerSaved.contains reg then
        modify fun s => { s with freeGPCallerSaved := s.freeGPCallerSaved.push reg }
    | none => pure ()

  -- Expire FP intervals
  let (expiredFP, activeFP) := s.activeFP.partition (·.end_ < pos)
  for iv in expiredFP do
    match s.allocation.get? iv.var.idx with
    | some reg => modify fun s => { s with freeFP := s.freeFP.push reg }
    | none => pure ()

  -- Expire spilled intervals and return slots to free pool
  let s ← get
  let (expiredSpilled, activeSpilled) := s.activeSpilled.partition (·.end_ < pos)
  for iv in expiredSpilled do
    if iv.ty.isScalar then
      match s.stackSlots.get? iv.var.idx with
      | some slot => modify fun s => { s with freeSpillSlots := s.freeSpillSlots.push slot }
      | none => pure ()

  modify fun s => { s with activeGP, activeFP, activeSpilled }

/-- Try to allocate a free register for an interval -/
def tryAllocateFree (iv : LiveInterval) : AllocM (Option PhysReg) := do
  let s ← get
  let usesFP := iv.ty.isScalar && (iv.ty == .float || iv.ty == .float32)

  if usesFP then
    -- FP allocation unchanged
    let pool := s.freeFP
    if pool.isEmpty then return none

    let bestReg := s.affinity.bestRegister iv.var pool s.allocation
    match bestReg with
    | some reg =>
      modify fun s => {
        s with
        freeFP := pool.filter (· != reg),
        allocation := s.allocation.insert iv.var.idx reg,
        activeFP := (s.activeFP.push iv).qsort (·.end_ < ·.end_)
      }
      return some reg
    | none =>
      let reg := pool[0]!
      modify fun s => {
        s with
        freeFP := pool.erase reg,
        allocation := s.allocation.insert iv.var.idx reg,
        activeFP := (s.activeFP.push iv).qsort (·.end_ < ·.end_)
      }
      return some reg
  else
    -- GP allocation: prefer caller-saved (x11-x15) for non-call-spanning intervals
    -- to save stack space (callee-saved regs must be pushed to stack in prologue).
    -- If it spans a call, we MUST use callee-saved or it will be clobbered.
    let spansCall := s.spansCall iv
    let pool := if spansCall then
      s.freeGPCalleeSaved
    else
      s.freeGPCallerSaved ++ s.freeGPCalleeSaved

    if pool.isEmpty then return none

    let bestReg := s.affinity.bestRegister iv.var pool s.allocation
    match bestReg with
    | some reg =>
      modify fun s => {
        s with
        freeGPCalleeSaved := s.freeGPCalleeSaved.filter (· != reg),
        freeGPCallerSaved := s.freeGPCallerSaved.filter (· != reg),
        allocation := s.allocation.insert iv.var.idx reg,
        activeGP := (s.activeGP.push iv).qsort (·.end_ < ·.end_)
      }
      return some reg
    | none =>
      let reg := pool[0]!
      modify fun s => {
        s with
        freeGPCalleeSaved := s.freeGPCalleeSaved.filter (· != reg),
        freeGPCallerSaved := s.freeGPCallerSaved.filter (· != reg),
        allocation := s.allocation.insert iv.var.idx reg,
        activeGP := (s.activeGP.push iv).qsort (·.end_ < ·.end_)
      }
      return some reg

/-- Allocate a stack slot for a spill, reusing freed scalar slots when possible. -/
def allocateSpillSlot (ty : IRType) : AllocM Nat := do
  let s ← get
  if ty.isScalar then
    match s.freeSpillSlots.back? with
    | some slot =>
      modify fun s => { s with freeSpillSlots := s.freeSpillSlots.pop }
      return slot
    | none => pure ()
  let slot := s.nextStackSlot
  modify fun s => { s with nextStackSlot := s.nextStackSlot + 1 }
  return slot

/-- Spill the current interval -/
def spillInterval (iv : LiveInterval) : AllocM Unit := do
  let s ← get
  -- Check if this variable is rematerializable (holds a small constant)
  -- If so, we mark it as spilled but DON'T allocate a stack slot
  -- The lowering phase will regenerate the constant instead of loading from stack
  if s.rematerializable.contains iv.var.idx then
    modify fun s => {
      s with
      spilled := s.spilled.push iv.var,
      -- No stack slot needed - constant will be rematerialized
      activeSpilled := (s.activeSpilled.push iv).qsort (·.end_ < ·.end_)
    }
    return
  -- Allocate a stack slot (reuse a freed slot if possible)
  let slot ← allocateSpillSlot iv.ty
  modify fun s => {
    s with
    spilled := s.spilled.push iv.var,
    stackSlots := s.stackSlots.insert iv.var.idx slot,
    -- Track this interval as active spilled for slot reuse
    activeSpilled := (s.activeSpilled.push iv).qsort (·.end_ < ·.end_)
  }

/-- Find interval to spill (one with latest end point, excluding parameters) -/
def findSpillCandidate (iv : LiveInterval) : AllocM (Option LiveInterval) := do
  let s ← get
  let usesFP := iv.ty.isScalar && (iv.ty == .float || iv.ty == .float32)
  let active := if usesFP then s.activeFP else s.activeGP

  -- Filter out parameters - they should never be spilled
  let spillable := active.filter fun cur => !s.paramVars.contains cur.var.idx

  if spillable.isEmpty then return none

  -- Find interval with latest end point among spillable candidates
  let candidate := spillable.foldl (fun best cur =>
    if cur.end_ > best.end_ then cur else best
  ) spillable[0]!

  -- Only spill if candidate ends later than current
  return if candidate.end_ > iv.end_ then some candidate else none

/-- Allocate blocked register (spill another interval) -/
def allocateBlocked (iv : LiveInterval) : AllocM Unit := do
  match ← findSpillCandidate iv with
  | some victim =>
    -- Spill the victim instead of current
    let s ← get
    let usesFP := iv.ty.isScalar && (iv.ty == .float || iv.ty == .float32)

    match s.allocation.get? victim.var.idx with
    | some reg =>
      -- Check if this register is safe for iv
      let ivSpansCall := s.spansCall iv
      let regIsCallerSaved := RegClass.allocatableGPCallerSaved.contains reg
      if ivSpansCall && regIsCallerSaved then
        -- Cannot use this caller-saved register for an interval that spans a call
        spillInterval iv
        return

      -- Check if victim is rematerializable (no stack slot needed)
      if s.rematerializable.contains victim.var.idx then
        modify fun s => {
          s with
          allocation := s.allocation.erase victim.var.idx |>.insert iv.var.idx reg,
          spilled := s.spilled.push victim.var,
          -- No stack slot for rematerializable
          activeGP := if usesFP then s.activeGP else s.activeGP.filter (·.var.idx != victim.var.idx) |>.push iv |>.qsort (·.end_ < ·.end_),
          activeFP := if usesFP then s.activeFP.filter (·.var.idx != victim.var.idx) |>.push iv |>.qsort (·.end_ < ·.end_) else s.activeFP,
          activeSpilled := (s.activeSpilled.push victim).qsort (·.end_ < ·.end_)
        }
      else
        -- Free the register from victim, allocate a stack slot (reuse if possible)
        let slot ← allocateSpillSlot victim.ty
        modify fun s => {
          s with
          allocation := s.allocation.erase victim.var.idx |>.insert iv.var.idx reg,
          spilled := s.spilled.push victim.var,
          stackSlots := s.stackSlots.insert victim.var.idx slot,
          activeGP := if usesFP then s.activeGP else s.activeGP.filter (·.var.idx != victim.var.idx) |>.push iv |>.qsort (·.end_ < ·.end_),
          activeFP := if usesFP then s.activeFP.filter (·.var.idx != victim.var.idx) |>.push iv |>.qsort (·.end_ < ·.end_) else s.activeFP,
          activeSpilled := (s.activeSpilled.push victim).qsort (·.end_ < ·.end_)
        }
    | none =>
      -- Victim not in register? Just spill current
      spillInterval iv
  | none =>
    -- No good candidate, spill current
    spillInterval iv

/-- Allocate a single interval -/
def allocateInterval (iv : LiveInterval) : AllocM Unit := do
  expireOldIntervals iv.start
  modify fun s => { s with currentPos := iv.start }
 
  -- Skip if already allocated (e.g., parameters pre-allocated by allocateParams)
  -- Add to active set so their registers are properly tracked for expiration
  let s ← get
  if s.allocation.contains iv.var.idx then
    -- Already allocated, add to active set for proper tracking
    let usesFP := iv.ty.isScalar && (iv.ty == .float || iv.ty == .float32)
    if usesFP then
      modify fun s => { s with activeFP := (s.activeFP.push iv).qsort (·.end_ < ·.end_) }
    else
      modify fun s => { s with activeGP := (s.activeGP.push iv).qsort (·.end_ < ·.end_) }
    return

  match ← tryAllocateFree iv with
  | some _ => pure ()  -- Successfully allocated
  | none => allocateBlocked iv  -- Need to spill

/-- Pre-allocate function parameters to registers.
    Parameters use callee-saved registers since they typically span calls. -/
def allocateParams (params : Array Param) : AllocM Unit := do
  let mut gpIdx := 0
  let mut fpIdx := 0

  for param in params do
    -- Track all params as protected from spilling
    modify fun s => { s with paramVars := s.paramVars.push param.x.idx }

    let isFloat := param.ty == .float || param.ty == .float32
    if isFloat then
      if fpIdx < RegClass.fpCalleeSaved.size then
        let reg := RegClass.fpCalleeSaved[fpIdx]!
        modify fun s => {
          s with
          allocation := s.allocation.insert param.x.idx reg,
          freeFP := s.freeFP.filter (· != reg)
        }
        fpIdx := fpIdx + 1
      else
        -- Spill parameter to stack
        let slot := (← get).nextStackSlot
        modify fun s => {
          s with
          spilled := s.spilled.push param.x,
          stackSlots := s.stackSlots.insert param.x.idx slot,
          nextStackSlot := s.nextStackSlot + 1
        }
    else
      -- Use callee-saved registers for parameters (they typically span calls)
      if gpIdx < RegClass.allocatableGPCalleeSaved.size then
        let reg := RegClass.allocatableGPCalleeSaved[gpIdx]!
        modify fun s => {
          s with
          allocation := s.allocation.insert param.x.idx reg,
          freeGPCalleeSaved := s.freeGPCalleeSaved.filter (· != reg)
        }
        gpIdx := gpIdx + 1
      else
        -- Spill parameter to stack
        let slot := (← get).nextStackSlot
        modify fun s => {
          s with
          spilled := s.spilled.push param.x,
          stackSlots := s.stackSlots.insert param.x.idx slot,
          nextStackSlot := s.nextStackSlot + 1
        }

/-- Main linear scan allocation -/
def linearScan (intervals : Array LiveInterval) : AllocM Unit := do
  -- Sort intervals by start position
  let sorted := intervals.qsort (·.start < ·.start)

  for iv in sorted do
    allocateInterval iv

/-- Run register allocation on a function -/
def allocateRegisters (params : Array Param) (liveness : LivenessInfo) (affinity : Affinity)
    : AllocState := Id.run do
  let initState := AllocState.init affinity liveness.callPositions liveness.rematerializable

  let (_, state) := (do
    allocateParams params
    linearScan liveness.intervals
  ).run initState

  return state

/-- Get the set of callee-saved GP registers actually used in allocation -/
def AllocState.usedCalleeSavedGP (s : AllocState) : Array PhysReg :=
  let calleeSaved := RegClass.gpCalleeSaved
  calleeSaved.filter fun reg =>
    s.allocation.any fun _ allocReg => allocReg == reg

/-- Get the set of callee-saved FP registers actually used in allocation -/
def AllocState.usedCalleeSavedFP (s : AllocState) : Array PhysReg :=
  let calleeSaved := RegClass.fpCalleeSaved
  calleeSaved.filter fun reg =>
    s.allocation.any fun _ allocReg => allocReg == reg

end Lean.Compiler.Backend.ARM64.RegAlloc

end
