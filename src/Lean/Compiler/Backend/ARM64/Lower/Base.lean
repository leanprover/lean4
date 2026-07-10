/-
Copyright (c) 2025 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Assistant
-/

module

prelude
public import Lean.Compiler.Backend.ARM64
public import Lean.Compiler.Backend.ARM64.RegAlloc.LinearScan
public import Lean.Compiler.IR.Basic
public import Lean.Compiler.IR.SSA
public import Lean.Compiler.IR.CompilerM
public import Lean.Compiler.NameMangling
public import Lean.Runtime
public import Lean.Environment
public import Init.Control.State
public import Std.Data.TreeMap
import Init.Data.String.Modify

public section

namespace Lean.Compiler.Backend.ARM64.Lower

/-!
# Lowering Base Types and Utilities

This module provides the shared infrastructure for instruction lowering:
- SelectContext: read-only context for the current function
- InstrBuffer: mutable instruction accumulator
- SelectM: the lowering monad
- Common utilities for register access, spilling, etc.
-/

open Lean.IR
open Lean.Compiler.Backend.ARM64
open Lean.Compiler.Backend.ARM64.RegAlloc

/-- Read-only context for instruction selection -/
structure SelectContext where
  /-- Environment for looking up declarations -/
  env : Environment
  /-- Current function name -/
  fnName : Name
  /-- Function parameters -/
  params : Array Param
  /-- Function return type -/
  returnType : IRType
  /-- Register allocation result -/
  allocResult : AllocState
  /-- Variable types -/
  varTypes : Std.TreeMap Index IRType (fun a b => compare a b)
  /-- Stack spill bytes (aligned) -/
  spillBytes : Nat := 0
  /-- Optional temporary stack slot offset (bytes from sp) for lowering helpers. -/
  tempSlotOffset : Option Int := none
  /-- Callee-saved GP registers that are actually used (for dynamic save/restore) -/
  usedCalleeSavedGP : Array PhysReg := #[]
  /-- Callee-saved FP registers that are actually used (for dynamic save/restore) -/
  usedCalleeSavedFP : Array PhysReg := #[]
  /-- Whether this is a boxed wrapper function (needs all callee-saved regs) -/
  isBoxed : Bool := false

/-- Mutable instruction buffer -/
structure InstrBuffer where
  /-- Accumulated instructions -/
  instrs : Array Instr := #[]
  /-- Next label counter -/
  nextLabel : Nat := 0
  /-- String literals gathered -/
  stringLits : Array StringLiteral := #[]
  /-- Next string literal ID -/
  nextStringId : Nat := 0
  deriving Inhabited

/-- Join point tracking state -/
structure JoinPointState where
  /-- Map from join point ID to label -/
  jpLabels : Std.TreeMap Index String (fun a b => compare a b) := {}
  /-- Map from join point ID to parameter variables -/
  jpParams : Std.TreeMap Index (Array VarId) (fun a b => compare a b) := {}
  deriving Inhabited

/-- Scratch register pool -/
structure ScratchPool where
  /-- Available scratch registers -/
  available : Array PhysReg := RegClass.scratch
  /-- Currently in-use scratch registers -/
  inUse : Array PhysReg := #[]
  /-- Available FP scratch registers -/
  availableFP : Array PhysReg := RegClass.fpScratch
  /-- Currently in-use FP scratch registers -/
  inUseFP : Array PhysReg := #[]
  deriving Inhabited

/-- Combined state for instruction selection -/
structure SelectState where
  buffer : InstrBuffer := {}
  joinPoints : JoinPointState := {}
  scratch : ScratchPool := {}
  /-- Rematerializable constants: spilled variables that hold small constant values.
      Instead of loading from stack, we can regenerate the constant with movz.
      Maps VarId index to the tagged constant value. -/
  rematerializable : Std.TreeMap Index UInt64 (fun a b => compare a b) := {}
  deriving Inhabited

/-- The instruction selection monad -/
abbrev SelectM := ReaderT SelectContext (StateT SelectState Id)

/-!
## Basic Operations
-/

/-- Emit an instruction -/
def emit (i : Instr) : SelectM Unit :=
  modify fun s => { s with buffer := { s.buffer with instrs := s.buffer.instrs.push i } }

/-- Emit a comment -/
def emitComment (text : String) : SelectM Unit := emit (Instr.comment text)

/-- Sanitize a string for use in a label -/
def sanitizeForLabel (s : String) : String :=
  s.map fun c => if c.isAlphanum || c == '_' then c else '_'

/-- Get a fresh label -/
def freshLabel (labelPrefix : String := "L") : SelectM String := do
  let n := (← get).buffer.nextLabel
  modify fun s => { s with buffer := { s.buffer with nextLabel := n + 1 } }
  let fnName := (← read).fnName
  return s!".{labelPrefix}_{sanitizeForLabel fnName.toString}_{n}"

/-- Get environment -/
def getEnv : SelectM Environment := (·.env) <$> read

/-- Get function name -/
def getFnName : SelectM Name := (·.fnName) <$> read

/-- Get return type -/
def getReturnType : SelectM IRType := (·.returnType) <$> read

/-- Get allocation result -/
def getAllocResult : SelectM AllocState := (·.allocResult) <$> read

/-- Get spill bytes -/
def getSpillBytes : SelectM Nat := (·.spillBytes) <$> read

/-- Get optional temp stack slot offset. -/
def getTempSlotOffset : SelectM (Option Int) := (·.tempSlotOffset) <$> read

/-- Get used callee-saved GP registers -/
def getUsedCalleeSavedGP : SelectM (Array PhysReg) := (·.usedCalleeSavedGP) <$> read

/-- Get used callee-saved FP registers -/
def getUsedCalleeSavedFP : SelectM (Array PhysReg) := (·.usedCalleeSavedFP) <$> read

/-- Check if this is a boxed wrapper function -/
def getIsBoxed : SelectM Bool := (·.isBoxed) <$> read

/-- Get pairs of callee-saved registers to save/restore based on which are used -/
def getCalleeSavedPairs (usedGP : Array PhysReg) : Array (Array Reg) :=
  let pairs := #[
    (PhysReg.x19, PhysReg.x20),
    (PhysReg.x21, PhysReg.x22),
    (PhysReg.x23, PhysReg.x24),
    (PhysReg.x25, PhysReg.x26),
    (PhysReg.x27, PhysReg.x28)
  ]
  pairs.filterMap fun (r1, r2) =>
    if usedGP.contains r1 || usedGP.contains r2 then
      some #[Reg.phys r1, Reg.phys r2]
    else
      none

/-- Get pairs of callee-saved FP registers to save/restore based on which are used. -/
def getCalleeSavedFPPairs (usedFP : Array PhysReg) : Array (Array Reg) :=
  let pairs := #[
    (PhysReg.v8, PhysReg.v9),
    (PhysReg.v10, PhysReg.v11),
    (PhysReg.v12, PhysReg.v13),
    (PhysReg.v14, PhysReg.v15)
  ]
  pairs.filterMap fun (r1, r2) =>
    if usedFP.contains r1 || usedFP.contains r2 then
      some #[Reg.phys r1, Reg.phys r2]
    else
      none

/-- Get variable type -/
def getVarType (v : VarId) : SelectM (Option IRType) := do
  return (← read).varTypes.get? v.idx

/-- Register a new variable type (no-op in new architecture) -/
def registerVarType (_v : VarId) (_ty : IRType) : SelectM Unit := pure ()

/-!
## Scratch Register Management (defined early for use by other functions)
-/

/-- Acquire a scratch register -/
def acquireScratch : SelectM PhysReg := do
  let s ← get
  for r in s.scratch.available do
    if !s.scratch.inUse.contains r then
      modify fun s => { s with scratch := { s.scratch with inUse := s.scratch.inUse.push r } }
      return r
  -- Fallback
  return s.scratch.available[0]!

/- Acquire an FP scratch register -/
def acquireFPScratch : SelectM PhysReg := do
  let s ← get
  for r in s.scratch.availableFP do
    if !s.scratch.inUseFP.contains r then
      modify fun s => { s with scratch := { s.scratch with inUseFP := s.scratch.inUseFP.push r } }
      return r
  -- Fallback
  return s.scratch.availableFP[0]!

/-- Release a scratch register -/
def releaseScratch (r : PhysReg) : SelectM Unit :=
  if r.isFP then
    modify fun s => { s with scratch := { s.scratch with inUseFP := s.scratch.inUseFP.filter (· != r) } }
  else
    modify fun s => { s with scratch := { s.scratch with inUse := s.scratch.inUse.filter (· != r) } }

/-- Release all scratch registers -/
def releaseAllScratch : SelectM Unit :=
  modify fun s => { s with scratch := { s.scratch with inUse := #[], inUseFP := #[] } }

/-- Run action with automatic scratch release -/
def withScratchScope (action : SelectM α) : SelectM α := do
  let result ← action
  releaseAllScratch
  return result


/- Acquire scratch register appropriate for the IR type. -/
def acquireScratchForType (ty : IRType) : SelectM PhysReg := do
  if ty == .float || ty == .float32 then
    acquireFPScratch
  else
    acquireScratch

/-!
## Register Access
-/

/-- Load a spilled variable into a scratch register -/
def loadSpilledVar (v : VarId) : SelectM Reg := do
  let alloc ← getAllocResult
  let ty := (← read).varTypes.get? v.idx |>.getD .object
  -- Check if this variable is rematerializable (holds a small constant)
  match alloc.rematerializable.get? v.idx with
  | some constVal =>
    -- Rematerialize the constant instead of loading from stack
    let scratch ← acquireScratchForType ty
    emit (Instr.movz (.phys scratch) constVal.toNat 0)
    return .phys scratch
  | none =>
    match alloc.stackSlots.get? v.idx with
    | some slot =>
      let scratch ← acquireScratchForType ty
      let offset := slot * 8
      -- Choose appropriate load based on type
      if ty == .uint8 then
        emit (Instr.ldrb (.phys scratch) (.mem (.phys .sp) (Int.ofNat offset)))
      else if ty == .uint16 then
        emit (Instr.ldrh (.phys scratch) (.mem (.phys .sp) (Int.ofNat offset)))
      else if ty == .uint32 then
        emit (Instr.ldrw (.phys scratch) (.mem (.phys .sp) (Int.ofNat offset)))
      else if ty == .float32 then
        emit (Instr.ldrs (.phys scratch) (.mem (.phys .sp) (Int.ofNat offset)))
      else if ty == .float then
        emit (Instr.ldrd (.phys scratch) (.mem (.phys .sp) (Int.ofNat offset)))
      else
        emit (Instr.ldr (.phys scratch) (.mem (.phys .sp) (Int.ofNat offset)))
      return .phys scratch
    | none =>
      -- Variable not allocated - this can happen when liveness analysis misses a variable
      -- Use a scratch register as fallback
      let scratch ← acquireScratchForType ty
      emit (Instr.comment s!"WARNING: unallocated variable x{v.idx}, using scratch {scratch}")
      return .phys scratch

/-- Get the physical register for a variable (or handle spill) -/
def varToReg (v : VarId) : SelectM Reg := do
  let alloc ← getAllocResult
  match alloc.allocation.get? v.idx with
  | some phys => return .phys phys
  | none =>
    -- Variable is spilled, load into scratch register
    loadSpilledVar v

/-- Store a value to a spilled variable's stack slot -/
def storeToStackSlot (src : Reg) (slot : Nat) (ty : IRType) : SelectM Unit := do
  let offset := Int.ofNat (slot * 8)
  if ty == .uint8 then
    emit (Instr.strb src (.mem (.phys .sp) offset))
  else if ty == .uint16 then
    emit (Instr.strh src (.mem (.phys .sp) offset))
  else if ty == .uint32 then
    emit (Instr.strw src (.mem (.phys .sp) offset))
  else if ty == .float32 then
    emit (Instr.strs src (.mem (.phys .sp) offset))
  else if ty == .float then
    emit (Instr.strd src (.mem (.phys .sp) offset))
  else
    emit (Instr.str src (.mem (.phys .sp) offset))

/-- Get destination register for a variable (handles spill) -/
def getDstReg (v : VarId) : SelectM (Reg × Bool) := do
  let alloc ← getAllocResult
  match alloc.allocation.get? v.idx with
  | some phys => return (.phys phys, false)
  | none =>
    -- Destination is spilled, use scratch register
    let ty := (← read).varTypes.get? v.idx |>.getD .object
    let scratch ← acquireScratchForType ty
    return (.phys scratch, true)

/-- Store result if destination was spilled -/
def storeSpilledDst (v : VarId) (dstReg : Reg) : SelectM Unit := do
  let alloc ← getAllocResult
  let ty := (← read).varTypes.get? v.idx |>.getD .object
  match alloc.stackSlots.get? v.idx with
  | some slot => storeToStackSlot dstReg slot ty
  | none => pure ()

/-!
## Join Point Management
-/

/-- Get or create label for join point -/
def getJPLabel (j : JoinPointId) : SelectM String := do
  let s ← get
  match s.joinPoints.jpLabels.get? j.idx with
  | some lbl => return lbl
  | none =>
    let lbl ← freshLabel "JP"
    modify fun s => { s with joinPoints := { s.joinPoints with jpLabels := s.joinPoints.jpLabels.insert j.idx lbl } }
    return lbl

/-- Register join point parameters -/
def registerJPParams (j : JoinPointId) (params : Array VarId) : SelectM Unit :=
  modify fun s => { s with joinPoints := { s.joinPoints with jpParams := s.joinPoints.jpParams.insert j.idx params } }

/-- Get join point parameters -/
def getJPParams (j : JoinPointId) : SelectM (Option (Array VarId)) := do
  return (← get).joinPoints.jpParams.get? j.idx

/-!
## Argument Handling
-/

/-- Convert IR Arg to operand -/
def argToOperand (arg : Arg) : SelectM Operand := do
  match arg with
  | .var v => return .reg (← varToReg v)
  | .erased => return .imm 1  -- lean_box(0)

/-- Get GP argument register by index -/
def getArgReg (idx : Nat) : PhysReg := RegClass.getGPArgReg idx

/-- Get FP argument register by index -/
def getFPArgReg (idx : Nat) : PhysReg := RegClass.getFPArgReg idx

/-!
## Type Utilities
-/

/-- Convert IRType to FloatPrec -/
def typeToFloatPrec (ty : IRType) : FloatPrec :=
  match ty with
  | .float32 => .single
  | _ => .double

/-- Check if type is floating point -/
def isFloatType (ty : IRType) : Bool :=
  ty == .float || ty == .float32

/-!
## Move Emission
-/

/-- Emit a move instruction, choosing correct form based on register types -/
def emitMove (dst : Reg) (src : Operand) : SelectM Unit := do
  let alloc ← getAllocResult
  match src with
  | .reg srcReg =>
    let dstIsFP := match dst with
      | .phys p => p.isFP
      | .virt v => match alloc.allocation.get? v.idx with
        | some p => p.isFP | none => false
    let srcIsFP := match srcReg with
      | .phys p => p.isFP
      | .virt v => match alloc.allocation.get? v.idx with
        | some p => p.isFP | none => false
    if dstIsFP || srcIsFP then
      emit (Instr.fmov .double dst srcReg)
    else
      emit (Instr.mov dst src)
  | _ =>
    emit (Instr.mov dst src)

/-- Load a 64-bit immediate into a register -/
def loadImm64 (dst : Reg) (value : Nat) : SelectM Unit := do
  if value < 65536 then
    emit (Instr.movz dst value 0)
  else if value < (1 <<< 32) then
    emit (Instr.movz dst (value &&& 0xFFFF) 0)
    if (value >>> 16) != 0 then
      emit (Instr.movk dst ((value >>> 16) &&& 0xFFFF) 16)
  else
    emit (Instr.movz dst (value &&& 0xFFFF) 0)
    if ((value >>> 16) &&& 0xFFFF) != 0 then
      emit (Instr.movk dst ((value >>> 16) &&& 0xFFFF) 16)
    if ((value >>> 32) &&& 0xFFFF) != 0 then
      emit (Instr.movk dst ((value >>> 32) &&& 0xFFFF) 32)
    if ((value >>> 48) &&& 0xFFFF) != 0 then
      emit (Instr.movk dst ((value >>> 48) &&& 0xFFFF) 48)

/-- Adjust stack pointer by a positive byte count (add/sub), using a scratch if needed. -/
def emitStackAdjust (isAdd : Bool) (bytes : Nat) : SelectM Unit := do
  if bytes == 0 then
    return
  if bytes <= 4095 then
    if isAdd then
      emit (Instr.add (.phys PhysReg.sp) (.phys PhysReg.sp) (.imm (Int.ofNat bytes)))
    else
      emit (Instr.sub (.phys PhysReg.sp) (.phys PhysReg.sp) (.imm (Int.ofNat bytes)))
  else
    let scratch := Reg.phys PhysReg.x16
    loadImm64 scratch bytes
    if isAdd then
      emit (Instr.add (.phys PhysReg.sp) (.phys PhysReg.sp) (.reg scratch))
    else
      emit (Instr.sub (.phys PhysReg.sp) (.phys PhysReg.sp) (.reg scratch))

/-- Convenience: subtract from stack pointer by byte count. -/
def emitStackSub (bytes : Nat) : SelectM Unit :=
  emitStackAdjust false bytes

/-- Convenience: add to stack pointer by byte count. -/
def emitStackAdd (bytes : Nat) : SelectM Unit :=
  emitStackAdjust true bytes

end Lean.Compiler.Backend.ARM64.Lower

end
