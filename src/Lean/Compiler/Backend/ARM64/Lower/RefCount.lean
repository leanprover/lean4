/-
Copyright (c) 2025 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Assistant
-/

module

prelude
public import Lean.Compiler.Backend.ARM64.Lower.Base

public section

namespace Lean.Compiler.Backend.ARM64.Lower.RefCount

/-!
# Reference Counting Lowering

Handles reference counting operations:
- .inc: Increment reference count
- .dec: Decrement reference count
- .del: Delete (decrement and potentially free)
-/

open Lean.IR
open Lean.Compiler.Backend.ARM64

/-- Check if a variable is a scalar type (no refcounting needed) -/
def isScalarVar (x : VarId) : SelectM Bool := do
  match ← getVarType x with
  | some ty => return ty.isScalar
  | none => return false

/-- Lower .inc instruction -/
def lowerInc (x : VarId) (n : Nat) (checkShared : Bool) (persistent : Bool) : SelectM Unit := do
  -- Skip for persistent, zero count, or scalar types
  if persistent || n == 0 || (← isScalarVar x) then return

  emitComment s!"inc {n}"
  let ptrReg ← varToReg x

  let rtName := if checkShared then
    if n == 1 then "lean_inc" else "lean_inc_n"
  else
    if n == 1 then "lean_inc_ref" else "lean_inc_ref_n"

  emit (Instr.mov (.phys .x0) (.reg ptrReg))
  if n != 1 then
    loadImm64 (.phys .x1) n
  emit (Instr.bl rtName)
  releaseAllScratch

/-- Lower .dec instruction -/
def lowerDec (x : VarId) (n : Nat) (checkShared : Bool) (persistent : Bool) : SelectM Unit := do
  -- Skip for persistent, zero count, or scalar types
  if persistent || n == 0 || (← isScalarVar x) then return

  emitComment s!"dec {n}"
  let ptrReg ← varToReg x

  let rtName := if checkShared then "lean_dec" else "lean_dec_ref"

  if n == 1 then
    emit (Instr.mov (.phys .x0) (.reg ptrReg))
    emit (Instr.bl rtName)
  else
    -- Loop for multiple decrements
    let loopLabel ← freshLabel "dec_loop"
    loadImm64 (.phys .x1) n
    emit (Instr.label loopLabel)
    emit (Instr.mov (.phys .x0) (.reg ptrReg))
    emit (Instr.bl rtName)
    emit (Instr.sub (.phys .x1) (.phys .x1) (.imm 1))
    emit (Instr.cmp (.phys .x1) (.imm 0))
    emit (Instr.bCond .gt loopLabel)

  releaseAllScratch

/-- Lower .del instruction -/
def lowerDel (x : VarId) : SelectM Unit := do
  let xReg ← varToReg x
  emitComment "del"
  emit (Instr.mov (.phys .x0) (.reg xReg))
  emit (Instr.bl "lean_free_object")
  releaseAllScratch

end Lean.Compiler.Backend.ARM64.Lower.RefCount

end
