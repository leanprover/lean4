/-
Copyright (c) 2025 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Assistant
-/

module

prelude
public import Lean.Compiler.Backend.ARM64.Lower.Base

public section

namespace Lean.Compiler.Backend.ARM64.Lower.Projection

/-!
# Projection Lowering

Handles field access operations:
- .proj: Object field projection
- .uproj: USize field projection
- .sproj: Scalar field projection
-/

open Lean.IR
open Lean.Compiler.Backend.ARM64

/-- Lower .proj (object field access) -/
def lowerProj (dst : VarId) (idx : Nat) (x : VarId) : SelectM Unit := do
  let xReg ← varToReg x
  let (dstReg, isSpilled) ← getDstReg dst
  emitComment s!"proj field {idx}"
  -- Layout: [RC:4, tag:4, field0:8, field1:8, ...]
  let offset := 8 + idx * 8
  emit (Instr.ldr dstReg (.mem xReg (Int.ofNat offset)))
  if isSpilled then
    storeSpilledDst dst dstReg
  releaseAllScratch

/-- Lower .uproj (usize field access) -/
def lowerUProj (dst : VarId) (idx : Nat) (x : VarId) : SelectM Unit := do
  let xReg ← varToReg x
  let (dstReg, isSpilled) ← getDstReg dst
  let offset := 8 + idx * 8
  emit (Instr.ldr dstReg (.mem xReg (Int.ofNat offset)))
  if isSpilled then
    storeSpilledDst dst dstReg
  releaseAllScratch

/-- Lower .sproj (scalar field access) -/
def lowerSProj (dst : VarId) (n : Nat) (offset : Nat) (x : VarId) : SelectM Unit := do
  let xReg ← varToReg x
  let (dstReg, isSpilled) ← getDstReg dst
  let dstType ← getVarType dst
  -- Scalar offset: 8 (header) + n * 8 (usize fields) + offset
  let totalOffset := 8 + n * 8 + offset
  match dstType with
  | some .uint8 =>
    emit (Instr.ldrb dstReg (.mem xReg (Int.ofNat totalOffset)))
  | some .uint16 =>
    emit (Instr.ldrh dstReg (.mem xReg (Int.ofNat totalOffset)))
  | some .uint32 =>
    emit (Instr.ldrw dstReg (.mem xReg (Int.ofNat totalOffset)))
  | some .float32 =>
    emit (Instr.ldrs dstReg (.mem xReg (Int.ofNat totalOffset)))
  | some .float =>
    emit (Instr.ldrd dstReg (.mem xReg (Int.ofNat totalOffset)))
  | _ =>
    emit (Instr.ldr dstReg (.mem xReg (Int.ofNat totalOffset)))
  if isSpilled then
    storeSpilledDst dst dstReg
  releaseAllScratch

end Lean.Compiler.Backend.ARM64.Lower.Projection

end
