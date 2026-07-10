/-
Copyright (c) 2025 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Assistant
-/

module

prelude
public import Lean.Compiler.Backend.ARM64.Lower.Base

public section

namespace Lean.Compiler.Backend.ARM64.Lower.Inline

/-!
# Inline External Call Lowering

Handles inlining of selected Lean runtime helper calls that are provided
only as C header inlines. These are performance-critical operations that
benefit from direct code generation rather than function calls.

Categories:
- Scalar boxing/unboxing (lean_box, lean_unbox)
- Integer arithmetic (uint32, uint64, usize add/sub/mul)
- Floating-point arithmetic
- Type predicates (is_scalar, is_shared)
- IO operations
-/

open Lean.IR
open Lean.Compiler.Backend.ARM64

/-- Convert argument to register, using zero register for erased args -/
def argToRegOrZero (arg : Arg) : SelectM Reg := do
  match arg with
  | .var v => varToReg v
  | .erased => return .phys PhysReg.xzr

/-- Inline lean_box -/
def inlineBox (args : Array Arg) (dstReg : Reg) : SelectM Bool := do
  if args.size == 1 then
    match args[0]! with
    | .var v =>
      let vReg ← varToReg v
      emitComment "call lean_box_export"
      emitMove (.phys PhysReg.x0) (.reg vReg)
      emit (Instr.bl "lean_box_export")
      if dstReg != .phys PhysReg.x0 then
        emitMove dstReg (.reg (.phys PhysReg.x0))
    | .erased =>
      emitComment "lean_box(erased)"
      emit (Instr.mov dstReg (.imm 1))
    return true
  else
    return false

/-- Inline lean_unbox -/
def inlineUnbox (args : Array Arg) (dstReg : Reg) : SelectM Bool := do
  if args.size == 1 then
    match args[0]! with
    | .var v =>
      let vReg ← varToReg v
      emitComment "call lean_unbox_export"
      emitMove (.phys PhysReg.x0) (.reg vReg)
      emit (Instr.bl "lean_unbox_export")
      if dstReg != .phys PhysReg.x0 then
        emitMove dstReg (.reg (.phys PhysReg.x0))
    | .erased =>
      emitComment "lean_unbox(erased)"
      emit (Instr.mov dstReg (.imm 0))
    return true
  else
    return false

/-- Inline lean_unbox_uint32 -/
def inlineUnboxUint32 (args : Array Arg) (dstReg : Reg) : SelectM Bool := do
  if args.size == 1 then
    match args[0]! with
    | .var v =>
      let vReg ← varToReg v
      emitComment "inline lean_unbox_uint32"
      emit (Instr.lsr dstReg vReg (.imm 1))
    | .erased =>
      emitComment "inline lean_unbox_uint32(erased)"
      emit (Instr.mov dstReg (.imm 0))
    return true
  else
    return false

/-- Inline lean_is_scalar -/
def inlineIsScalar (args : Array Arg) (dstReg : Reg) : SelectM Bool := do
  if args.size == 1 then
    match args[0]! with
    | .var v =>
      let vReg ← varToReg v
      emitComment "inline lean_is_scalar"
      emit (Instr.and dstReg vReg (.imm 1))
    | .erased =>
      emitComment "inline lean_is_scalar(erased)"
      emit (Instr.mov dstReg (.imm 0))
    return true
  else
    return false

/-- Inline lean_io_mk_world -/
def inlineIoMkWorld (args : Array Arg) (dstReg : Reg) : SelectM Bool := do
  if args.isEmpty then
    emitComment "inline lean_io_mk_world"
    emit (Instr.mov dstReg (.imm 1))
    return true
  else
    return false

/-- Inline lean_io_result_is_ok -/
def inlineIoResultIsOk (args : Array Arg) (dstReg : Reg) : SelectM Bool := do
  if args.size == 1 then
    match args[0]! with
    | .var v =>
      let vReg ← varToReg v
      emitComment "inline lean_io_result_is_ok"
      emit (Instr.ldrb dstReg (.mem vReg 7))
      emit (Instr.cmp dstReg (.imm 0))
      emit (Instr.mov dstReg (.imm 1))
      emit (Instr.csel dstReg dstReg (.phys PhysReg.xzr) Cond.eq)
    | .erased =>
      emitComment "inline lean_io_result_is_ok(erased)"
      emit (Instr.mov dstReg (.imm 0))
    return true
  else
    return false

/-- Inline uint64 binary operation -/
def inlineUint64BinOp (op : String) (args : Array Arg) (dstReg : Reg)
    (emitOp : Reg → Reg → Reg → SelectM Unit) : SelectM Bool := do
  if args.size == 2 then
    let lhsReg ← argToRegOrZero args[0]!
    let rhsReg ← argToRegOrZero args[1]!
    emitComment s!"inline lean_{op}"
    emitOp dstReg lhsReg rhsReg
    releaseAllScratch
    return true
  else
    return false

/-- Inline uint32 binary operation with truncation -/
def inlineUint32BinOp (op : String) (args : Array Arg) (dstReg : Reg)
    (emitOp : Reg → Reg → Reg → SelectM Unit) : SelectM Bool := do
  if args.size == 2 then
    let lhs ← argToRegOrZero args[0]!
    let rhs ← argToRegOrZero args[1]!
    emitComment s!"inline lean_{op}"
    emitOp dstReg lhs rhs
    -- Truncate to 32 bits
    let scratch ← acquireScratch
    loadImm64 (.phys scratch) 0xFFFF_FFFF
    emit (Instr.and dstReg dstReg (.reg (.phys scratch)))
    releaseAllScratch
    return true
  else
    return false

/-- Inline usize binary operation -/
def inlineUsizeBinOp (op : String) (args : Array Arg) (dstReg : Reg)
    (emitOp : Reg → Reg → Reg → SelectM Unit) : SelectM Bool := do
  if args.size == 2 then
    let lhs ← argToRegOrZero args[0]!
    let rhs ← argToRegOrZero args[1]!
    emitComment s!"inline lean_{op}"
    emitOp dstReg lhs rhs
    releaseAllScratch
    return true
  else
    return false

/-- Inline floating-point binary operation -/
def inlineFloatBinOp (prec : FloatPrec) (op : String) (args : Array Arg) (dstReg : Reg)
    (emitOp : FloatPrec → Reg → Reg → Reg → SelectM Unit) : SelectM Bool := do
  if args.size == 2 then
    match args[0]!, args[1]! with
    | .var v1, .var v2 =>
      let v1Reg ← varToReg v1
      let v2Reg ← varToReg v2
      emitComment s!"inline lean_float_{op}"
      emitOp prec dstReg v1Reg v2Reg
      return true
    | _, _ => return false
  else
    return false

/-- Inline floating-point unary operation -/
def inlineFloatUnaryOp (prec : FloatPrec) (op : String) (args : Array Arg) (dstReg : Reg)
    (emitOp : FloatPrec → Reg → Reg → SelectM Unit) : SelectM Bool := do
  if args.size == 1 then
    match args[0]! with
    | .var v =>
      let vReg ← varToReg v
      emitComment s!"inline lean_float_{op}"
      emitOp prec dstReg vReg
      return true
    | .erased => return false
  else
    return false

/-- Inline floating-point comparison -/
def inlineFloatCmp (prec : FloatPrec) (cond : Cond) (args : Array Arg) (dstReg : Reg) : SelectM Bool := do
  if args.size == 2 then
    match args[0]!, args[1]! with
    | .var v1, .var v2 =>
      let v1Reg ← varToReg v1
      let v2Reg ← varToReg v2
      emitComment "inline float comparison"
      emit (Instr.fcmp prec v1Reg v2Reg)
      -- Returns decidable: isTrue (boxed 0) or isFalse (boxed 1)
      emit (Instr.cset dstReg cond)                 -- 1 if true, 0 otherwise
      emit (Instr.eor dstReg dstReg (.imm 1))       -- invert
      emit (Instr.lsl dstReg dstReg (.imm 1))       -- 0 or 2
      emit (Instr.add dstReg dstReg (.imm 1))       -- 1 or 3
      return true
    | _, _ => return false
  else
    return false

/-- Inline float equality -/
def inlineFloatBeq (prec : FloatPrec) (args : Array Arg) (dstReg : Reg) : SelectM Bool := do
  if args.size == 2 then
    match args[0]!, args[1]! with
    | .var v1, .var v2 =>
      let v1Reg ← varToReg v1
      let v2Reg ← varToReg v2
      emitComment "inline lean_float_beq"
      emit (Instr.fcmp prec v1Reg v2Reg)
      -- Set result to 1 if equal, 0 otherwise
      emit (Instr.mov dstReg (.imm 1))
      emit (Instr.csel dstReg dstReg (.phys PhysReg.xzr) Cond.eq)
      return true
    | _, _ => return false
  else
    return false

/-- Inline lean_mk_empty_array_with_capacity -/
def inlineMkEmptyArrayWithCapacity (args : Array Arg) (dstReg : Reg) : SelectM Bool := do
  if args.size == 2 then
    emitComment "inline lean_mk_empty_array_with_capacity"
    match args[1]! with
    | .var v =>
      let capReg ← varToReg v
      let vType ← getVarType v
      let treatAsScalar := match vType with
        | some ty => ty.isScalar
        | none => false
      match capReg with
      | .phys r =>
        if r != PhysReg.x0 then
          emit (Instr.mov (.phys PhysReg.x0) (.reg capReg))
      | _ =>
        emit (Instr.mov (.phys PhysReg.x0) (.reg capReg))
      if treatAsScalar then
        emit (Instr.bl "_lean_unsigned_to_nat_export")
      emit (Instr.bl "_lean_mk_empty_array_with_capacity")
    | .erased =>
      emit (Instr.mov (.phys PhysReg.x0) (.imm 0))
      emit (Instr.bl "_lean_unsigned_to_nat_export")
      emit (Instr.bl "_lean_mk_empty_array_with_capacity")
    if dstReg != .phys PhysReg.x0 then
      emitMove dstReg (.reg (.phys PhysReg.x0))
    return true
  else
    return false

/-- Try to inline an external function call. Returns true if handled. -/
def tryInlineExternCall (fnName : String) (args : Array Arg) (dstReg : Reg) : SelectM Bool := do
  match fnName with
  | "_lean_box" => inlineBox args dstReg
  | "_lean_unbox" => inlineUnbox args dstReg
  | "_lean_unbox_uint32" => inlineUnboxUint32 args dstReg
  | "_lean_is_scalar" => inlineIsScalar args dstReg
  | "_lean_io_mk_world" => inlineIoMkWorld args dstReg
  | "_lean_io_result_is_ok" => inlineIoResultIsOk args dstReg

  | "_lean_mk_empty_array_with_capacity" => inlineMkEmptyArrayWithCapacity args dstReg

  -- uint64 operations
  | "_lean_uint64_add" =>
    inlineUint64BinOp "uint64_add" args dstReg fun dst lhs rhs => do
      emit (Instr.add dst lhs (.reg rhs))
  | "_lean_uint64_sub" =>
    inlineUint64BinOp "uint64_sub" args dstReg fun dst lhs rhs => do
      emit (Instr.sub dst lhs (.reg rhs))
  | "_lean_uint64_mul" =>
    inlineUint64BinOp "uint64_mul" args dstReg fun dst lhs rhs => do
      emit (Instr.mul dst lhs rhs)

  -- uint32 operations (need truncation)
  | "_lean_uint32_add" =>
    inlineUint32BinOp "uint32_add" args dstReg fun dst lhs rhs => do
      emit (Instr.add dst lhs (.reg rhs))
  | "_lean_uint32_sub" =>
    inlineUint32BinOp "uint32_sub" args dstReg fun dst lhs rhs => do
      emit (Instr.sub dst lhs (.reg rhs))
  | "_lean_uint32_mul" =>
    inlineUint32BinOp "uint32_mul" args dstReg fun dst lhs rhs => do
      emit (Instr.mul dst lhs rhs)

  -- usize operations
  | "_lean_usize_add" =>
    inlineUsizeBinOp "usize_add" args dstReg fun dst lhs rhs => do
      emit (Instr.add dst lhs (.reg rhs))
  | "_lean_usize_sub" =>
    inlineUsizeBinOp "usize_sub" args dstReg fun dst lhs rhs => do
      emit (Instr.sub dst lhs (.reg rhs))
  | "_lean_usize_mul" =>
    inlineUsizeBinOp "usize_mul" args dstReg fun dst lhs rhs => do
      emit (Instr.mul dst lhs rhs)

  -- Float operations
  | "lean_float_add" =>
    inlineFloatBinOp .double "add" args dstReg fun prec dst lhs rhs => do
      emit (Instr.fadd prec dst lhs rhs)
  | "lean_float_sub" =>
    inlineFloatBinOp .double "sub" args dstReg fun prec dst lhs rhs => do
      emit (Instr.fsub prec dst lhs rhs)
  | "lean_float_mul" =>
    inlineFloatBinOp .double "mul" args dstReg fun prec dst lhs rhs => do
      emit (Instr.fmul prec dst lhs rhs)
  | "lean_float_div" =>
    inlineFloatBinOp .double "div" args dstReg fun prec dst lhs rhs => do
      emit (Instr.fdiv prec dst lhs rhs)
  | "lean_float_negate" =>
    inlineFloatUnaryOp .double "negate" args dstReg fun prec dst src => do
      emit (Instr.fneg prec dst src)
  | "lean_float_beq" => inlineFloatBeq .double args dstReg
  | "lean_float_decLt" => inlineFloatCmp .double Cond.lt args dstReg
  | "lean_float_decLe" => inlineFloatCmp .double Cond.le args dstReg
  | "lean_float32_add" =>
    inlineFloatBinOp .single "add" args dstReg fun prec dst lhs rhs => do
      emit (Instr.fadd prec dst lhs rhs)
  | "lean_float32_sub" =>
    inlineFloatBinOp .single "sub" args dstReg fun prec dst lhs rhs => do
      emit (Instr.fsub prec dst lhs rhs)
  | "lean_float32_mul" =>
    inlineFloatBinOp .single "mul" args dstReg fun prec dst lhs rhs => do
      emit (Instr.fmul prec dst lhs rhs)
  | "lean_float32_div" =>
    inlineFloatBinOp .single "div" args dstReg fun prec dst lhs rhs => do
      emit (Instr.fdiv prec dst lhs rhs)
  | "lean_float32_negate" =>
    inlineFloatUnaryOp .single "negate" args dstReg fun prec dst src => do
      emit (Instr.fneg prec dst src)
  | "lean_float32_beq" => inlineFloatBeq .single args dstReg
  | "lean_float32_decLt" => inlineFloatCmp .single Cond.lt args dstReg
  | "lean_float32_decLe" => inlineFloatCmp .single Cond.le args dstReg

  | _ => return false

end Lean.Compiler.Backend.ARM64.Lower.Inline

end
