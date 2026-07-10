/-
Copyright (c) 2025 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Pehle
-/
module

prelude
public import Lean.Compiler.Backend.ARM64
public import Lean.Compiler.Backend.ARM64.Lower.Base
public import Lean.Compiler.Backend.ARM64.Lower.Constructor
public import Lean.Compiler.Backend.ARM64.Lower.Projection
public import Lean.Compiler.Backend.ARM64.Lower.RefCount
public import Lean.Compiler.Backend.ARM64.Lower.Call
public import Lean.Compiler.Backend.ARM64.Lower.Inline
public import Lean.Compiler.Backend.ARM64.Lower.Control
public import Lean.Compiler.Backend.ARM64.Liveness
public import Lean.Compiler.Backend.ARM64.Affinity
public import Lean.Compiler.Backend.ARM64.RegAlloc.LinearScan
public import Lean.Compiler.ExportAttr
public import Lean.Compiler.IR.SSA
public import Lean.Compiler.IR.Basic
public import Lean.Compiler.IR.CompilerM
public import Lean.Compiler.IR.EmitUtil
public import Lean.Compiler.LCNF.Types
public import Lean.Compiler.NameMangling
public import Lean.Runtime
public import Std.Data.TreeMap
import Init.Data.String.Modify

public section

namespace Lean.Compiler.Backend
namespace InstrSelect

open Lean.IR
open Lean.Compiler.Backend.ARM64
open Lean.Compiler.Backend.ARM64.Lower
open Lean.Compiler.Backend.ARM64.RegAlloc

/-!
# Instruction Selection Orchestrator

This module provides the main entry point for ARM64 instruction selection.
It delegates actual lowering to the modular Lower/ modules:
- Constructor: .ctor, .reset, .reuse
- Projection: .proj, .uproj, .sproj
- RefCount: .inc, .dec, .del
- Call: .fap, .pap, .ap, .box, .unbox, .lit
- Inline: inline extern optimizations
- Control: .case, .ret, .jmp, .jdecl, control flow
-/

/-- Remove the "_boxed" suffix from a function name -/
def stripBoxedSuffix (n : Name) : Name :=
  match n with
  | Name.str pre s => if s == "_boxed" then pre else n
  | _ => n

/-- Sanitize a string for use in a label -/
def sanitizeForLabel' (s : String) : String :=
  s.map fun c => if c.isAlphanum || c == '_' then c else '_'

/-- Get argument register by index -/
def getArgReg (idx : Nat) : PhysReg := RegClass.getGPArgReg idx

/-- Get FP argument register by index -/
def getFPArgReg (idx : Nat) : PhysReg := RegClass.getFPArgReg idx

/-- Convert IRType to FloatPrec -/
def typeToFloatPrec (ty : IRType) : FloatPrec :=
  match ty with
  | .float32 => FloatPrec.single
  | _ => FloatPrec.double

/-!
## Main Expression Dispatcher

Delegates each IR expression to the appropriate Lower/ module.
-/

/-- Main expression dispatcher - delegates to Lower/ modules -/
def selectExpr (dst : VarId) (dstType : IRType) (e : IR.Expr) : SelectM Unit := do
  match e with
  | .ctor info args => Constructor.lowerCtor dst info args
  | .reset n x => Constructor.lowerReset dst n x
  | .reuse x info updtHeader args => Constructor.lowerReuse dst x info updtHeader args
  | .proj i x => Projection.lowerProj dst i x
  | .uproj i x => Projection.lowerUProj dst i x
  | .sproj n offset x => Projection.lowerSProj dst n offset x
  | .fap f args => Call.lowerFap dst dstType f args Inline.tryInlineExternCall
  | .pap f args => Call.lowerPap dst f args
  | .ap c args => Call.lowerAp dst c args
  | .box ty x => Call.lowerBox dst ty x
  | .unbox x => Call.lowerUnbox dst dstType x
  | .lit v =>
    match v with
    | .num n => Call.lowerLitNum dst dstType n
    | .str s => Call.lowerLitStr dst s
  | .isShared x => Call.lowerIsShared dst x

/-!
## Main Body Dispatcher

Handles IR body traversal and control flow.
-/

/-- Check if this is a tail call pattern:
    .vdecl x ty (.fap f args) (.ret (.var x))
    Returns (target function, args, isSelfRecursive) if it's a valid tail call target.
    Only user-defined functions can be tail-called (not extern C functions). -/
def isTailCallPattern (x : VarId) (e : IR.Expr) (rest : FnBody) : SelectM (Option (FunId × Array Arg × Bool)) := do
  match e, rest with
  | .fap f args, .ret (.var retVar) =>
    if x.idx == retVar.idx then
      let currentFn ← getFnName
      let isSelfRecursive := f == currentFn
      -- Only tail-call user-defined functions (not extern C functions)
      if isSelfRecursive then
        return some (f, args, true)
      else if ← Call.isUserDefinedFunction f then
        return some (f, args, false)
      else
        return none  -- External function - don't tail call
    return none
  | _, _ => return none

/-- Main body dispatcher - handles control flow and IR traversal -/
partial def selectFnBody (body : FnBody) : SelectM Unit := do
  match body with
  | .vdecl x ty e rest =>
    -- Check for tail call pattern (self-recursive or general)
    match ← isTailCallPattern x e rest with
    | some (f, args, isSelfRecursive) =>
      registerVarType x ty
      if isSelfRecursive then
        -- Self-recursive tail call: jump to function start label
        Call.lowerSelfTailCall f args
      else
        -- General tail call: jump to different function
        Call.lowerTailCall f args
    | none =>
      registerVarType x ty
      selectExpr x ty e
      selectFnBody rest
  | .jdecl j params jpBody rest =>
    Control.lowerJDecl j params
    selectFnBody rest
    Control.lowerJDeclBody j jpBody selectFnBody
  | .set x i y rest => Control.lowerSet x i y; selectFnBody rest
  | .uset x i y rest => Control.lowerUSet x i y; selectFnBody rest
  | .sset x i off y ty rest => Control.lowerSSet x i off y ty; selectFnBody rest
  | .setTag x t rest => Control.lowerSetTag x t; selectFnBody rest
  | .inc x n c p rest => RefCount.lowerInc x n c p; selectFnBody rest
  | .dec x n c p rest => RefCount.lowerDec x n c p; selectFnBody rest
  | .del x rest => RefCount.lowerDel x; selectFnBody rest
  | .case _ x ty alts => Control.lowerCase x ty alts selectFnBody
  | .ret arg =>
    let retTy ← getReturnType
    let spillBytes ← getSpillBytes
    Control.lowerRet arg retTy spillBytes
  | .jmp j args => Control.lowerJmp j args
  | .unreachable => Control.lowerUnreachable

/-!
## Function Prologue and Epilogue

Handles stack frame setup and teardown.
-/

/-- Emit function prologue with dynamic callee-saved register saving -/
def emitPrologue (spillBytes : Nat) (numSpilled : Nat) : SelectM Unit := do
  let usedGP ← getUsedCalleeSavedGP
  let usedFP ← getUsedCalleeSavedFP
  let isBoxed ← getIsBoxed

  emit (Instr.push #[Reg.phys PhysReg.x29, Reg.phys PhysReg.x30])
  emit (Instr.mov (.phys PhysReg.x29) (.reg (.phys PhysReg.sp)))

  -- For boxed wrappers, save all registers; for normal functions, only save used
  let gpPairs := if isBoxed then
    -- Boxed wrappers call other code - must save all callee-saved registers
    #[#[Reg.phys PhysReg.x19, Reg.phys PhysReg.x20],
      #[Reg.phys PhysReg.x21, Reg.phys PhysReg.x22],
      #[Reg.phys PhysReg.x23, Reg.phys PhysReg.x24],
      #[Reg.phys PhysReg.x25, Reg.phys PhysReg.x26],
      #[Reg.phys PhysReg.x27, Reg.phys PhysReg.x28]]
  else
    -- Normal functions: only save callee-saved register pairs that are actually used
    getCalleeSavedPairs usedGP

  let fpPairs := if isBoxed then
    #[#[Reg.phys PhysReg.v8, Reg.phys PhysReg.v9],
      #[Reg.phys PhysReg.v10, Reg.phys PhysReg.v11],
      #[Reg.phys PhysReg.v12, Reg.phys PhysReg.v13],
      #[Reg.phys PhysReg.v14, Reg.phys PhysReg.v15]]
  else
    getCalleeSavedFPPairs usedFP

  for pair in gpPairs do
    emit (Instr.push pair)

  for pair in fpPairs do
    emit (Instr.push pair)

  if spillBytes > 0 then
    emitStackSub spillBytes

  if numSpilled > 0 || gpPairs.size < 5 || fpPairs.size < 4 then
    let savedBytes := (gpPairs.size + fpPairs.size) * 16
    emit (Instr.comment s!"Stack frame: {spillBytes} spill + {savedBytes} saved regs (gp {gpPairs.size}/5, fp {fpPairs.size}/4)")

/-- Emit boxed function wrapper epilogue -/
def emitBoxedEpilogue (spillBytes : Nat) : SelectM Unit := do
  if spillBytes > 0 then
    emitStackAdd spillBytes

  -- Always restore all callee-saved registers (conservative)
  emit (Instr.pop #[Reg.phys PhysReg.v14, Reg.phys PhysReg.v15])
  emit (Instr.pop #[Reg.phys PhysReg.v12, Reg.phys PhysReg.v13])
  emit (Instr.pop #[Reg.phys PhysReg.v10, Reg.phys PhysReg.v11])
  emit (Instr.pop #[Reg.phys PhysReg.v8, Reg.phys PhysReg.v9])
  emit (Instr.pop #[Reg.phys PhysReg.x27, Reg.phys PhysReg.x28])
  emit (Instr.pop #[Reg.phys PhysReg.x25, Reg.phys PhysReg.x26])
  emit (Instr.pop #[Reg.phys PhysReg.x23, Reg.phys PhysReg.x24])
  emit (Instr.pop #[Reg.phys PhysReg.x21, Reg.phys PhysReg.x22])
  emit (Instr.pop #[Reg.phys PhysReg.x19, Reg.phys PhysReg.x20])

  emit (Instr.pop #[Reg.phys PhysReg.x29, Reg.phys PhysReg.x30])
  emit Instr.ret

/-- Emit boxed wrapper body -/
def emitBoxedWrapper (f : Name) (params : Array Param) (spillBytes : Nat) : SelectM Unit := do
  emit (Instr.comment s!"Boxed wrapper: unpacking {params.size} args from array")

  let extra := if params.size > 8 then params.size - 8 else 0
  let callStackBytes := extra * 8
  let callStackBase := 0
  let argStorageBase := callStackBytes

  -- Remove "_boxed" suffix from function name and fetch base parameter types if available.
  let baseFunc := stripBoxedSuffix f
  let env ← Lean.Compiler.Backend.ARM64.Lower.getEnv
  let baseParamTypes : Array IRType :=
    match (Lean.IR.getDecls env).find? (fun decl => decl.name == baseFunc) with
    | some (.fdecl _ baseParams _ _ _) =>
      baseParams.filter (fun (p : Param) => !p.ty.isVoid) |>.map (fun (p : Param) => p.ty)
    | _ =>
      params.map (fun (p : Param) => p.ty)
  let getParamTy (idx : Nat) : IRType :=
    if h : idx < baseParamTypes.size then
      baseParamTypes[idx]
    else
      (params[idx]!).ty

  -- Unpack all arguments from array to temporary storage
  for idx in [:params.size] do
    let arrayOffset := Int.ofNat (idx * 8)
    let spillOffset := Int.ofNat (argStorageBase + idx * 8)
    emit (Instr.ldr (.phys PhysReg.x8) (.mem (.phys PhysReg.x0) arrayOffset))
    emit (Instr.str (.phys PhysReg.x8) (.mem (.phys PhysReg.sp) spillOffset))

  -- Unbox scalar arguments in-place
  for idx in [:params.size] do
    let paramTy := getParamTy idx
    if paramTy.isScalar then
      let spillOffset := Int.ofNat (argStorageBase + idx * 8)
      emit (Instr.ldr (.phys PhysReg.x8) (.mem (.phys PhysReg.sp) spillOffset))
      match paramTy with
      | .uint64 =>
        emit (Instr.mov (.phys PhysReg.x0) (.reg (.phys PhysReg.x8)))
        emit (Instr.bl "_lean_unbox_uint64")
        emit (Instr.str (.phys PhysReg.x0) (.mem (.phys PhysReg.sp) spillOffset))
      | .usize =>
        emit (Instr.mov (.phys PhysReg.x0) (.reg (.phys PhysReg.x8)))
        emit (Instr.bl "_lean_unbox_usize")
        emit (Instr.str (.phys PhysReg.x0) (.mem (.phys PhysReg.sp) spillOffset))
      | .float =>
        emit (Instr.mov (.phys PhysReg.x0) (.reg (.phys PhysReg.x8)))
        emit (Instr.bl "_lean_unbox_float")
        emit (Instr.strd (.phys PhysReg.v0) (.mem (.phys PhysReg.sp) spillOffset))
      | .float32 =>
        emit (Instr.mov (.phys PhysReg.x0) (.reg (.phys PhysReg.x8)))
        emit (Instr.bl "_lean_unbox_float32")
        emit (Instr.strs (.phys PhysReg.v0) (.mem (.phys PhysReg.sp) spillOffset))
      | .uint8 | .uint16 | .uint32 =>
        emit (Instr.asr (.phys PhysReg.x8) (.phys PhysReg.x8) (.imm 1))
        emit (Instr.str (.phys PhysReg.x8) (.mem (.phys PhysReg.sp) spillOffset))
      | _ =>
        emit (Instr.asr (.phys PhysReg.x8) (.phys PhysReg.x8) (.imm 1))
        emit (Instr.str (.phys PhysReg.x8) (.mem (.phys PhysReg.sp) spillOffset))

  -- Copy args 8+ from temporary storage to call stack positions
  for j in [:extra] do
    let argIdx := j + 8
    let paramTy := getParamTy argIdx
    let srcOffset := Int.ofNat (argStorageBase + argIdx * 8)
    let dstOffset := Int.ofNat (callStackBase + j * 8)
    if paramTy == IRType.float32 then
      emit (Instr.ldrs (.phys PhysReg.v0) (.mem (.phys PhysReg.sp) srcOffset))
      emit (Instr.strs (.phys PhysReg.v0) (.mem (.phys PhysReg.sp) dstOffset))
    else if paramTy == IRType.float then
      emit (Instr.ldrd (.phys PhysReg.v0) (.mem (.phys PhysReg.sp) srcOffset))
      emit (Instr.strd (.phys PhysReg.v0) (.mem (.phys PhysReg.sp) dstOffset))
    else
      emit (Instr.ldr (.phys PhysReg.x8) (.mem (.phys PhysReg.sp) srcOffset))
      emit (Instr.str (.phys PhysReg.x8) (.mem (.phys PhysReg.sp) dstOffset))

  -- Load args 0-7 into x0-x7
  for i in [:min params.size 8] do
    let argReg := getArgReg i
    let spillOffset := Int.ofNat (argStorageBase + i * 8)
    let paramTy := getParamTy i
    if paramTy == IRType.float32 then
      let fpArgReg := getFPArgReg i
      emit (Instr.ldrs (.phys fpArgReg) (.mem (.phys PhysReg.sp) spillOffset))
    else if paramTy == IRType.float then
      let fpArgReg := getFPArgReg i
      emit (Instr.ldrd (.phys fpArgReg) (.mem (.phys PhysReg.sp) spillOffset))
    else
      emit (Instr.ldr (.phys argReg) (.mem (.phys PhysReg.sp) spillOffset))

  -- Call the non-boxed version
  let callTarget := if baseFunc == `main then "_lean_main" else "_" ++ Name.mangle baseFunc "l_"
  emit (Instr.bl callTarget)

  -- Epilogue
  emitBoxedEpilogue spillBytes

/-- Load stack parameters (idx >= 8) -/
def loadStackParams (params : Array Param) (allocState : AllocState) : SelectM Unit := do
  for idx in [:params.size] do
    if idx ≥ 8 then
      let param := params[idx]!
      let extra := idx - 8
      let callerOffset := Int.ofNat (16 + extra * 8)
      match allocState.allocation.get? param.x.idx with
      | some allocReg =>
        emit (Instr.comment s!"load stack param {idx}: [x29, #{callerOffset}] → {allocReg}")
        if param.ty == IRType.float32 then
          emit (Instr.ldrs (.phys allocReg) (.mem (.phys PhysReg.x29) callerOffset))
        else if param.ty == IRType.float then
          emit (Instr.ldrd (.phys allocReg) (.mem (.phys PhysReg.x29) callerOffset))
        else
          emit (Instr.ldr (.phys allocReg) (.mem (.phys PhysReg.x29) callerOffset))
      | none =>
        -- Stack parameter is spilled - must copy from caller stack to local spill slot
        match allocState.stackSlots.get? param.x.idx with
        | some slot =>
          let localOffset := Int.ofNat (slot * 8)
          emit (Instr.comment s!"copy stack param {idx} from [x29, #{callerOffset}] to [sp, #{localOffset}]")
          if param.ty == IRType.float32 then
            emit (Instr.ldrs (.phys PhysReg.v0) (.mem (.phys PhysReg.x29) callerOffset))
            emit (Instr.strs (.phys PhysReg.v0) (.mem (.phys PhysReg.sp) localOffset))
          else if param.ty == IRType.float then
            emit (Instr.ldrd (.phys PhysReg.v0) (.mem (.phys PhysReg.x29) callerOffset))
            emit (Instr.strd (.phys PhysReg.v0) (.mem (.phys PhysReg.sp) localOffset))
          else
            emit (Instr.ldr (.phys PhysReg.x8) (.mem (.phys PhysReg.x29) callerOffset))
            emit (Instr.str (.phys PhysReg.x8) (.mem (.phys PhysReg.sp) localOffset))
        | none =>
          emit (Instr.comment s!"WARNING: stack param {idx} not allocated!")

/-- Save parameters from argument registers to allocated registers or stack slots -/
def saveParamsFromRegs (params : Array Param) (allocState : AllocState) : SelectM Unit := do
  for i in [:min params.size 8] do
    let param := params[i]!
    match allocState.allocation.get? param.x.idx with
    | some allocReg =>
      let isFloat := param.ty == IRType.float || param.ty == IRType.float32
      if isFloat then
        let fpArgReg := getFPArgReg i
        if allocReg != fpArgReg then
          let prec := typeToFloatPrec param.ty
          emit (Instr.fmov prec (.phys allocReg) (.phys fpArgReg))
      else
        let argReg := getArgReg i
        if allocReg != argReg then
          emitMove (.phys allocReg) (.reg (.phys argReg))
    | none =>
      -- Parameter is spilled - store argument register to stack slot
      match allocState.stackSlots.get? param.x.idx with
      | some slot =>
        let isFloat := param.ty == IRType.float || param.ty == IRType.float32
        if isFloat then
          let fpArgReg := getFPArgReg i
          let offset := Int.ofNat (slot * 8)
          emit (Instr.comment s!"store spilled float param {i} to stack slot {slot}")
          if param.ty == IRType.float32 then
            emit (Instr.strs (.phys fpArgReg) (.mem (.phys PhysReg.sp) offset))
          else
            emit (Instr.strd (.phys fpArgReg) (.mem (.phys PhysReg.sp) offset))
        else
          let argReg := getArgReg i
          let offset := Int.ofNat (slot * 8)
          emit (Instr.comment s!"store spilled param {i} to stack slot {slot}")
          emit (Instr.str (.phys argReg) (.mem (.phys PhysReg.sp) offset))
      | none => pure ()

/-!
## Entry Points
-/

/-- Collect variable types from IR body for register allocation -/
partial def collectVarTypes (body : FnBody) (params : Array Param) : Std.TreeMap Index IRType (fun a b => compare a b) :=
  let rec collect (b : FnBody) (acc : Std.TreeMap Index IRType (fun a b => compare a b)) : Std.TreeMap Index IRType (fun a b => compare a b) :=
    match b with
    | .vdecl x ty _ rest => collect rest (acc.insert x.idx ty)
    | .jdecl _ jparams _ rest =>
      let acc := jparams.foldl (fun m p => m.insert p.x.idx p.ty) acc
      collect rest acc
    | .case _ _ _ alts =>
      alts.foldl (fun m alt => collect alt.body m) acc
    | .set _ _ _ rest | .uset _ _ _ rest | .sset _ _ _ _ _ rest
    | .setTag _ _ rest | .inc _ _ _ _ rest | .dec _ _ _ _ rest | .del _ rest => collect rest acc
    | .ret _ | .jmp _ _ | .unreachable => acc
  let initMap := params.foldl (fun m p => m.insert p.x.idx p.ty) {}
  collect body initMap

/-- Run instruction selection with the Lower/ monad -/
def runSelectM (ctx : SelectContext) (action : SelectM Unit) : SelectState :=
  let initState : SelectState := {}
  let (_, finalState) := action ctx initState
  finalState

/-- Compile a declaration to ARM64 machine code -/
def compileDecl (env : Environment) (decl : Decl) : MachineFunction :=
  match decl with
  | .fdecl f params retTy body _ =>
    -- Void parameters are not passed at runtime; drop them for codegen.
    let params := params.filter fun p => !p.ty.isVoid
    -- Pre-collect variable types for register allocation
    let varTypes := collectVarTypes body params

    -- Check if function uses floating-point types
    let _usesFloat :=
      params.any (fun p => p.ty == IRType.float || p.ty == IRType.float32) ||
      retTy == IRType.float || retTy == IRType.float32 ||
      varTypes.any (fun _ ty => ty == IRType.float || ty == IRType.float32)

    -- Compute proper liveness information
    let liveness := computeLiveness f params body varTypes

    -- Build affinity information for register coalescing
    let affinity := buildAffinity params body

    -- Perform register allocation with proper liveness
    let allocState := allocateRegisters params liveness affinity

    -- Calculate stack size
    let baseSpillBytes := ((allocState.nextStackSlot * 8 + 15) / 16) * 16
    let tempSlotBytes := 16
    let tempSlotOffset :=
      if baseSpillBytes == 0 then
        some (Int.ofNat 0)
      else
        some (Int.ofNat baseSpillBytes)

    -- Check if this is a boxed function
    let isBoxed := params.size > closureMaxArgs && LCNF.isBoxedName f
    let spillBytes := if isBoxed then
      let argBytes := params.size * 8
      let extra := if params.size > 8 then params.size - 8 else 0
      let callStackBytes := extra * 8
      let boxedBytes := argBytes + callStackBytes
      ((boxedBytes + 15) / 16) * 16
    else
      baseSpillBytes + tempSlotBytes

    -- Get used callee-saved registers for dynamic save/restore
    let usedCalleeSavedGP := allocState.usedCalleeSavedGP
    let usedCalleeSavedFP := allocState.usedCalleeSavedFP

    -- Create context for SelectM
    let ctx : SelectContext := {
      env := env
      fnName := f
      params := params
      returnType := retTy
      allocResult := allocState
      varTypes := varTypes
      spillBytes := spillBytes
      tempSlotOffset := if isBoxed then none else tempSlotOffset
      usedCalleeSavedGP := usedCalleeSavedGP
      usedCalleeSavedFP := usedCalleeSavedFP
      isBoxed := isBoxed
    }

    -- Run instruction selection
    let finalState := runSelectM ctx do
      emit (Instr.comment s!"Function: {f}")

      -- Register parameter types
      for param in params do
        registerVarType param.x param.ty

      let numSpilled := allocState.nextStackSlot

      -- Emit prologue
      emitPrologue spillBytes numSpilled

      if isBoxed then
        -- Boxed wrapper
        emitBoxedWrapper f params spillBytes
      else
        -- Normal function
        loadStackParams params allocState

        -- Add label for tail call optimization
        emit (Instr.label s!".Lfn_start_{sanitizeForLabel' f.toString}")

        -- Save parameters from argument registers
        saveParamsFromRegs params allocState

        -- Select instructions for body
        selectFnBody body

    {
      name := f
      blocks := #[{ label := f.toString, instrs := finalState.buffer.instrs }]
      stringLits := finalState.buffer.stringLits
    }

  | .extern f _ _ _ =>
    { name := f, blocks := #[], stringLits := #[] }

end InstrSelect
end Lean.Compiler.Backend

end
