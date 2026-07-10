/-
Copyright (c) 2025 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Assistant
-/

module

prelude
public import Lean.Compiler.Backend.ARM64.Lower.Base
public import Lean.Compiler.ExportAttr
public import Lean.Compiler.ExternAttr
public import Lean.Compiler.ClosedTermCache
public import Lean.Compiler.ModPkgExt

public section

namespace Lean.Compiler.Backend.ARM64.Lower.Call

/-!
# Function Call Lowering

Handles function call expressions:
- .fap: Full application (direct call)
- .pap: Partial application (closure creation)
- .ap: Apply closure
- .box: Box scalar to object
- .unbox: Unbox object to scalar
- .lit: Literal values
-/

open Lean.IR
open Lean.Compiler.Backend.ARM64

/-- Look up a function declaration in the environment -/
def findEnvDecl' (env : Environment) (f : FunId) : Option Decl :=
  IR.findEnvDecl env f

/-- Check if a function is a callable user-defined Lean function.
    Only user-defined functions can be tail-called safely.
    Excludes:
    - Extern C functions (can't branch to external symbols)
    - Closed terms (global constants, not functions) -/
def isUserDefinedFunction (f : FunId) : SelectM Bool := do
  let env ← getEnv
  -- Closed terms are global constants, not callable functions
  if isClosedTermName env f then return false
  match findEnvDecl' env f with
  | some (.fdecl _ params ..) =>
    let arity := params.foldl (init := 0) fun acc p =>
      if p.ty.isVoid then acc else acc + 1
    if arity == 0 then
      return false
    return true  -- User-defined function
  | _ => return false  -- Extern or unknown - don't tail call

/-- Get the mangled function name for a FunId -/
def getFunctionName (f : FunId) : SelectM String := do
  let env ← getEnv
  let withSymbolPrefix (name : String) : String :=
    if name.startsWith "_" then name else s!"_{name}"
  let defaultSymbolName : String :=
    if f == `main then "_lean_main" else withSymbolPrefix (Lean.getSymbolStem env f)
  let exportSymbolName? : Option String :=
    match Lean.getExportNameFor? env f with
    | some (.str .anonymous s) => some (withSymbolPrefix s)
    | some _ => panic! s!"invalid export name '{f}'"
    | none => none
  match findEnvDecl' env f with
  | some (.extern _ _ _ extData) =>
    -- Try to get the C function name from extern data
    match getExternEntryFor extData `c with
    | some (.standard _ cName) => return withSymbolPrefix cName
    | _ => return defaultSymbolName
  | _ =>
    match exportSymbolName? with
    | some exportName => return exportName
    | none => return defaultSymbolName

/-- Get the arity of a function -/
def getFunctionArity (f : FunId) : SelectM Nat := do
  let env ← getEnv
  match findEnvDecl' env f with
  | some (.fdecl _ params ..) =>
    return params.foldl (init := 0) fun acc p =>
      if p.ty.isVoid then acc else acc + 1
  | some (.extern _ params ..) =>
    let externC := isExternC env f
    return params.foldl (init := 0) fun acc p =>
      if p.ty.isVoid || (externC && p.ty.isErased) then acc else acc + 1
  | none => return 0

/-- Get parameter types for a function -/
def getParamTypes (f : FunId) (args : Array Arg) : SelectM (Array Arg × Array IRType) := do
  let env ← getEnv
  match findEnvDecl' env f with
  | some (.extern _ params ..) =>
    let externC := isExternC env f
    let mut acc := #[]
    let mut types := #[]
    for idx in [:args.size] do
      let arg := args[idx]!
      if idx < params.size then
        let param := params[idx]!
        if !param.ty.isVoid && (!externC || !param.ty.isErased) then
          acc := acc.push arg
          types := types.push param.ty
      else
        acc := acc.push arg
        types := types.push IRType.object
    return (acc, types)
  | some (.fdecl _ params ..) =>
    let mut acc := #[]
    let mut types := #[]
    for idx in [:args.size] do
      let arg := args[idx]!
      if idx < params.size then
        let param := params[idx]!
        if !param.ty.isVoid then
          acc := acc.push arg
          types := types.push param.ty
      else
        acc := acc.push arg
        types := types.push IRType.object
    return (acc, types)
  | _ => return (args, args.map (fun _ => IRType.object))

/-- Get parameter index for a variable (if it's a function parameter) -/
def getParameterIndex? (_v : VarId) : SelectM (Option Nat) := pure none

/-- Lower nullary function reference (global constant load) -/
def lowerGlobalLoad (dst : VarId) (f : FunId) (dstType : IRType) : SelectM Unit := do
  let fnName ← getFunctionName f
  let (dstReg, isSpilled) ← getDstReg dst

  emitComment s!"load global constant {fnName}"

  match dstType with
  | .float | .float32 =>
    -- Float constants: use temp GP register for adrp/add, then load into FP register
    let tempReg := Reg.phys PhysReg.x16
    emit (Instr.adrp tempReg s!"{fnName}@PAGE")
    emit (Instr.add tempReg tempReg (.label s!"{fnName}@PAGEOFF"))
    if dstType == .float32 then
      emit (Instr.ldrs dstReg (.mem tempReg 0))
    else
      emit (Instr.ldrd dstReg (.mem tempReg 0))
  | .uint8 =>
    emit (Instr.adrp dstReg s!"{fnName}@PAGE")
    emit (Instr.add dstReg dstReg (.label s!"{fnName}@PAGEOFF"))
    emit (Instr.ldrb dstReg (.mem dstReg 0))
  | .uint16 =>
    emit (Instr.adrp dstReg s!"{fnName}@PAGE")
    emit (Instr.add dstReg dstReg (.label s!"{fnName}@PAGEOFF"))
    emit (Instr.ldrh dstReg (.mem dstReg 0))
  | .uint32 =>
    emit (Instr.adrp dstReg s!"{fnName}@PAGE")
    emit (Instr.add dstReg dstReg (.label s!"{fnName}@PAGEOFF"))
    emit (Instr.ldrw dstReg (.mem dstReg 0))
  | _ =>
    -- Load doubleword (64-bit) - objects, uint64, usize
    emit (Instr.adrp dstReg s!"{fnName}@PAGE")
    emit (Instr.ldr dstReg (.reg dstReg) s!", {fnName}@PAGEOFF")

  if isSpilled then
    storeSpilledDst dst dstReg
  releaseAllScratch

/-- Release scratch register used for a spilled variable. -/
def releaseScratchIfSpilled (v : VarId) (reg : Reg) : SelectM Unit := do
  let alloc ← getAllocResult
  if (alloc.allocation.get? v.idx).isNone then
    match reg with
    | .phys pr =>
      if RegClass.scratch.contains pr || RegClass.fpScratch.contains pr then
        releaseScratch pr
    | _ => pure ()

/-- Setup argument in register for function call -/
def setupCallArg (i : Nat) (arg : Arg) (paramTy : IRType) : SelectM Unit := do
  let isFloat := paramTy == IRType.float || paramTy == IRType.float32
  match arg with
  | .var v =>
    let vReg ← varToReg v
    if isFloat then
      let fpArgReg := getFPArgReg i
      let prec := typeToFloatPrec paramTy
      emit (Instr.fmov prec (.phys fpArgReg) vReg)
    else
      let argReg := getArgReg i
      emitMove (.phys argReg) (.reg vReg)
    releaseScratchIfSpilled v vReg
  | .erased =>
    let argReg := getArgReg i
    emit (Instr.mov (.phys argReg) (.imm 1))  -- lean_box(0)

/-- Load an argument into a GP register, honoring rematerializable constants and stack offsets. -/
def loadArgToGP (dst : PhysReg) (arg : Arg) (stackOffset : Nat) : SelectM Unit := do
  match arg with
  | .erased =>
    emit (Instr.mov (.phys dst) (.imm 1))
  | .var v =>
    let alloc ← getAllocResult
    match alloc.allocation.get? v.idx with
    | some phys =>
      if phys != dst then
        emitMove (.phys dst) (.reg (.phys phys))
    | none =>
      match alloc.rematerializable.get? v.idx with
      | some constVal =>
        loadImm64 (.phys dst) constVal.toNat
      | none =>
        match alloc.stackSlots.get? v.idx with
        | some slot =>
          let offset := Int.ofNat (stackOffset + slot * 8)
          let ty := (← getVarType v).getD .object
          if ty == .uint8 then
            emit (Instr.ldrb (.phys dst) (.mem (.phys PhysReg.sp) offset))
          else if ty == .uint16 then
            emit (Instr.ldrh (.phys dst) (.mem (.phys PhysReg.sp) offset))
          else if ty == .uint32 then
            emit (Instr.ldrw (.phys dst) (.mem (.phys PhysReg.sp) offset))
          else
            emit (Instr.ldr (.phys dst) (.mem (.phys PhysReg.sp) offset))
        | none =>
          emitComment s!"ERROR: arg var{v.idx} not allocated!"

/-- Load an argument into an FP register (float/float32). -/
def loadArgToFP (dst : PhysReg) (arg : Arg) (stackOffset : Nat) (ty : IRType) : SelectM Unit := do
  let prec := typeToFloatPrec ty
  match arg with
  | .erased =>
    -- Default to 0.0 for erased float arguments.
    emit (Instr.mov (.phys PhysReg.x0) (.imm 0))
    emit (Instr.fmov prec (.phys dst) (.phys PhysReg.x0))
  | .var v =>
    let alloc ← getAllocResult
    match alloc.allocation.get? v.idx with
    | some phys =>
      if phys != dst then
        emit (Instr.fmov prec (.phys dst) (.phys phys))
    | none =>
      match alloc.stackSlots.get? v.idx with
      | some slot =>
        let offset := Int.ofNat (stackOffset + slot * 8)
        if ty == .float32 then
          emit (Instr.ldrs (.phys dst) (.mem (.phys PhysReg.sp) offset))
        else
          emit (Instr.ldrd (.phys dst) (.mem (.phys PhysReg.sp) offset))
      | none =>
        emitComment s!"ERROR: arg var{v.idx} not allocated!"

/-- Store an argument to the outgoing stack slot with type-aware width. -/
def storeStackArg (arg : Arg) (paramTy : IRType) (offset : Int) (stackBytes : Nat) : SelectM Unit := do
  let isFloat := paramTy == IRType.float || paramTy == IRType.float32
  if isFloat then
    let prec := typeToFloatPrec paramTy
    let emitStore (r : PhysReg) : SelectM Unit := do
      if paramTy == IRType.float32 then
        emit (Instr.strs (.phys r) (.mem (.phys PhysReg.sp) offset))
      else
        emit (Instr.strd (.phys r) (.mem (.phys PhysReg.sp) offset))
    match arg with
    | .var v =>
      let alloc ← getAllocResult
      match alloc.allocation.get? v.idx with
      | some phys =>
        if phys.isFP then
          emitStore phys
        else
          let tmp ← acquireFPScratch
          emit (Instr.fmov prec (.phys tmp) (.phys phys))
          emitStore tmp
          releaseScratch tmp
      | none =>
        let tmp ← acquireFPScratch
        loadArgToFP tmp (.var v) stackBytes paramTy
        emitStore tmp
        releaseScratch tmp
    | .erased =>
      let tmp ← acquireFPScratch
      emit (Instr.mov (.phys PhysReg.x0) (.imm 0))
      emit (Instr.fmov prec (.phys tmp) (.phys PhysReg.x0))
      emitStore tmp
      releaseScratch tmp
  else
    match arg with
    | .var v =>
      let alloc ← getAllocResult
      match alloc.allocation.get? v.idx with
      | some phys =>
        emit (Instr.str (.phys phys) (.mem (.phys PhysReg.sp) offset))
      | none =>
        let tmp ← acquireScratch
        loadArgToGP tmp (.var v) stackBytes
        emit (Instr.str (.phys tmp) (.mem (.phys PhysReg.sp) offset))
        releaseScratch tmp
    | .erased =>
      let tmp ← acquireScratch
      emit (Instr.mov (.phys tmp) (.imm 1))
      emit (Instr.str (.phys tmp) (.mem (.phys PhysReg.sp) offset))
      releaseScratch tmp

/-- Handle result from function call -/
def handleCallResult (dstReg : Reg) (dstType : IRType) : SelectM Unit := do
  if dstType == IRType.float || dstType == IRType.float32 then
    if dstReg != .phys PhysReg.v0 then
      let prec := typeToFloatPrec dstType
      emit (Instr.fmov prec dstReg (.phys PhysReg.v0))
  else if dstType == IRType.uint8 then
    if dstReg == .phys PhysReg.x0 then
      emit (Instr.and (.phys PhysReg.x0) (.phys PhysReg.x0) (.imm 0xFF))
    else
      emit (Instr.and dstReg (.phys PhysReg.x0) (.imm 0xFF))
  else if dstType == IRType.uint16 then
    if dstReg == .phys PhysReg.x0 then
      emit (Instr.and (.phys PhysReg.x0) (.phys PhysReg.x0) (.imm 0xFFFF))
    else
      emit (Instr.and dstReg (.phys PhysReg.x0) (.imm 0xFFFF))
  else
    if dstReg != .phys PhysReg.x0 then
      emitMove dstReg (.reg (.phys PhysReg.x0))

/-- Check if a call is a self-recursive tail call.
    Returns true if the called function is the current function. -/
def isSelfCall (f : FunId) : SelectM Bool := do
  let currentFn ← getFnName
  return f == currentFn

/-- Lower self-recursive tail call: true tail call with stack restore -/
def lowerSelfTailCall (f : FunId) (args : Array Arg) : SelectM Unit := do
  let (callArgs, paramTypes) ← getParamTypes f args
  let fnName ← getFunctionName f
  let spillBytes ← getSpillBytes

  emitComment s!"true tail call to self with {callArgs.size} runtime args"

  -- Setup arguments for the tail call
  for i in [:min callArgs.size 8] do
    let paramTy := if i < paramTypes.size then paramTypes[i]! else IRType.object
    setupCallArg i callArgs[i]! paramTy

  -- If more than 8 args, fall back to a normal call with stack args
  if callArgs.size > 8 then
    emitComment "WARNING: self tail call with >8 args, falling back to regular call"
    let extra := callArgs.size - 8
    let extraBytes := extra * 8
    let stackBytes := ((extraBytes + 15) / 16) * 16

    if stackBytes > 0 then
      emitStackSub stackBytes

    if extra > 0 then
      for j in [:extra] do
        let argIdx := j + 8
        let offset := Int.ofNat (j * 8)
        let paramTy := if argIdx < paramTypes.size then paramTypes[argIdx]! else IRType.object
        storeStackArg callArgs[argIdx]! paramTy offset stackBytes

    emit (Instr.bl fnName)

    if stackBytes > 0 then
      emitStackAdd stackBytes

    if spillBytes > 0 then
      emitStackAdd spillBytes

    let usedGP ← getUsedCalleeSavedGP
    let usedFP ← getUsedCalleeSavedFP
    let fpPairs := getCalleeSavedFPPairs usedFP
    let pairs := getCalleeSavedPairs usedGP
    for pair in fpPairs.reverse do
      emit (Instr.pop pair)
    for pair in pairs.reverse do
      emit (Instr.pop pair)
    emit (Instr.pop #[Reg.phys PhysReg.x29, Reg.phys PhysReg.x30])
    emit Instr.ret
    return

  -- Restore stack frame (epilogue without ret)
  if spillBytes > 0 then
    emitStackAdd spillBytes

  -- Only restore callee-saved registers that were saved (reverse order of prologue)
  let usedGP ← getUsedCalleeSavedGP
  let usedFP ← getUsedCalleeSavedFP
  let fpPairs := getCalleeSavedFPPairs usedFP
  let pairs := getCalleeSavedPairs usedGP
  for pair in fpPairs.reverse do
    emit (Instr.pop pair)
  for pair in pairs.reverse do
    emit (Instr.pop pair)

  -- Restore frame pointer and link register
  emit (Instr.pop #[Reg.phys PhysReg.x29, Reg.phys PhysReg.x30])

  -- Jump to function (tail call - reuses caller's return address)
  emit (Instr.branch fnName)

/-- Lower general tail call to a different function: tail call with stack restore -/
def lowerTailCall (f : FunId) (args : Array Arg) : SelectM Unit := do
  let (callArgs, paramTypes) ← getParamTypes f args
  let fnName ← getFunctionName f
  let spillBytes ← getSpillBytes

  emitComment s!"general tail call to {f} with {callArgs.size} runtime args"

  -- Setup arguments for the tail call (same as lowerSelfTailCall)
  for i in [:min callArgs.size 8] do
    let paramTy := if i < paramTypes.size then paramTypes[i]! else IRType.object
    setupCallArg i callArgs[i]! paramTy

  -- Handle stack arguments if more than 8 args (callee will pop them)
  -- Note: For tail calls with stack args, we need to set up the stack args
  -- in the callee's expected position. This is complex because we need to
  -- clean up our frame first. For now, only support <= 8 args in tail calls.
  if callArgs.size > 8 then
    emitComment "WARNING: tail call with >8 args, falling back to regular call"
    let extra := callArgs.size - 8
    let extraBytes := extra * 8
    let stackBytes := ((extraBytes + 15) / 16) * 16

    if stackBytes > 0 then
      emitStackSub stackBytes

    if extra > 0 then
      for j in [:extra] do
        let argIdx := j + 8
        let offset := Int.ofNat (j * 8)
        let paramTy := if argIdx < paramTypes.size then paramTypes[argIdx]! else IRType.object
        storeStackArg callArgs[argIdx]! paramTy offset stackBytes

    emit (Instr.bl fnName)

    if stackBytes > 0 then
      emitStackAdd stackBytes

    if spillBytes > 0 then
      emitStackAdd spillBytes
    let usedGP ← getUsedCalleeSavedGP
    let usedFP ← getUsedCalleeSavedFP
    let fpPairs := getCalleeSavedFPPairs usedFP
    let pairs := getCalleeSavedPairs usedGP
    for pair in fpPairs.reverse do
      emit (Instr.pop pair)
    for pair in pairs.reverse do
      emit (Instr.pop pair)
    emit (Instr.pop #[Reg.phys PhysReg.x29, Reg.phys PhysReg.x30])
    emit Instr.ret
    return

  -- Restore stack frame (epilogue without ret)
  if spillBytes > 0 then
    emitStackAdd spillBytes

  -- Only restore callee-saved registers that were saved (reverse order of prologue)
  let usedGP ← getUsedCalleeSavedGP
  let usedFP ← getUsedCalleeSavedFP
  let fpPairs := getCalleeSavedFPPairs usedFP
  let pairs := getCalleeSavedPairs usedGP
  for pair in fpPairs.reverse do
    emit (Instr.pop pair)
  for pair in pairs.reverse do
    emit (Instr.pop pair)

  -- Restore frame pointer and link register
  emit (Instr.pop #[Reg.phys PhysReg.x29, Reg.phys PhysReg.x30])

  -- Jump to target function (tail call - reuses caller's return address)
  emit (Instr.branch fnName)

/-- Lower .fap (full application / direct call) -/
def lowerFap (dst : VarId) (dstType : IRType) (f : FunId) (args : Array Arg)
    (tryInline : String → Array Arg → Reg → SelectM Bool) : SelectM Unit := do
  let (dstReg, isSpilled) ← getDstReg dst

  if args.size == 0 then
    lowerGlobalLoad dst f dstType
    return

  let fnName ← getFunctionName f
  if ← tryInline fnName args dstReg then
    if isSpilled then
      storeSpilledDst dst dstReg
    releaseAllScratch
    return

  -- NOTE: Tail call optimization is now handled at the IR level
  -- lowerFap should NOT do tail call optimization since we don't know if we're in tail position
  -- Self-recursive tail calls in Lean IR are represented differently (goto-style jumps)

  -- Standard function call
  let (callArgs, paramTypes) ← getParamTypes f args
  emitComment s!"call {f} with {callArgs.size} runtime args"

  -- Setup first 8 arguments in registers
  for i in [:min callArgs.size 8] do
    let paramTy := if i < paramTypes.size then paramTypes[i]! else IRType.object
    setupCallArg i callArgs[i]! paramTy

  -- Handle stack arguments (beyond 8)
  let extra := if callArgs.size > 8 then callArgs.size - 8 else 0
  let extraBytes := extra * 8
  let stackBytes := ((extraBytes + 15) / 16) * 16

  if stackBytes > 0 then
    emitStackSub stackBytes

  -- Store extra arguments to stack
  if extra > 0 then
    for j in [:extra] do
      let argIdx := j + 8
      let offset := Int.ofNat (j * 8)
      let paramTy := if argIdx < paramTypes.size then paramTypes[argIdx]! else IRType.object
      storeStackArg callArgs[argIdx]! paramTy offset stackBytes

  emit (Instr.bl fnName)

  if stackBytes > 0 then
    emitStackAdd stackBytes

  handleCallResult dstReg dstType

  if isSpilled then
    storeSpilledDst dst dstReg
  releaseAllScratch

/-- Lower .pap (partial application / closure creation) -/
def lowerPap (dst : VarId) (f : FunId) (args : Array Arg) : SelectM Unit := do
  let (dstReg, isSpilled) ← getDstReg dst

  emitComment s!"partial application {f} with {args.size} args"
  let fnName ← getFunctionName f
  let arity ← getFunctionArity f

  -- Allocate closure: lean_alloc_closure(fn, arity, num_args)
  -- Use direct address for internal functions; use GOT for externs on macOS.
  let env ← getEnv
  let useGOT :=
    match findEnvDecl' env f with
    | some (.extern ..) => true
    | _ => false
  if useGOT then
    emit (Instr.adrp (.phys PhysReg.x0) s!"{fnName}@GOTPAGE")
    emit (Instr.ldr (.phys PhysReg.x0) (.reg (.phys PhysReg.x0)) s!", {fnName}@GOTPAGEOFF")
  else
    emit (Instr.adrp (.phys PhysReg.x0) s!"{fnName}@PAGE")
    emit (Instr.add (.phys PhysReg.x0) (.phys PhysReg.x0) (.label s!"{fnName}@PAGEOFF"))
  emit (Instr.mov (.phys PhysReg.x1) (.imm (Int.ofNat arity)))
  emit (Instr.mov (.phys PhysReg.x2) (.imm (Int.ofNat args.size)))
  emit (Instr.bl "_lean_alloc_closure")

  if args.isEmpty then
    if dstReg != .phys PhysReg.x0 then
      emitMove dstReg (.reg (.phys PhysReg.x0))
  else
    -- Preserve the closure pointer across _lean_closure_set calls.
    -- Prefer the per-function temp slot to avoid extra stack adjustment.
    let tempSlotOffset? ← getTempSlotOffset
    let (slotOffset, stackAdjust) :=
      match tempSlotOffset? with
      | some off => (off, 0)
      | none => (Int.ofNat 0, 16)
    if stackAdjust > 0 then
      emitStackSub stackAdjust
    emit (Instr.str (.phys PhysReg.x0) (.mem (.phys PhysReg.sp) slotOffset))
    for i in [:args.size] do
      emit (Instr.ldr (.phys PhysReg.x0) (.mem (.phys PhysReg.sp) slotOffset))
      emit (Instr.mov (.phys PhysReg.x1) (.imm (Int.ofNat i)))
      match args[i]! with
      | .var v =>
        loadArgToGP PhysReg.x2 (.var v) stackAdjust
      | .erased =>
        emit (Instr.mov (.phys PhysReg.x2) (.imm 1))
      emit (Instr.bl "_lean_closure_set")
    emit (Instr.ldr (.phys PhysReg.x0) (.mem (.phys PhysReg.sp) slotOffset))
    if stackAdjust > 0 then
      emitStackAdd stackAdjust
    if dstReg != .phys PhysReg.x0 then
      emitMove dstReg (.reg (.phys PhysReg.x0))

  if isSpilled then
    storeSpilledDst dst dstReg
  releaseAllScratch

/-- Lower .ap (apply closure) -/
def lowerAp (dst : VarId) (x : VarId) (args : Array Arg) : SelectM Unit := do
  let xReg ← varToReg x
  let (dstReg, isSpilled) ← getDstReg dst
  let alloc ← getAllocResult

  emitComment s!"apply closure with {args.size} args"

  if args.isEmpty then
    if dstReg != xReg then
      emit (Instr.mov dstReg (.reg xReg))
  else
    let maxArgs := closureMaxArgs
    if args.size ≤ maxArgs then
      let n := args.size
      let extra := if n > 7 then n - 7 else 0
      let extraBytes := extra * 8
      let stackBytes := ((extraBytes + 15) / 16) * 16
      if stackBytes > 0 then
        emitStackSub stackBytes
      emit (Instr.mov (.phys PhysReg.x0) (.reg xReg))
      for i in [:min n 7] do
        let argReg := getArgReg (i + 1)
        match args[i]! with
        | .var v =>
          loadArgToGP argReg (.var v) stackBytes
        | .erased =>
          emit (Instr.mov (.phys argReg) (.imm 1))
      if extra > 0 then
        for j in [:extra] do
          let argIdx := j + 7
          let offset := Int.ofNat (j * 8)
          match args[argIdx]! with
          | .var v =>
            match alloc.allocation.get? v.idx with
            | some phys =>
              emit (Instr.str (.phys phys) (.mem (.phys PhysReg.sp) offset))
            | none =>
              let tmp ← acquireScratch
              loadArgToGP tmp (.var v) stackBytes
              emit (Instr.str (.phys tmp) (.mem (.phys PhysReg.sp) offset))
              releaseScratch tmp
          | .erased =>
            let tmp ← acquireScratch
            emit (Instr.mov (.phys tmp) (.imm 1))
            emit (Instr.str (.phys tmp) (.mem (.phys PhysReg.sp) offset))
            releaseScratch tmp
      emit (Instr.bl s!"_lean_apply_{n}")
      if stackBytes > 0 then
        emitStackAdd stackBytes
      if dstReg != .phys PhysReg.x0 then
        emitMove dstReg (.reg (.phys PhysReg.x0))
    else
      -- Many arguments: use lean_apply_m with argument array
      let argBytes := args.size * 8
      let totalBytes := ((argBytes + 15) / 16) * 16
      if totalBytes > 0 then
        emitStackSub totalBytes
      for i in [:args.size] do
        let offset := Int.ofNat (i * 8)
        match args[i]! with
        | .var v =>
          match alloc.allocation.get? v.idx with
          | some phys =>
            emit (Instr.str (.phys phys) (.mem (.phys PhysReg.sp) offset))
          | none =>
            let tmp ← acquireScratch
            loadArgToGP tmp (.var v) totalBytes
            emit (Instr.str (.phys tmp) (.mem (.phys PhysReg.sp) offset))
            releaseScratch tmp
        | .erased =>
          let tmp ← acquireScratch
          emit (Instr.mov (.phys tmp) (.imm 1))
          emit (Instr.str (.phys tmp) (.mem (.phys PhysReg.sp) offset))
          releaseScratch tmp
      emit (Instr.mov (.phys PhysReg.x0) (.reg xReg))
      emit (Instr.mov (.phys PhysReg.x1) (.imm (Int.ofNat args.size)))
      emit (Instr.mov (.phys PhysReg.x2) (.reg (.phys PhysReg.sp)))
      emit (Instr.bl "_lean_apply_m")
      if totalBytes > 0 then
        emitStackAdd totalBytes
      if dstReg != .phys PhysReg.x0 then
        emitMove dstReg (.reg (.phys PhysReg.x0))

  if isSpilled then
    storeSpilledDst dst dstReg
  releaseAllScratch

/-- Lower .box expression -/
def lowerBox (dst : VarId) (ty : IRType) (x : VarId) : SelectM Unit := do
  let xReg ← varToReg x
  let (dstReg, isSpilled) ← getDstReg dst

  emitComment "box"

  match ty with
  | .uint64 =>
    emit (Instr.mov (.phys PhysReg.x0) (.reg xReg))
    emit (Instr.bl "_lean_box_uint64")
    if dstReg != .phys PhysReg.x0 then
      emitMove dstReg (.reg (.phys PhysReg.x0))
  | .float =>
    emit (Instr.fmov .double (.phys PhysReg.v0) xReg)
    emit (Instr.bl "_lean_box_float")
    if dstReg != .phys PhysReg.x0 then
      emit (Instr.mov dstReg (.reg (.phys PhysReg.x0)))
  | .float32 =>
    emit (Instr.fmov .single (.phys PhysReg.v0) xReg)
    emit (Instr.bl "_lean_box_float32")
    if dstReg != .phys PhysReg.x0 then
      emit (Instr.mov dstReg (.reg (.phys PhysReg.x0)))
  | .usize =>
    emit (Instr.mov (.phys PhysReg.x0) (.reg xReg))
    emit (Instr.bl "_lean_box_usize")
    if dstReg != .phys PhysReg.x0 then
      emit (Instr.mov dstReg (.reg (.phys PhysReg.x0)))
  | .uint8 | .uint16 | .uint32 =>
    -- Inline scalar boxing: shift left by 1 and set low bit
    emit (Instr.lsl dstReg xReg (.imm 1))
    emit (Instr.orr dstReg dstReg (.imm 1))
  | _ =>
    emit (Instr.mov dstReg (.reg xReg))

  if isSpilled then
    storeSpilledDst dst dstReg
  releaseAllScratch

/-- Lower .unbox expression -/
def lowerUnbox (dst : VarId) (dstType : IRType) (x : VarId) : SelectM Unit := do
  let xReg ← varToReg x
  let (dstReg, isSpilled) ← getDstReg dst

  emitComment "unbox"

  match dstType with
  | .uint64 =>
    emit (Instr.mov (.phys PhysReg.x0) (.reg xReg))
    emit (Instr.bl "_lean_unbox_uint64")
    if dstReg != .phys PhysReg.x0 then
      emit (Instr.mov dstReg (.reg (.phys PhysReg.x0)))
  | .float =>
    emit (Instr.mov (.phys PhysReg.x0) (.reg xReg))
    emit (Instr.bl "_lean_unbox_float")
    if dstReg != .phys PhysReg.v0 then
      emit (Instr.fmov .double dstReg (.phys PhysReg.v0))
  | .float32 =>
    emit (Instr.mov (.phys PhysReg.x0) (.reg xReg))
    emit (Instr.bl "_lean_unbox_float32")
    if dstReg != .phys PhysReg.v0 then
      emit (Instr.fmov .single dstReg (.phys PhysReg.v0))
  | .usize =>
    emit (Instr.mov (.phys PhysReg.x0) (.reg xReg))
    emit (Instr.bl "_lean_unbox_usize")
    if dstReg != .phys PhysReg.x0 then
      emit (Instr.mov dstReg (.reg (.phys PhysReg.x0)))
  | .uint8 | .uint16 | .uint32 =>
    -- Inline scalar unboxing: arithmetic shift right by 1
    emit (Instr.asr dstReg xReg (.imm 1))
  | _ =>
    emit (Instr.asr dstReg xReg (.imm 1))

  if isSpilled then
    storeSpilledDst dst dstReg
  releaseAllScratch

/-- Register a string literal for data emission and return its data label. -/
private def registerStringLiteral (s : String) : SelectM String := do
  let state ← get
  let fnName ← getFnName
  let fnSuffix := sanitizeForLabel fnName.toString
  let strId := state.buffer.nextStringId
  let dataLabel := s!"_str_{fnSuffix}_{strId}_data"
  modify fun st => { st with
    buffer := { st.buffer with
      stringLits := st.buffer.stringLits.push {
        id := strId
        ptrLabel := dataLabel
        dataLabel := dataLabel
        value := s
      }
      nextStringId := strId + 1
    }
  }
  return dataLabel

/-- Lower numeric literal -/
def lowerLitNum (dst : VarId) (dstType : IRType) (n : Nat) : SelectM Unit := do
  let (dstReg, isSpilled) ← getDstReg dst
  let alloc ← getAllocResult
  -- Check if this constant is rematerializable (identified during liveness analysis)
  let isRematerializable := alloc.rematerializable.contains dst.idx

  if dstType.isScalar then
    -- Scalar: direct value
    loadImm64 dstReg n
    -- If spilled and NOT rematerializable, store to stack
    -- If rematerializable, skip store - loadSpilledVar will regenerate the constant
    if isSpilled && !isRematerializable then
      storeSpilledDst dst dstReg
  else
    -- Object: create boxed Nat
    emitComment s!"lit nat {n}"
    if n < (1 <<< 62) then
      -- Small enough for tagged representation
      let taggedVal := n * 2 + 1
      loadImm64 dstReg taggedVal
      -- If spilled and NOT rematerializable, store to stack
      if isSpilled && !isRematerializable then
        storeSpilledDst dst dstReg
    else
      -- Need heap allocation - cannot rematerialize
      if n < (1 <<< 64) then
        loadImm64 (.phys PhysReg.x0) n
        emit (Instr.bl "_lean_nat_of_uint64")
      else
        let dataLabel ← registerStringLiteral (toString n)
        emit (Instr.adrp (.phys PhysReg.x0) s!"{dataLabel}@PAGE")
        emit (Instr.add (.phys PhysReg.x0) (.phys PhysReg.x0) (.label s!"{dataLabel}@PAGEOFF"))
        emit (Instr.bl "_lean_cstr_to_nat")
      if dstReg != .phys PhysReg.x0 then
        emitMove dstReg (.reg (.phys PhysReg.x0))
      if isSpilled then
        storeSpilledDst dst dstReg
  releaseAllScratch

/-- Escape a string for a single-line comment preview. -/
private def escapeForComment (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | _ =>
      let n := c.toNat
      if n < 32 || n > 126 then
        acc ++ "?"
      else
        acc.push c

/-- Lower string literal -/
def lowerLitStr (dst : VarId) (s : String) : SelectM Unit := do
  let (dstReg, isSpilled) ← getDstReg dst

  let preview := escapeForComment ((s.take 20).toString)
  let suffix := if s.length > 20 then "..." else ""
  emitComment s!"lit string \"{preview}{suffix}\""

  let dataLabel ← registerStringLiteral s

  -- Get the UTF-8 byte length of the string
  let byteLen := s.toUTF8.size

  -- Call lean_mk_string_unchecked(s, sz, capacity)
  -- x0 = pointer to raw string data
  -- x1 = byte length (sz)
  -- x2 = capacity (same as sz for string literals)
  emit (Instr.adrp (.phys PhysReg.x0) s!"{dataLabel}@PAGE")
  emit (Instr.add (.phys PhysReg.x0) (.phys PhysReg.x0) (.label s!"{dataLabel}@PAGEOFF"))
  loadImm64 (.phys PhysReg.x1) byteLen
  loadImm64 (.phys PhysReg.x2) byteLen
  emit (Instr.bl "_lean_mk_string_unchecked")

  -- Result is in x0
  if dstReg != .phys PhysReg.x0 then
    emitMove dstReg (.reg (.phys PhysReg.x0))

  if isSpilled then
    storeSpilledDst dst dstReg
  releaseAllScratch

/-- Lower .isShared expression (inlined) -/
def lowerIsShared (dst : VarId) (x : VarId) : SelectM Unit := do
  let xReg ← varToReg x
  let (dstReg, isSpilled) ← getDstReg dst

  emitComment "isShared (inline)"

  -- If xReg and dstReg are the same, we need to save xReg first
  let (ptrReg, ptrScratch) ←
    if xReg == dstReg then
      let tmp ← acquireScratch
      emit (Instr.mov (.phys tmp) (.reg xReg))
      pure (.phys tmp, some tmp)
    else
      pure (xReg, none)

  -- Check if tagged pointer (low bit set) - if tagged, treat as shared
  emit (Instr.tst ptrReg (.imm 1))
  let doneLabel ← freshLabel "is_shared_done"
  let scalarLabel ← freshLabel "is_shared_scalar"
  emit (Instr.bCond Cond.ne scalarLabel)

  -- Not tagged, check reference count
  -- m_rc is at offset 0, 4 bytes (int32_t)
  let rcReg ← acquireScratch
  emit (Instr.ldrw (.phys rcReg) (.mem ptrReg 0))
  -- The IR `isShared` instruction implements `!lean_is_exclusive`, i.e., rc != 1
  -- (This includes persistent objects with rc=0 and shared objects with rc>=2)
  emit (Instr.cmp (.phys rcReg) (.imm 1))
  emit (Instr.cset dstReg Cond.ne)  -- dstReg = 1 if rc != 1
  releaseScratch rcReg
  emit (Instr.branch doneLabel)

  -- Tagged scalars are treated as shared (not reusable)
  emit (Instr.label scalarLabel)
  emit (Instr.mov dstReg (.imm 1))

  emit (Instr.label doneLabel)

  match ptrScratch with
  | some pr => releaseScratch pr
  | none => pure ()

  if isSpilled then
    storeSpilledDst dst dstReg
  releaseAllScratch

/-- Lower .isTaggedPtr expression -/
def lowerIsTaggedPtr (dst : VarId) (x : VarId) : SelectM Unit := do
  let xReg ← varToReg x
  let (dstReg, isSpilled) ← getDstReg dst

  emitComment "isTaggedPtr"
  -- Check if low bit is set: (x & 1)
  emit (Instr.and dstReg xReg (.imm 1))

  if isSpilled then
    storeSpilledDst dst dstReg
  releaseAllScratch

end Lean.Compiler.Backend.ARM64.Lower.Call

end
