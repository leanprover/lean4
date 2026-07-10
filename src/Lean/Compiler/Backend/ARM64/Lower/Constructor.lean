/-
Copyright (c) 2025 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Assistant
-/

module

prelude
public import Lean.Compiler.Backend.ARM64.Lower.Base

public section

namespace Lean.Compiler.Backend.ARM64.Lower.Constructor

/-!
# Constructor Lowering

This module handles lowering of constructor-related IR expressions:
- .ctor: Allocate a new constructor and set its fields
- .reuse: Reuse an existing object's memory for a new constructor
- .reset: Reset an object for reuse

Constructor lowering is complex due to:
1. Register conflicts (arg may use same register as result)
2. Spilled destinations requiring stack management
3. Boxing of scalar fields
4. ABI compliance for runtime calls
-/

open Lean.IR
open Lean.Compiler.Backend.ARM64

/-- Lower a boxed tag constructor (size=0, ssize=0) -/
def lowerBoxedTag (dstReg : Reg) (tag : Nat) : SelectM Unit := do
  -- (tag << 1) | 1
  let tagVal := tag * 2 + 1
  emit (Instr.mov dstReg (.imm (Int.ofNat tagVal)))

/-- Detect if any argument would conflict with destination register -/
def detectConflict (dstReg : Reg) (args : Array Arg) : SelectM (Option VarId) := do
  let alloc ← getAllocResult
  match dstReg with
  | .phys dstPhys =>
    for arg in args do
      match arg with
      | .var v =>
        match alloc.allocation.get? v.idx with
        | some phys =>
          if phys == dstPhys then return some v
        | none => pure ()
      | .erased => pure ()
    return none
  | _ =>
    return none

/-- Save a conflicting argument to a scratch register before it gets overwritten. -/
def saveConflict (conflict : VarId) (dstReg : Reg) : SelectM PhysReg := do
  let scratch ← acquireScratch
  emitComment s!"save vreg{conflict.idx} from {dstReg} to {scratch} (constructor will overwrite)"
  emit (Instr.mov (.phys scratch) (.reg dstReg))
  return scratch

/-- Compute scalar bytes for constructor (usize fields + other scalars). -/
def ctorScalarBytes (info : CtorInfo) : Nat :=
  info.usize * 8 + info.ssize

/-- Emit constructor allocation call (scalar size includes usize fields). -/
def emitAllocCtor (info : CtorInfo) : SelectM Unit := do
  emit (Instr.mov (.phys .x0) (.imm (Int.ofNat info.cidx)))
  emit (Instr.mov (.phys .x1) (.imm (Int.ofNat info.size)))
  emit (Instr.mov (.phys .x2) (.imm (Int.ofNat (ctorScalarBytes info))))
  emit (Instr.bl "lean_alloc_ctor")

/-- Emit field set by inlining the store instruction.
    This avoids function call overhead and register clobbering from lean_ctor_set. -/
def emitFieldSet (fieldIdx : Nat) (arg : Arg) (conflict : Option (VarId × PhysReg))
    (ctorReg : Reg) (ctorStackOffset : Option Int) : SelectM Unit := do
  -- Field offset: header is 8 bytes, each field is 8 bytes
  let fieldOffset := Int.ofNat (8 + fieldIdx * 8)

  match arg with
  | .var v =>
    let alloc ← getAllocResult
    let useConflict := match conflict with
      | some (cv, _) => cv.idx == v.idx
      | none => false
    let vReg ← if useConflict then
      match conflict with
      | some (_, reg) => pure (.phys reg)
      | none => varToReg v
    else
      varToReg v
    let actualReg := vReg

    -- Check if field needs boxing
    let vType ← getVarType v
    let needsBoxing := match vType with
      | some ty => ty.isScalar
      | none => false

    if needsBoxing then
      let ty := vType.getD .object
      emitComment s!"box {ty} field {fieldIdx}"
      emit (Instr.mov (.phys .x0) (.reg actualReg))

      -- Check if boxing requires a function call (destruction point)
      let boxingIsCall := match ty with
        | .usize | .uint64 | .float | .float32 => true
        | _ => false

      -- For calls, we need to handle ctorReg potentially being clobbered
      -- ctorReg is either a callee-saved register (x19-x28) or x8
      -- If it's x8, reload from the stack slot after the call

      match ty with
      | .usize => emit (Instr.bl "_lean_box_usize")
      | .uint64 => emit (Instr.bl "_lean_box_uint64")
      | .uint8 | .uint16 | .uint32 =>
        -- Inline box for small uints: (val << 1) | 1
        emit (Instr.lsl (.phys .x0) (.phys .x0) (.imm 1))
        emit (Instr.orr (.phys .x0) (.phys .x0) (.imm 1))
      | .float =>
        emit (Instr.fmov .double (.phys .v0) actualReg)
        emit (Instr.bl "_lean_box_float")
      | .float32 =>
        emit (Instr.fmov .single (.phys .v0) actualReg)
        emit (Instr.bl "_lean_box_float32")
      | _ =>
        emit (Instr.lsl (.phys .x0) (.phys .x0) (.imm 1))
        emit (Instr.orr (.phys .x0) (.phys .x0) (.imm 1))

      -- After boxing, x0 has the boxed value
      -- Determine which register holds the constructor pointer
      let finalCtorReg ← if boxingIsCall then
        match ctorReg with
        | .phys pr =>
          if pr.isCalleeSaved then
            pure ctorReg
          else
            match ctorStackOffset with
            | some offset =>
              emitComment "reload constructor from temp stack slot"
              emit (Instr.ldr (.phys pr) (.mem (.phys .sp) offset))
              pure ctorReg
            | none =>
              pure ctorReg
        | _ =>
          pure ctorReg
      else
        pure ctorReg

      -- Inline store: str x0, [ctorReg, #offset]
      emit (Instr.str (.phys .x0) (.mem finalCtorReg fieldOffset))

    else
      -- No boxing needed, direct inline store
      emit (Instr.str actualReg (.mem ctorReg fieldOffset))

    -- Release scratch registers used for spilled args once the value is stored.
    if !useConflict && (alloc.allocation.get? v.idx).isNone then
      match actualReg with
      | .phys pr =>
        let conflictReg := conflict.map (fun (_, reg) => reg)
        let ctorPhys := match ctorReg with
          | .phys p => some p
          | _ => none
        if RegClass.scratch.contains pr && conflictReg != some pr && ctorPhys != some pr then
          releaseScratch pr
      | _ => pure ()

  | .erased =>
    emitComment s!"field {fieldIdx} erased, set to lean_box(0) = 1"
    let tmp ← acquireScratch
    emit (Instr.mov (.phys tmp) (.imm 1))
    emit (Instr.str (.phys tmp) (.mem ctorReg fieldOffset))
    releaseScratch tmp

/-- Lower .ctor expression -/
def lowerCtor (dst : VarId) (info : CtorInfo) (args : Array Arg) : SelectM Unit := do
  let alloc ← getAllocResult
  let (dstReg, isSpilled) ← getDstReg dst
  emitComment s!"ctor {info.name} (tag={info.cidx}, objs={info.size}, usize={info.usize}, scalar={info.ssize})"

  -- Zero-sized constructors are either unboxed enums or boxed tags
  if info.size == 0 && info.usize == 0 && info.ssize == 0 then
    let dstTy ← getVarType dst
    match dstTy with
    | some ty =>
      if ty.isScalar then
        emit (Instr.mov dstReg (.imm (Int.ofNat info.cidx)))
      else
        lowerBoxedTag dstReg info.cidx
    | none =>
      lowerBoxedTag dstReg info.cidx
    if isSpilled then
      storeSpilledDst dst dstReg
    releaseAllScratch
    return

  -- Check for register conflicts
  let conflictVar ← if isSpilled then
    pure none
  else
    detectConflict dstReg args

  -- Allocate constructor
  emitAllocCtor info

  -- Move result to destination register (if not spilled)
  let ctorReg := dstReg
  let conflict ← match conflictVar with
    | some v => do
      let reg ← saveConflict v dstReg
      pure (some (v, reg))
    | none => pure none
  emit (Instr.mov ctorReg (.reg (.phys .x0)))

  let ctorStackOffset :=
    if isSpilled then
      alloc.stackSlots.get? dst.idx |>.map (fun slot => Int.ofNat (slot * 8))
    else
      none
  match ctorStackOffset with
  | some offset =>
    emitComment "store constructor for reuse across boxing calls"
    emit (Instr.str (.phys .x0) (.mem (.phys .sp) offset))
  | none => pure ()

  -- Set all fields (pass stack slot for potential reload after boxing calls)
  let ctorStackSlot := ctorStackOffset
  let mut conflictIdxs : Array Nat := #[]
  match conflict with
  | some (cv, _) =>
    for i in [:args.size] do
      match args[i]! with
      | .var v =>
        if v.idx == cv.idx then
          conflictIdxs := conflictIdxs.push i
      | .erased => pure ()
  | none => pure ()
  if conflictIdxs.isEmpty then
    for i in [:args.size] do
      let arg := args[i]!
      emitFieldSet i arg conflict ctorReg ctorStackSlot
  else
    for i in conflictIdxs do
      let arg := args[i]!
      emitFieldSet i arg conflict ctorReg ctorStackSlot
    for i in [:args.size] do
      if !conflictIdxs.contains i then
        let arg := args[i]!
        emitFieldSet i arg conflict ctorReg ctorStackSlot

  -- Final move to destination if needed
  if !isSpilled && ctorReg != dstReg then
    emit (Instr.mov dstReg (.reg ctorReg))

  releaseAllScratch

/-- Lower .reset expression -/
def lowerReset (dst : VarId) (n : Nat) (x : VarId) : SelectM Unit := do
  let alloc ← getAllocResult
  let xSpilled := (alloc.stackSlots.get? x.idx).isSome
  let loadX : SelectM Reg := do
    if xSpilled then
      loadSpilledVar x
    else
      varToReg x
  let releaseX (r : Reg) : SelectM Unit := do
    if xSpilled then
      match r with
      | .phys pr => releaseScratch pr
      | _ => pure ()
    else
      pure ()

  let (dstReg, isSpilled) ← getDstReg dst
  emitComment s!"reset {n}"

  -- Check exclusivity: non-scalar and rc == 1
  let rcReg ← acquireScratch
  let xRegCheck ← loadX
  let notExclusiveLabel ← freshLabel "reset_not_exclusive"
  let exclusiveLabel ← freshLabel "reset_exclusive"
  let doneLabel ← freshLabel "reset_done"
  emit (Instr.tst xRegCheck (.imm 1))
  emit (Instr.bCond Cond.ne notExclusiveLabel)
  emit (Instr.ldrw (.phys rcReg) (.mem xRegCheck 0))
  emit (Instr.cmp (.phys rcReg) (.imm 1))
  releaseX xRegCheck
  releaseScratch rcReg
  emit (Instr.bCond Cond.eq exclusiveLabel)
  emit (Instr.branch notExclusiveLabel)

  -- Not exclusive: dec_ref and return box(0)
  emit (Instr.label notExclusiveLabel)
  let xRegDec ← loadX
  emit (Instr.mov (.phys .x0) (.reg xRegDec))
  emit (Instr.bl "lean_dec_ref")
  releaseX xRegDec
  emit (Instr.mov dstReg (.imm 1))  -- lean_box(0)
  if isSpilled then
    storeSpilledDst dst dstReg
  emit (Instr.branch doneLabel)

  -- Exclusive: release fields and return original object
  emit (Instr.label exclusiveLabel)
  for i in [:n] do
    let fieldOffset := Int.ofNat (8 + i * 8)
    let xRegField ← loadX
    let fieldReg ← acquireScratch
    emit (Instr.ldr (.phys fieldReg) (.mem xRegField fieldOffset))
    emit (Instr.tst (.phys fieldReg) (.imm 1))
    let skipLabel ← freshLabel "reset_skip_dec"
    emit (Instr.bCond Cond.ne skipLabel)
    emit (Instr.mov (.phys .x0) (.reg (.phys fieldReg)))
    emit (Instr.bl "lean_dec_ref")
    emit (Instr.label skipLabel)
    emit (Instr.mov (.phys fieldReg) (.imm 1))
    if xSpilled then
      releaseX xRegField
      let xRegStore ← loadX
      emit (Instr.str (.phys fieldReg) (.mem xRegStore fieldOffset))
      releaseX xRegStore
    else
      emit (Instr.str (.phys fieldReg) (.mem xRegField fieldOffset))
      releaseX xRegField
    releaseScratch fieldReg

  let xRegFinal ← loadX
  emit (Instr.mov dstReg (.reg xRegFinal))
  if isSpilled then
    storeSpilledDst dst dstReg
  releaseX xRegFinal

  emit (Instr.label doneLabel)
  releaseAllScratch

/-- Lower .reuse expression -/
def lowerReuse (dst : VarId) (x : VarId) (info : CtorInfo)
    (updtHeader : Bool) (args : Array Arg) : SelectM Unit := do
  let alloc ← getAllocResult
  let (dstReg, isSpilled) ← getDstReg dst
  let xSpilled := (alloc.stackSlots.get? x.idx).isSome
  let loadX : SelectM Reg := do
    if xSpilled then
      loadSpilledVar x
    else
      varToReg x
  let releaseX (r : Reg) : SelectM Unit := do
    if xSpilled then
      match r with
      | .phys pr => releaseScratch pr
      | _ => pure ()
    else
      pure ()

  emitComment s!"reuse {info.name}"

  -- Check for conflicts
  let conflictVar ← if isSpilled then
    pure none
  else
    detectConflict dstReg args
  let conflict ← match conflictVar with
    | some v => do
      let reg ← saveConflict v dstReg
      pure (some (v, reg))
    | none => pure none
  let ctorReg := dstReg
  let ctorStackSlot :=
    if isSpilled then
      alloc.stackSlots.get? dst.idx |>.map (fun slot => Int.ofNat (slot * 8))
    else
      none
  let scalarLabel ← freshLabel "reuse_scalar"
  let setFieldsLabel ← freshLabel "reuse_set_fields"

  let xRegCheck ← loadX
  emit (Instr.tst xRegCheck (.imm 1))
  emit (Instr.bCond Cond.ne scalarLabel)

  -- Non-scalar: reuse object
  emit (Instr.mov ctorReg (.reg xRegCheck))
  match ctorStackSlot with
  | some offset =>
    emitComment "store reused object for reuse across boxing calls"
    emit (Instr.str ctorReg (.mem (.phys .sp) offset))
  | none => pure ()
  if updtHeader then
    emitComment s!"update tag to {info.cidx} (inline)"
    let tagReg ← acquireScratch
    emit (Instr.mov (.phys tagReg) (.imm (Int.ofNat info.cidx)))
    -- Tag is at byte offset 7 in the header (little-endian)
    emit (Instr.strb (.phys tagReg) (.mem ctorReg 7))
    releaseScratch tagReg
  releaseX xRegCheck
  emit (Instr.branch setFieldsLabel)

  -- Scalar: allocate new object
  emit (Instr.label scalarLabel)
  releaseX xRegCheck
  emitAllocCtor info
  emit (Instr.mov ctorReg (.reg (.phys .x0)))
  match ctorStackSlot with
  | some offset =>
    emitComment "store reused object for reuse across boxing calls"
    emit (Instr.str ctorReg (.mem (.phys .sp) offset))
  | none => pure ()

  emit (Instr.label setFieldsLabel)

  -- Set all fields
  let mut conflictIdxs : Array Nat := #[]
  match conflict with
  | some (cv, _) =>
    for i in [:args.size] do
      match args[i]! with
      | .var v =>
        if v.idx == cv.idx then
          conflictIdxs := conflictIdxs.push i
      | .erased => pure ()
  | none => pure ()
  if conflictIdxs.isEmpty then
    for i in [:args.size] do
      let arg := args[i]!
      emitFieldSet i arg conflict ctorReg ctorStackSlot
  else
    for i in conflictIdxs do
      let arg := args[i]!
      emitFieldSet i arg conflict ctorReg ctorStackSlot
    for i in [:args.size] do
      if !conflictIdxs.contains i then
        let arg := args[i]!
        emitFieldSet i arg conflict ctorReg ctorStackSlot

  -- Final move if needed
  if !isSpilled && ctorReg != dstReg then
    emit (Instr.mov dstReg (.reg ctorReg))

  releaseAllScratch

end Lean.Compiler.Backend.ARM64.Lower.Constructor

end
