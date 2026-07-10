/-
Copyright (c) 2025 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Assistant
-/

module

prelude
public import Lean.Compiler.Backend.ARM64.Lower.Base

public section

namespace Lean.Compiler.Backend.ARM64.Lower.Control

/-!
# Control Flow Lowering

Handles control flow operations:
- .case: Pattern matching / tag dispatch
- .ret: Function return
- .jmp: Jump to join point
- .jdecl: Join point declaration
- .unreachable: Unreachable code marker
-/

open Lean.IR
open Lean.Compiler.Backend.ARM64

/-- Load a spilled variable from its stack slot -/
def loadSpilledVar (v : VarId) (slot : Nat) : SelectM Reg := do
  let ty := (← read).varTypes.get? v.idx |>.getD .object
  let offset := slot * 8
  let scratch ← acquireScratchForType ty
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

/-- Store value to a stack slot -/
def storeToStackSlot' (srcReg : Reg) (slot : Nat) (ty : IRType) : SelectM Unit := do
  let offset := Int.ofNat (slot * 8)
  if ty == .uint8 then
    emit (Instr.strb srcReg (.mem (.phys .sp) offset))
  else if ty == .uint16 then
    emit (Instr.strh srcReg (.mem (.phys .sp) offset))
  else if ty == .uint32 then
    emit (Instr.strw srcReg (.mem (.phys .sp) offset))
  else if ty == .float32 then
    emit (Instr.strs srcReg (.mem (.phys .sp) offset))
  else if ty == .float then
    emit (Instr.strd srcReg (.mem (.phys .sp) offset))
  else
    emit (Instr.str srcReg (.mem (.phys .sp) offset))

/- Location for join point moves. -/
inductive PhiLoc where
  | reg (r : PhysReg)
  | stack (slot : Nat)
  | imm (val : Int)
  deriving Inhabited, BEq, DecidableEq, Repr

/- Move for join point parameter assignment. -/
structure PhiMove where
  src : PhiLoc
  dst : PhiLoc
  ty : IRType
  deriving Inhabited, Repr

/- Load a value from a stack slot into a register. -/
def loadFromStackSlot (dst : Reg) (slot : Nat) (ty : IRType) : SelectM Unit := do
  let offset := Int.ofNat (slot * 8)
  if ty == .uint8 then
    emit (Instr.ldrb dst (.mem (.phys .sp) offset))
  else if ty == .uint16 then
    emit (Instr.ldrh dst (.mem (.phys .sp) offset))
  else if ty == .uint32 then
    emit (Instr.ldrw dst (.mem (.phys .sp) offset))
  else if ty == .float32 then
    emit (Instr.ldrs dst (.mem (.phys .sp) offset))
  else if ty == .float then
    emit (Instr.ldrd dst (.mem (.phys .sp) offset))
  else
    emit (Instr.ldr dst (.mem (.phys .sp) offset))

/- Emit a single join point move. -/
def emitPhiMove (move : PhiMove) : SelectM Unit := do
  match move.src, move.dst with
  | .reg srcReg, .reg dstReg =>
    if srcReg != dstReg then
      if move.ty == .float || move.ty == .float32 then
        let prec := typeToFloatPrec move.ty
        emit (Instr.fmov prec (.phys dstReg) (.phys srcReg))
      else
        emitMove (.phys dstReg) (.reg (.phys srcReg))
  | .reg srcReg, .stack slot =>
    storeToStackSlot' (.phys srcReg) slot move.ty
  | .stack slot, .reg dstReg =>
    loadFromStackSlot (.phys dstReg) slot move.ty
  | .stack srcSlot, .stack dstSlot =>
    if srcSlot != dstSlot then
      let tmp ← acquireScratchForType move.ty
      loadFromStackSlot (.phys tmp) srcSlot move.ty
      storeToStackSlot' (.phys tmp) dstSlot move.ty
      releaseScratch tmp
  | .imm val, .reg dstReg =>
    if move.ty == .float || move.ty == .float32 then
      emitMove (.phys dstReg) (.reg (.phys PhysReg.xzr))
    else
      emit (Instr.mov (.phys dstReg) (.imm val))
  | .imm val, .stack slot =>
    let tmp ← acquireScratchForType move.ty
    if move.ty == .float || move.ty == .float32 then
      emitMove (.phys tmp) (.reg (.phys PhysReg.xzr))
    else
      emit (Instr.mov (.phys tmp) (.imm val))
    storeToStackSlot' (.phys tmp) slot move.ty
    releaseScratch tmp
  | _, .imm _ =>
    emitComment "ERROR: phi move to immediate"

/- Emit parallel join point moves with cycle breaking. -/
partial def emitParallelMoves (moves : Array PhiMove) : SelectM Unit := do
  let rec loop (pending : Array PhiMove) (temps : Array PhysReg) : SelectM Unit := do
    if pending.isEmpty then
      pure ()
    else
      let sources := pending.foldl (init := #[]) fun acc m =>
        match m.src with
        | .imm _ => acc
        | _ => if acc.contains m.src then acc else acc.push m.src
      match pending.findIdx? (fun m => !(sources.contains m.dst)) with
      | some idx =>
        let m := pending[idx]!
        emitPhiMove m
        let pending' := pending.eraseIdx! idx
        let temps' ←
          match m.src with
          | .reg r =>
            if temps.contains r && !(pending'.any (fun p => p.src == .reg r)) then
              releaseScratch r
              pure (temps.filter (· != r))
            else
              pure temps
          | _ => pure temps
        loop pending' temps'
      | none =>
        let m := pending[0]!
        let temp ← acquireScratchForType m.ty
        emitPhiMove { src := m.src, dst := .reg temp, ty := m.ty }
        let pending' := (pending.eraseIdx! 0).push { src := .reg temp, dst := m.dst, ty := m.ty }
        loop pending' (temps.push temp)
  loop moves #[]

/-- Lower .case expression (pattern matching) -/
def lowerCase (x : VarId) (xType : IRType) (alts : Array Alt)
    (selectBody : FnBody → SelectM Unit) : SelectM Unit := do
  let xReg ← varToReg x
  let alloc ← getAllocResult
  let xSpilled := (alloc.allocation.get? x.idx).isNone

  emitComment "case"

  let tagReg ← acquireScratch

  -- Extract tag based on type
  if xType.isScalar then
    -- For scalar types, the value is already in the register
    emit (Instr.mov (.phys tagReg) (.reg xReg))
  else if xType.isObj then
    -- For `tagged` or `object` types, value can be scalar OR pointer at runtime
    let scalarLabel ← freshLabel "scalar_tag"
    let compareLabel ← freshLabel "compare_tag"
    emitComment "runtime scalar check"
    emit (Instr.tst xReg (.imm 1))
    emit (Instr.bCond Cond.ne scalarLabel)
    -- Pointer case: load tag from object header
    emit (Instr.ldrb (.phys tagReg) (.mem xReg 7))
    emit (Instr.branch compareLabel)
    -- Scalar case: unbox to get tag (shift right by 1)
    emit (Instr.label scalarLabel)
    emit (Instr.lsr (.phys tagReg) xReg (.imm 1))
    emit (Instr.label compareLabel)
  else
    -- Unknown type, assume pointer
    emit (Instr.ldrb (.phys tagReg) (.mem xReg 7))

  let endLabel ← freshLabel "case_end"

  -- Generate branch targets
  let mut ctorLabels : Array (String × Alt) := #[]
  let mut defaultAlt : Option (String × Alt) := none

  for alt in alts do
    match alt with
    | .ctor info _ =>
      let label ← freshLabel "case_ctor"
      ctorLabels := ctorLabels.push (label, alt)
      emit (Instr.cmp (.phys tagReg) (.imm (Int.ofNat info.cidx)))
      emit (Instr.bCond Cond.eq label)
    | .default _ =>
      let label ← freshLabel "case_default"
      defaultAlt := some (label, alt)

  match defaultAlt with
  | some (label, _) => emit (Instr.branch label)
  | none => emit (Instr.branch endLabel)

  releaseScratch tagReg
  if xSpilled then
    match xReg with
    | .phys pr =>
      if RegClass.scratch.contains pr then
        releaseScratch pr
    | _ => pure ()

  -- Emit constructor arms
  for (label, alt) in ctorLabels do
    emit (Instr.label label)
    selectBody (Alt.body alt)
    emit (Instr.branch endLabel)

  -- Emit default arm if present
  match defaultAlt with
  | some (label, alt) =>
    emit (Instr.label label)
    selectBody (Alt.body alt)
    emit (Instr.branch endLabel)
  | none => pure ()

  emit (Instr.label endLabel)
  -- Unmatched tag: treat as unreachable but restore the stack to avoid fallthrough corruption.
  let spillBytes ← getSpillBytes
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
  emit (Instr.bl "lean_internal_panic_unreachable")
  emit Instr.ret

/-- Lower .ret expression (function return) -/
def lowerRet (arg : Arg) (retTy : IRType) (spillBytes : Nat) : SelectM Unit := do
  emitComment "return"

  match arg with
  | .var v =>
    let vReg ← varToReg v
    if retTy == IRType.float then
      emit (Instr.fmov FloatPrec.double (.phys PhysReg.v0) vReg)
    else if retTy == IRType.float32 then
      emit (Instr.fmov FloatPrec.single (.phys PhysReg.v0) vReg)
    else
      emitMove (.phys PhysReg.x0) (.reg vReg)
  | .erased =>
    emit (Instr.mov (.phys PhysReg.x0) (.imm 0))

  -- Restore stack
  if spillBytes > 0 then
    emitStackAdd spillBytes

  -- Only restore callee-saved registers that were saved (reverse order of prologue)
  let usedGP ← getUsedCalleeSavedGP
  let usedFP ← getUsedCalleeSavedFP
  let fpPairs := getCalleeSavedFPPairs usedFP
  let pairs := getCalleeSavedPairs usedGP
  -- Pop in reverse order (last saved = first popped)
  for pair in fpPairs.reverse do
    emit (Instr.pop pair)
  for pair in pairs.reverse do
    emit (Instr.pop pair)

  emit (Instr.pop #[Reg.phys PhysReg.x29, Reg.phys PhysReg.x30])
  emit Instr.ret

/-- Lower .jmp expression (jump to join point) -/
def lowerJmp (j : JoinPointId) (args : Array Arg) : SelectM Unit := do
  emitComment s!"jump to JP{j.idx}"

  let alloc ← getAllocResult
  let jpParams ← getJPParams j

  match jpParams with
  | none =>
    -- No parameters, just jump
    let label ← getJPLabel j
    emit (Instr.branch label)
  | some params =>
    let varTypes := (← read).varTypes
    let getVarLoc? (v : VarId) : Option PhiLoc :=
      match alloc.allocation.get? v.idx with
      | some reg => some (.reg reg)
      | none =>
        match alloc.stackSlots.get? v.idx with
        | some slot => some (.stack slot)
        | none => none

    -- Phi resolution: move arguments into parameter locations
    let mut moves : Array PhiMove := #[]
    for i in [:min args.size params.size] do
      let arg := args[i]!
      let param := params[i]!
      let paramTy := varTypes.get? param.idx |>.getD IRType.object
      let dstLoc? := getVarLoc? param

      match arg with
      | .var argVar =>
        let srcLoc? := getVarLoc? argVar
        match srcLoc?, dstLoc? with
        | some srcLoc, some dstLoc =>
          if srcLoc != dstLoc then
            moves := moves.push { src := srcLoc, dst := dstLoc, ty := paramTy }
        | _, _ =>
          emitComment s!"ERROR: phi arg vreg{argVar.idx} or param vreg{param.idx} not allocated!"
      | .erased =>
        match dstLoc? with
        | some dstLoc =>
          let immVal := if paramTy.isObj then 1 else 0
          moves := moves.push { src := .imm (Int.ofNat immVal), dst := dstLoc, ty := paramTy }
        | none =>
          emitComment s!"ERROR: phi param vreg{param.idx} not allocated!"

    emitParallelMoves moves
    let label ← getJPLabel j
    emit (Instr.branch label)

  releaseAllScratch

/-- Lower .jdecl (join point declaration) -/
def lowerJDecl (j : JoinPointId) (params : Array Param) : SelectM Unit := do
  -- Register join point parameters
  let paramVars := params.map (·.x)
  registerJPParams j paramVars

  -- Register parameter types
  for param in params do
    registerVarType param.x param.ty

/-- Lower join point body (emit label and compile body) -/
def lowerJDeclBody (j : JoinPointId) (body : FnBody)
    (selectBody : FnBody → SelectM Unit) : SelectM Unit := do
  let label ← getJPLabel j
  emit (Instr.label label)
  selectBody body

/-- Lower .unreachable -/
def lowerUnreachable : SelectM Unit := do
  emitComment "unreachable"
  emit Instr.ret

/-- Lower field set operations (inlined) -/
def lowerSet (x : VarId) (i : Nat) (y : Arg) : SelectM Unit := do
  let xReg ← varToReg x
  emitComment s!"set field {i} (inline)"
  -- Inline store: field offset = 8 (header) + i * 8
  let fieldOffset := Int.ofNat (8 + i * 8)
  match y with
  | .var v =>
    let yReg ← varToReg v
    emit (Instr.str yReg (.mem xReg fieldOffset))
  | .erased =>
    -- lean_box(0) = 1
    let tmp ← acquireScratch
    emit (Instr.mov (.phys tmp) (.imm 1))
    emit (Instr.str (.phys tmp) (.mem xReg fieldOffset))
    releaseScratch tmp
  releaseAllScratch

/-- Lower usize field set -/
def lowerUSet (x : VarId) (i : Nat) (y : VarId) : SelectM Unit := do
  let xReg ← varToReg x
  let yReg ← varToReg y
  emitComment s!"uset field {i}"
  -- Inline store: offset = 8 + i * 8
  let offset := 8 + i * 8
  emit (Instr.str yReg (.mem xReg (Int.ofNat offset)))
  releaseAllScratch

/-- Lower scalar field set -/
def lowerSSet (x : VarId) (n : Nat) (offset : Nat) (y : VarId) (ty : IRType) : SelectM Unit := do
  let xReg ← varToReg x
  let yReg ← varToReg y
  emitComment s!"sset scalar {n} offset {offset}"
  -- Scalar offset: 8 (header) + n * 8 (usize fields) + offset
  let totalOffset := 8 + n * 8 + offset
  if ty == .uint8 then
    emit (Instr.strb yReg (.mem xReg (Int.ofNat totalOffset)))
  else if ty == .uint16 then
    emit (Instr.strh yReg (.mem xReg (Int.ofNat totalOffset)))
  else if ty == .uint32 then
    emit (Instr.strw yReg (.mem xReg (Int.ofNat totalOffset)))
  else if ty == .float32 then
    emit (Instr.strs yReg (.mem xReg (Int.ofNat totalOffset)))
  else if ty == .float then
    emit (Instr.strd yReg (.mem xReg (Int.ofNat totalOffset)))
  else
    emit (Instr.str yReg (.mem xReg (Int.ofNat totalOffset)))
  releaseAllScratch

/-- Lower setTag (inlined) -/
def lowerSetTag (x : VarId) (tag : Nat) : SelectM Unit := do
  let xReg ← varToReg x
  emitComment s!"setTag {tag} (inline)"
  -- m_tag is at offset 7 in lean_object header (little-endian layout)
  let tempReg ← acquireScratch
  emit (Instr.mov (.phys tempReg) (.imm (Int.ofNat tag)))
  emit (Instr.strb (.phys tempReg) (.mem xReg 7))
  releaseScratch tempReg
  releaseAllScratch

end Lean.Compiler.Backend.ARM64.Lower.Control

end
