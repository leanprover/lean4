/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez, Sebastian Ullrich
-/
module

prelude
public import Lean.Compiler.LCNF.Basic
public import Lean.Compiler.Bytecode.Instruction
import Lean.Compiler.Bytecode.Sorry
import Lean.Compiler.LCNF.PrettyPrinter
import Init.While
public meta import Lean.Elab.Term.TermElabM

public section

namespace Lean.Compiler.Bytecode

open LCNF ImpureType

namespace ToBytecode

structure RegAlloc where
  used : Nat := 0 -- bit set
  map : Std.HashMap FVarId (Array Nat) := {}
  max : Nat := 0
deriving Inhabited

def RegAlloc.isFree (reg : RegAlloc) (i : Nat) : Bool :=
  !reg.used.testBit i

def RegAlloc.allocAt (reg : RegAlloc) (pos : Nat) : RegAlloc :=
  let bit := 1 <<< pos
  { reg with used := reg.used ||| bit, max := reg.max.max (pos + 1) }

def RegAlloc.alloc (reg : RegAlloc) : Nat × RegAlloc :=
  let bit := ((reg.used + 1) ^^^ reg.used) &&& (reg.used + 1) -- first unset bit
  let pos := bit.log2
  (pos, { reg with used := reg.used ||| bit, max := reg.max.max (pos + 1) })

def RegAlloc.allocN (reg : RegAlloc) (n : Nat) : Array Nat × RegAlloc :=
  go n reg #[]
where
  go (n : Nat) (reg : RegAlloc) (acc : Array Nat) : Array Nat × RegAlloc :=
    match n with
    | 0 => (acc, reg)
    | k + 1 =>
      let (i, reg) := reg.alloc
      go k reg (acc.push i)

def computeRegSpace (type : Expr) : Nat :=
  match type with
  | erased | void => 0
  | _ => 1 -- TODO: unboxed types

def computeCallsideSpace (type : Expr) : Nat :=
  match type with
  | void => 0
  | _ => 1 -- TODO: unboxed types

def RegAlloc.allocVar (reg : RegAlloc) (v : FVarId) (ty : Expr) : RegAlloc :=
  let (as, reg) := reg.allocN (computeRegSpace ty)
  { reg with map := reg.map.insert v as }

def RegAlloc.allocPreferred (reg : RegAlloc) (v : FVarId) (preferred : Array Nat) :
    RegAlloc := Id.run do
  let mut reg := reg
  let mut out := #[]
  for p in preferred do
    if reg.isFree p then
      reg := reg.allocAt p
      out := out.push p
    else
      let (fresh, newReg) := reg.alloc
      out := out.push fresh
      reg := newReg
  { reg with map := reg.map.insert v out }

def RegAlloc.deallocVar (reg : RegAlloc) (v : FVarId) : RegAlloc :=
  match reg.map.get? v with
  | none => reg
  | some as =>
    let map := reg.map.erase v
    let used := as.foldl (fun used i => used ^^^ (1 <<< i)) reg.used
    { reg with used, map }

def RegAlloc.findLocs (reg : RegAlloc) (v : FVarId) : Array Nat :=
  reg.map.get! v

def RegAlloc.findObj! (reg : RegAlloc) (v : FVarId) : Nat :=
  (reg.findLocs v)[0]!

inductive FixUp where
  | argRel (whereBbRev whereIndexRev : Nat) (bitoff bitlen : Nat)
  | basicBlockRef (whereBbRev whereIndexRev : Nat) (targetBbRev : Nat) (bitlen : Nat)
  | beginRef (whereBbRev whereIndexRev : Nat) (bitlen : Nat)
deriving Inhabited

inductive ComplexInstruction where
  | move (tgt src : Nat) (argTgt argSrc : Bool)
  | eraseArg (tgt : Nat)
  | referToTempSpot (base : Instruction) (bitoff : UInt32)
  | jumpToBB (targetRev : Nat)
  | jumpToBeginning
deriving Inhabited

structure JoinPointState where
  paramInfo : Array (Array Nat)
  bb : Nat
deriving Inhabited

structure State where
  /-- Order of blocks reversed, each block in reverse order -/
  revBasicBlocks : Array (Array Instruction) := #[]
  revCurrBlock : Array Instruction := #[]
  symbols : Array Name := #[]
  symbolTable : Std.HashMap Name Nat := {}
  joinPoints : Std.HashMap FVarId JoinPointState := {}
  constants : Array NonScalar := #[]
  constantTable : Std.HashMap LitValue Nat := {}
  complex : Array ComplexInstruction := #[]
  regAlloc : RegAlloc := {}
  returnBb : Option Nat := none -- only for constants

structure Context where
  currDecl : Name
  params : Array (Param .impure)

abbrev M := ReaderT Context <| StateRefT State CompilerM

elab tk:"where_am_i%" : term => do
  let some info := tk.getInfo? | return toExpr 0
  let some pos := info.getPos? | return toExpr 0
  let pos := (← getFileMap).toPosition pos
  return toExpr pos.line

@[inline]
def as (val : Nat) (bits : Nat) (decl : Name := by exact decl_name%)
    (pos : Nat := by exact where_am_i%) : M UInt32 := do
  if val < 1 <<< bits then
    return val.toUInt32
  else
    throwError "Instruction argument out of range: {val} for {bits} at {decl}:{pos}"

def emit (instr : Instruction) : M Unit := do
  modify fun state => { state with revCurrBlock := state.revCurrBlock.push instr }

def emitComplex (instr : ComplexInstruction) : M Unit := do
  let i := (← get).complex.size
  emit (.assemblerInternal (← as i 26))
  modify fun state => { state with complex := state.complex.push instr }

def emitJump (targetBb : Nat) : M Unit := do
  if (← get).revCurrBlock.isEmpty ∧ targetBb + 1 = (← get).revBasicBlocks.size then
    return
  emitComplex (.jumpToBB targetBb)

@[inline] def numTemps := 3
@[inline] def normalRange := 256 - numTemps

def adjustStackSpace (tgt : Nat) : Nat :=
  if tgt < normalRange then tgt else tgt + numTemps

def maybeTarget (var : Nat) (inner : Bool := false) : Nat :=
  if var < normalRange then var else if inner then 254 else 255

def maybeToTemp (var : Nat) (inner : Bool := false) : M Unit := do
  if var < normalRange then
    return
  let pos := if inner then 254 else 255
  emit (.move pos (← as (var + numTemps) 13))

def maybeFromTemp (var : Nat) (inner : Bool := false) : M Nat := do
  if var < normalRange then
    return var
  let pos := if inner then 254 else 255
  emit (.move (← as (var + numTemps) 13) pos)
  return pos.toNat

def emitMove (tgt src : Nat) : M Unit := do
  let tgt := adjustStackSpace tgt
  let src := adjustStackSpace src
  emit (.move (← as tgt 13) (← as src 13))

def emitMoveToReal (tgt src : Nat) : M Unit := do
  let src := adjustStackSpace src
  emit (.move (← as tgt 8) (← as src 13))

def emitMoveToArg (tgt src : Nat) : M Unit := do
  emitComplex (.move tgt src (argTgt := true) (argSrc := false))

def emitMoveFromArg (tgt src : Nat) : M Unit := do
  emitComplex (.move tgt src (argTgt := false) (argSrc := true))

def emitMoveWithinArgs (tgt src : Nat) : M Unit := do
  emitComplex (.move tgt src (argTgt := true) (argSrc := true))

def emitErasedTo (tgt : Nat) : M Unit := do
  let tgt' ← maybeFromTemp tgt
  emit (.uconst (← as tgt' 8) 1)

def emitErasedToArg (tgt : Nat) : M Unit := do
  emitComplex (.eraseArg tgt)

def endBlock : M Nat := do
  let bb := (← get).revBasicBlocks.size
  if (← get).revCurrBlock.isEmpty then
    return bb - 1
  modify fun state => {
    state with
    revBasicBlocks := state.revBasicBlocks.push state.revCurrBlock
    revCurrBlock := #[]
  }
  return bb

def recordSymbol (sym : Name) : M Nat := do
  if let some i := (← get).symbolTable[sym]? then
    return i
  let i := (← get).symbols.size
  modify fun state => {
    state with
    symbols := state.symbols.push sym,
    symbolTable := state.symbolTable.insert sym i
  }
  return i

def declareVar (v : FVarId) : M Unit := do
  modify fun state => { state with regAlloc := state.regAlloc.deallocVar v }

def useVar (v : FVarId) : M (Array Nat) := do
  if let some res := (← get).regAlloc.map[v]? then
    return res
  let type ← getType v
  modify fun state => { state with regAlloc := state.regAlloc.allocVar v type }
  return (← get).regAlloc.map[v]!

def useVarJmp (v : FVarId) (preferred : Array Nat) : M (Array Nat) := do
  if let some res := (← get).regAlloc.map[v]? then
    return res
  modify fun state => { state with regAlloc := state.regAlloc.allocPreferred v preferred }
  return (← get).regAlloc.map[v]!

def parallelAssignment (lhss rhss : Array Nat) : M Unit := do
  let mut assignedBefore : Std.HashSet Nat := {}
  for lhs in lhss, rhs in rhss do
    if lhs = rhs then
      continue
    assignedBefore := assignedBefore.insert lhs
  let mut tempVars : Array (Nat × Nat) := {}
  let mut i := lhss.size
  while i > 0 do
    i := i - 1
    let lhs := lhss[i]!
    let rhs := rhss[i]!
    if lhs = rhs then
      continue
    assignedBefore := assignedBefore.erase lhs
    if assignedBefore.contains rhs then
      let tmpIdx := tempVars.size
      tempVars := tempVars.push (rhs, tmpIdx)
      emitMoveFromArg lhs tmpIdx -- used as temporary storage
    else
      emitMove lhs rhs
  for (rhs, tmpIdx) in tempVars do
    emitMoveToArg tmpIdx rhs

def prepareCallArgs (args : Array (Arg .impure)) (params : Array (Param .impure)) : M Unit := do
  let mut pos := 0
  let mut sizes := #[]
  for param in params do
    let size := computeCallsideSpace param.type
    sizes := sizes.push size
    pos := pos + size
  let mut i := args.size
  while i > 0 do
    i := i - 1
    let arg := args[i]!
    let size := sizes[i]!
    pos := pos - size
    match arg with
    | .erased =>
      if size != 0 then
        emitErasedToArg pos
    | .fvar var =>
      let x ← useVar var
      if size = 0 then
        emitErasedToArg pos
      else
        assert! x.size = size
        for j in 0...size do
          emitMoveToArg (pos + j) x[j]!

-- equivalent to `prepareCallArgs args (Array.replicate { type := tobject, .. } args.size)`
def prepareCallArgsSimple (args : Array (Arg .impure)) : M Unit := do
  let mut i := args.size
  while i > 0 do
    i := i - 1
    let arg := args[i]!
    match arg with
    | .erased => emitErasedToArg i
    | .fvar var =>
      let x ← useVar var
      if x.isEmpty then
        emitErasedToArg i
      else
        assert! x.size = 1
        emitMoveToArg i x[0]!

def setCtorArgs (tgt : Nat) (args : Array (Arg .impure)) : M Unit := do
  let mut i := args.size
  let mut hadErased := false
  while i > 0 do
    i := i - 1
    let arg := args[i]!
    match arg with
    | .fvar var =>
      let #[v] ← useVar var | throwError "Unexpected size for constructor argument"
      let v' := maybeTarget v (inner := true)
      emit (.set (← as tgt 8) (← as v' 8) (← as i 8))
      maybeToTemp v (inner := true)
    | .erased =>
      emitComplex (.referToTempSpot (.set (← as tgt 8) 0 (← as i 8)) 8)
      hadErased := true
  if hadErased then
    emitComplex (.referToTempSpot (.uconst 0 1) 18)

unsafe def addConstant (lit : LitValue) (value : α) : M Nat := do
  if let some idx := (← get).constantTable[lit]? then
    return idx
  let i := (← get).constants.size
  modify fun state => {
    state with
    constants := state.constants.push (unsafeCast value),
    constantTable := state.constantTable.insert lit i
  }
  return i

def computeScalar (usize ssize : Nat) : M Unit := do
  if ssize = 0 ∧ usize = 0 then
    return
  emit (.computeScalar (← as usize 13) (← as ssize 13))

def processLetDecl (decl : LetDecl .impure) : M Unit := do
  let vars? := (← get).regAlloc.map[decl.fvarId]?
  match decl.value with
  | .lit value =>
    let some #[var] := vars? | return -- return if unused
    let var' ← maybeFromTemp var
    match value with
    | .uint8 val => emit (.uconst (← as var' 8) val.toUInt32)
    | .uint16 val => emit (.uconst (← as var' 8) val.toUInt32)
    | .uint32 val =>
      if val.toNat ≤ maxUConst then
        emit (.uconst (← as var' 8) val)
      else
        let constId ← unsafe addConstant value val
        emit (.unboxUInt32 (← as var' 8) (← as var' 8))
        emit (.declConst (← as var' 8) (← as constId 18))
    | .uint64 val =>
      if val.toNat ≤ maxUConst then
        emit (.uconst (← as var' 8) val.toUInt32)
      else
        let constId ← unsafe addConstant value val
        emit (.unboxUInt64 (← as var' 8) (← as var' 8))
        emit (.declConst (← as var' 8) (← as constId 18))
    | .usize val =>
      if val.toNat ≤ maxUConst then
        emit (.uconst (← as var' 8) val.toUInt32)
      else
        let constId ← unsafe addConstant value val
        emit (.unboxUSize (← as var' 8) (← as var' 8))
        emit (.declConst (← as var' 8) (← as constId 18))
    | .nat val =>
      if val ≤ maxNConst then
        emit (.nconst (← as var' 8) val.toUInt32)
      else
        let constId ← unsafe addConstant value val
        unless unsafe isScalarObj val do
          emit (.inc (← as var' 8) 1)
        emit (.declConst (← as var' 8) (← as constId 18))
    | .str s =>
      let constId ← unsafe addConstant value s
      emit (.inc (← as var' 8) 1)
      emit (.declConst (← as var' 8) (← as constId 18))
  | .erased =>
    let some #[var] := vars? | return -- return if unused
    emitErasedTo var
  | .fvar fvarId args =>
    let #[fn] ← useVar fvarId | throwError "Unexpected size for function"
    if let some #[var] := vars? then
      emitMoveFromArg var 0
      declareVar decl.fvarId
    emit (.app (← as (adjustStackSpace fn) 16) (← as args.size 10))
    prepareCallArgsSimple args
  | .ctor info args =>
    if info.isScalar then
      if let some #[tgt] := vars? then
        let tgt' ← maybeFromTemp tgt
        emit (.nconst (← as tgt' 8) (← as info.cidx 18))
      return
    let some #[tgt] := vars? | throwError "Result of constructor leaked"
    let tgt' ← maybeFromTemp tgt
    setCtorArgs tgt' args
    emit (.allocCtor (← as tgt' 8) (← as info.cidx 10) (← as info.size 8))
    computeScalar info.usize info.ssize
  | .fap fn args =>
    let some sig ← getImpureSignature? fn | throwError "Missing impure signature for `{fn}`"
    if let some vars := vars? then
      let mut i := vars.size
      while i > 0 do
        i := i - 1
        emitMoveFromArg vars[i]! i
      declareVar decl.fvarId
    if args.isEmpty then
      emit (.loadConst (← as (← recordSymbol fn) 16))
    else
      emit (.call (← as (← recordSymbol fn) 16))
      prepareCallArgs args sig.params
  | .pap fn args =>
    if let some #[var] := vars? then
      emitMoveFromArg var 0
      declareVar decl.fvarId
    emit (.pap (← as (← recordSymbol fn) 16) (← as args.size 10))
    prepareCallArgsSimple args
  | .oproj i var =>
    let some #[tgt] := vars? | return -- return if unused
    let tgt' ← maybeFromTemp tgt
    let #[src] ← useVar var | throwError "Unexpected input size for projection"
    let src' := maybeTarget src (inner := true)
    emit (.proj (← as tgt' 8) (← as src' 8) (← as i 8))
    maybeToTemp src (inner := true)
  | .uproj i var =>
    let some #[tgt] := vars? | return -- return if unused
    let tgt' ← maybeFromTemp tgt
    let #[src] ← useVar var | throwError "Unexpected input size for projection"
    let src' := maybeTarget src (inner := true)
    emit (.uproj (← as tgt' 8) (← as src' 8) (← as i 8))
    maybeToTemp src (inner := true)
  | .sproj i offset var =>
    let some #[tgt] := vars? | return -- return if unused
    let tgt' ← maybeFromTemp tgt
    let #[src] ← useVar var | throwError "Unexpected input size for projection"
    let src' := maybeTarget src (inner := true)
    match decl.type with
    | uint8 => emit (.sproj8 (← as tgt' 8) (← as src' 8))
    | uint16 => emit (.sproj16 (← as tgt' 8) (← as src' 8))
    | uint32 => emit (.sproj32 (← as tgt' 8) (← as src' 8))
    | uint64 => emit (.sproj64 (← as tgt' 8) (← as src' 8))
    | float32 => emit (.sproj32 (← as tgt' 8) (← as src' 8))
    | float => emit (.sproj64 (← as tgt' 8) (← as src' 8))
    | _ => unreachable!
    computeScalar i offset
    maybeToTemp src (inner := true)
  | .reset n var =>
    let some #[tgt] := vars? | throwError "Result of reset leaked"
    let tgt' ← maybeFromTemp tgt
    let #[src] ← useVar var | throwError "Unexpected input size for reset"
    let src' := maybeTarget src (inner := true)
    emit (.reset (← as n 8) (← as tgt' 8) (← as src' 8))
    maybeToTemp src (inner := true)
  | .reuse var i _updateHeader args =>
    let some #[tgt] := vars? | throwError "Result of reuse leaked"
    let tgt' ← maybeFromTemp tgt
    let #[src] ← useVar var | throwError "Unexpected input size for reuse"
    setCtorArgs tgt' args
    emit (.reuse (← as tgt' 8) (← as i.cidx 10) (← as i.size 8))
    computeScalar i.usize i.ssize
    unless src = tgt' do
      emitMoveToReal tgt' src
  | .box ty var =>
    let some #[tgt] := vars? | throwError "Result of box leaked"
    let tgt' ← maybeFromTemp tgt
    let #[src] ← useVar var | throwError "Unexpected input size for boxing function"
    let src' := maybeTarget src (inner := true)
    match ty with
    | uint8 | uint16 => emit (.boxSmall (← as tgt' 8) (← as src' 8))
    | uint32 => emit (.boxUInt32 (← as tgt' 8) (← as src' 8))
    | uint64 => emit (.boxUInt64 (← as tgt' 8) (← as src' 8))
    | usize => emit (.boxUSize (← as tgt' 8) (← as src' 8))
    | float32 => emit (.boxFloat32 (← as tgt' 8) (← as src' 8))
    | float => emit (.boxFloat (← as tgt' 8) (← as src' 8))
    | _ => unreachable!
    maybeToTemp src (inner := true)
  | .unbox var =>
    let some #[tgt] := vars? | return -- return if unused
    let tgt' ← maybeFromTemp tgt
    let #[src] ← useVar var | throwError "Unexpected input size for boxing function"
    let src' := maybeTarget src (inner := true)
    match decl.type with
    | uint8 | uint16 => emit (.unboxSmall (← as tgt' 8) (← as src' 8))
    | uint32 => emit (.unboxUInt32 (← as tgt' 8) (← as src' 8))
    | uint64 => emit (.unboxUInt64 (← as tgt' 8) (← as src' 8))
    | usize => emit (.unboxUSize (← as tgt' 8) (← as src' 8))
    | float32 => emit (.unboxFloat32 (← as tgt' 8) (← as src' 8))
    | float => emit (.unboxFloat (← as tgt' 8) (← as src' 8))
    | _ => unreachable!
    maybeToTemp src (inner := true)
  | .isShared fvarId =>
    let some #[tgt] := vars? | return -- return if unused
    let tgt' ← maybeFromTemp tgt
    let #[src] ← useVar fvarId | throwError "Unexpected input size for boxing function"
    let src' := maybeTarget src (inner := true)
    emit (.isShared (← as tgt' 8) (← as src' 8))
    maybeToTemp src (inner := true)

def processInstruction (decl : CodeDecl .impure) : M Unit := do
  match decl with
  | .let ldecl =>
    processLetDecl ldecl
    declareVar ldecl.fvarId -- if not already done above
  | .oset v i y =>
    let #[tgt] ← useVar v | throwError "Unexpected target size for set"
    let tgt' := maybeTarget tgt
    match y with
    | .fvar var =>
      let #[src] ← useVar var | throwError "Unexpected input size for projection"
      let src' := maybeTarget src (inner := true)
      emit (.set (← as tgt' 8) (← as src' 8) (← as i 8))
      maybeToTemp src (inner := true)
    | .erased =>
      emitComplex (.referToTempSpot (.set (← as tgt' 8) 0 (← as i 8)) 8)
      emitComplex (.referToTempSpot (.uconst 0 1) 18)
    maybeToTemp tgt
  | .uset v i y =>
    let #[tgt] ← useVar v | throwError "Unexpected target size for uset"
    let #[src] ← useVar y | throwError "Unexpected input size for projection"
    let tgt' := maybeTarget tgt
    let src' := maybeTarget src (inner := true)
    emit (.uset (← as tgt' 8) (← as src' 8) (← as i 8))
    maybeToTemp src (inner := true)
    maybeToTemp tgt
  | .sset v i off y ty =>
    let #[tgt] ← useVar v | throwError "Unexpected target size for uset"
    let #[src] ← useVar y | throwError "Unexpected input size for projection"
    let tgt' := maybeTarget tgt
    let src' := maybeTarget src (inner := true)
    match ty with
    | uint8 => emit (.sset8 (← as tgt' 8) (← as src' 8))
    | uint16 => emit (.sset16 (← as tgt' 8) (← as src' 8))
    | uint32 => emit (.sset32 (← as tgt' 8) (← as src' 8))
    | uint64 => emit (.sset64 (← as tgt' 8) (← as src' 8))
    | float32 => emit (.sset32 (← as tgt' 8) (← as src' 8))
    | float => emit (.sset64 (← as tgt' 8) (← as src' 8))
    | _ => unreachable!
    emit (.computeScalar (← as i 13) (← as off 13))
    maybeToTemp src (inner := true)
    maybeToTemp tgt
  | .inc v n _c _p =>
    let #[tgt] ← useVar v | throwError "Unexpected target size for inc"
    let tgt' := maybeTarget tgt
    let mut n := n
    while n >= 256 do
      emit (.inc (← as tgt' 8) 255)
      n := n - 255
    emit (.inc (← as tgt' 8) (← as n 8))
    maybeToTemp tgt
  | .dec v n _c _p _o? =>
    let #[tgt] ← useVar v | throwError "Unexpected target size for dec"
    let tgt' := maybeTarget tgt
    let mut n := n
    while n >= 256 do
      emit (.dec (← as tgt' 8) 255)
      n := n - 255
    emit (.dec (← as tgt' 8) (← as n 8))
    maybeToTemp tgt
  | .del v =>
    let #[tgt] ← useVar v | throwError "Unexpected target size for del"
    let tgt' := maybeTarget tgt
    emit (.del (← as tgt' 8))
    maybeToTemp tgt
  | .setTag v i =>
    let #[tgt] ← useVar v | throwError "Unexpected target size for setTag"
    let tgt' := maybeTarget tgt
    emit (.setTag (← as tgt' 8) (← as i 10))
    maybeToTemp tgt
  | .jp _ => unreachable!

def processBacklog (backlog : Array (CodeDecl .impure)) : M Unit := do
  let mut i := backlog.size
  while i > 0 do
    i := i - 1
    let decl := backlog[i]!
    processInstruction decl

def parallelArgAssignment (args : Array (Arg .impure)) (paramInfo : Array (Array Nat)) :
    M Unit := do
  let mut lhss := #[]
  let mut rhss := #[]
  for arg in args, pinfo in paramInfo do
    if pinfo.isEmpty then
      -- void parameters and unused parameters
      continue
    match arg with
    | .erased =>
      assert! pinfo.size = 1
      -- since we're processing in reverse, there's no risk rewriting anything
      -- by performing the assignment here
      emitErasedTo pinfo[0]!
    | .fvar var =>
      let allocs ← useVarJmp var pinfo
      for lhs in pinfo, rhs in allocs do
        lhss := lhss.push lhs
        rhss := rhss.push rhs
  parallelAssignment lhss rhss

def parallelArgAssignmentRetCall (args : Array (Arg .impure)) (params : Array (Param .impure)) :
    M Unit := do
  let mut lhss := #[]
  let mut rhss := #[]
  let mut pos := 0
  for arg in args, param in params do
    let sz := computeCallsideSpace param.type
    if sz = 0 then
      -- void parameters
      continue
    if param.type.isErased then
      emitErasedTo pos
      pos := pos + sz
      continue
    match arg with
    | .erased =>
      assert! sz = 1
      emitErasedTo pos
    | .fvar var =>
      let pinfo := Array.range' pos sz
      let allocs ← useVarJmp var pinfo
      for lhs in pinfo, rhs in allocs do
        lhss := lhss.push lhs
        rhss := rhss.push rhs
    pos := pos + sz
  -- `parallelAssignment` wishes to use the argument slots as temporaries
  -- so we need to make sure that all the arguments are on the regular stack
  modify fun state => { state with regAlloc.max := state.regAlloc.max.max pos }
  parallelAssignment lhss rhss

partial def visit (code : Code .impure) (backlog : Array (CodeDecl .impure)) : M Unit :=
    withTraceNode `Compiler.bytecode (fun _ => return m!"{← ppCode code}") do
  match code with
  | .jp decl k => visit k backlog
  | .jmp tgt args =>
    unless (← get).joinPoints.contains tgt do
      let decl : FunDecl .impure ← getFunDecl tgt
      visit decl.value #[]
      let bb ← endBlock
      let mut paramInfo := #[]
      for param in decl.params do
        if let some res := (← get).regAlloc.map[param.fvarId]? then
          paramInfo := paramInfo.push res
          declareVar param.fvarId
        else
          paramInfo := paramInfo.push #[]
      modify fun state => { state with joinPoints := state.joinPoints.insert tgt { bb, paramInfo } }
    let jpInfo := (← get).joinPoints[tgt]!
    emitJump jpInfo.bb
    parallelArgAssignment args jpInfo.paramInfo
    processBacklog backlog
  | .cases cases =>
    if cases.alts.isEmpty then
      -- idk if this reachable honestly
      return ← visit (.unreach cases.resultType) backlog
    if let #[alt] := cases.alts then
      return ← visit alt.getCode backlog
    let mut bbs : Array (Option Nat) := #[]
    let mut default : Option (Code .impure) := none
    for case in cases.alts.reverse do
      match case with
      | .ctorAlt info code =>
        visit code #[]
        let bb ← endBlock
        let idx := info.cidx
        while bbs.size ≤ idx do
          bbs := bbs.push none
        bbs := bbs.set! idx (some bb)
      | .default code =>
        default := some code
    if let some d := default then
      visit d #[]
      discard <| endBlock
    -- we had at least one endBlock before
    let lastBb := (← get).revBasicBlocks.size - 1
    -- create a jump table
    for bb in bbs.reverse do
      emitJump (bb.getD lastBb)
    let discr ← useVar cases.discr
    let type ← getType cases.discr
    let discr' := maybeTarget discr[0]!
    if type.isScalar then
      emit (.jumpTable (← as discr' 8) (← as bbs.size 10))
    else
      -- todo: unboxed types when we have them
      emitComplex (.referToTempSpot (.jumpTable 0 (← as bbs.size 10)) 10)
      emitComplex (.referToTempSpot (.loadTag 0 (← as discr' 8)) 8)
    maybeToTemp discr[0]!
    processBacklog backlog
  | .unreach _ =>
    emit .unreachable
    processBacklog backlog
  | .return var =>
    let pos ← useVar var
    if let some bb := (← get).returnBb then
      emitJump bb
      if pos.size = 1 then
        if pos[0]! != 0 then
          emit (.move 0 (← as (adjustStackSpace pos[0]!) 13))
      else if pos.isEmpty then
        pure ()
      else
        unreachable! -- todo for unboxing
    else
      if pos.size = 1 then
        emit (.ret (← as (adjustStackSpace pos[0]!) 16))
      else if pos.isEmpty then
        emit (.ret 0)
      else
        unreachable! -- todo for unboxing
    processBacklog backlog
  | .let decl k =>
    let cont (_ : Unit) := visit k (backlog.push (.let decl))
    -- special case: tail call
    let .return var := k | cont ()
    unless decl.fvarId == var do return ← cont ()
    let .fap nm args := decl.value | cont ()
    if (← get).returnBb.isSome then return ← cont ()
    if args.isEmpty then return ← cont ()
    let mut params := (← read).params
    if (← read).currDecl == nm then
      emitComplex .jumpToBeginning
    else
      let sym ← recordSymbol nm
      emit (.retcall (← as sym 16))
      let some decl ← getImpureSignature? nm | throwError "Missing impure signature for `{nm}`"
      params := decl.params
    parallelArgAssignmentRetCall args params
    processBacklog backlog
  | .oset v i y k => visit k (backlog.push (.oset v i y))
  | .uset v i y k => visit k (backlog.push (.uset v i y))
  | .sset v i off y ty k => visit k (backlog.push (.sset v i off y ty))
  | .inc v n c p k => visit k (backlog.push (.inc v n c p))
  | .dec v n c p o? k => visit k (backlog.push (.dec v n c p o?))
  | .del v k => visit k (backlog.push (.del v))
  | .setTag v i k => visit k (backlog.push (.setTag v i))

partial def setupParams (retType : Expr) : M Unit := do
  let mut pos := 0
  for p in (← read).params do
    let skip := computeCallsideSpace p.type
    let sz := computeRegSpace p.type
    let mut as := #[]
    for i in 0...sz do
      modify fun state => { state with regAlloc := state.regAlloc.allocAt (pos + i) }
      as := as.push (pos + i)
    modify fun state => { state with regAlloc.map := state.regAlloc.map.insert p.fvarId as }
    pos := pos + skip
  if (← read).params.isEmpty then
    emit (.ret 0)
    match retType with
    | uint8 | uint16 => emit (.unboxSmall 0 0)
    | uint32 => emit (.unboxUInt32 0 0)
    | uint64 => emit (.unboxUInt64 0 0)
    | usize => emit (.unboxUSize 0 0)
    | float32 => emit (.unboxFloat32 0 0)
    | float => emit (.unboxFloat 0 0)
    | tobject | object | tagged | erased | void => pure ()
    | _ => unreachable!
    discard <| endBlock
    emit (.storeCache 0)
    match retType with
    | uint8 | uint16 => emit (.boxSmall 0 0)
    | uint32 => emit (.boxUInt32 0 0)
    | uint64 => emit (.boxUInt64 0 0)
    | usize => emit (.boxUSize 0 0)
    | float32 => emit (.boxFloat32 0 0)
    | float => emit (.boxFloat 0 0)
    | tobject | object | tagged | erased | void => pure ()
    | _ => unreachable!
    let returnBb ← endBlock
    modify fun state => { state with returnBb }

structure BasicBlockReference where
  pos : Nat
  targetBB : Nat
  offset : Nat
  bitlen : Nat

def assemble : M BytecodeDecl := do
  discard <| endBlock
  let name := (← read).currDecl
  let arity := (← read).params.size
  let mut flatCode : Array Instruction := #[]
  let mut refs : Array BasicBlockReference := #[]
  let mut bbLocs : Array Nat := #[]
  let revBBs := (← get).revBasicBlocks
  if arity = 0 then
    -- we need to add a jump to the last basic block for constants
    refs := refs.push {
      pos := flatCode.size, targetBB := revBBs.size - 1,
      offset := 0, bitlen := 26
    }
    flatCode := flatCode.push (.skipIfCached 0)
  let mut i := (← get).revBasicBlocks.size
  let regCount := (← get).regAlloc.max
  let mut argOffset := regCount + 1
  let mut tempSpace := regCount
  if argOffset >= normalRange then
    argOffset := argOffset + numTemps
    tempSpace := 253
  let mut argSize := 0
  -- iterate through the reversed blocks in reverse in reverse
  while i > 0 do
    i := i - 1
    bbLocs := bbLocs.push flatCode.size
    let revBB := revBBs[i]!
    let mut j := revBB.size
    while j > 0 do
      j := j - 1
      let instr := revBB[j]!
      unless instr.value >>> 26 = 63 do
        flatCode := flatCode.push instr
        continue
      let complexInstr := (← get).complex[instr.value.toNat &&& (1 <<< 26 - 1)]!
      match complexInstr with
      | .move tgt src argTgt argSrc =>
        let mut tgt := tgt; let mut src := src
        if argTgt then
          argSize := max argSize (tgt + 1)
          tgt := tgt + argOffset
        else if tgt >= normalRange then
          tgt := tgt + numTemps
        if argSrc then
          argSize := max argSize (src + 1)
          src := src + argOffset
        else if src >= normalRange then
          src := src + numTemps
        flatCode := flatCode.push (.move (← as tgt 13) (← as src 13))
      | .eraseArg tgt =>
        argSize := max argSize (tgt + 1)
        let tgt := tgt + argOffset
        if tgt >= normalRange then
          flatCode := flatCode.push (.uconst (← as tempSpace 8) 1)
          flatCode := flatCode.push (.move (← as tgt 13) (← as tempSpace 13))
        else
          flatCode := flatCode.push (.uconst (← as tgt 8) 1)
      | .referToTempSpot instr bitoff =>
        flatCode := flatCode.push ⟨instr.value ||| (← as tempSpace 8) <<< bitoff⟩
      | .jumpToBB bbRev =>
        refs := refs.push {
          pos := flatCode.size, targetBB := revBBs.size - 1 - bbRev,
          offset := 0x200_0000, bitlen := 26
        }
        flatCode := flatCode.push .nojump
      | .jumpToBeginning =>
        refs := refs.push {
          pos := flatCode.size, targetBB := 0,
          offset := 0x200_0000, bitlen := 26
        }
        flatCode := flatCode.push .nojump
  for ref in refs do
    let off : Int := bbLocs[ref.targetBB]! - (ref.pos + 1)
    let value := off + ref.offset
    if value < 0 then
      throwError "Backreference too large: {off} for offset {ref.offset}"
    if value >= 1 <<< ref.bitlen then
      throwError "Forward reference too large: {off} for offset {ref.offset}"
    flatCode := flatCode.modify ref.pos fun ⟨instr⟩ => ⟨instr ||| value.toNat.toUInt32⟩
  return {
    name, arity,
    symbols := (← get).symbols
    code := Bytecode.assemble flatCode
    stackReserved := argOffset + argSize
    stackSpace := argOffset
    constants := (← get).constants
    cache := .mkEmpty ..
  }

end ToBytecode

open ToBytecode
def compileBytecodeDecl (d : Decl .impure) : CompilerM BytecodeDecl := do
  let d ← d.internalize
  let .code code := d.value |
    throwError "Unexpected extern decl for Bytecode.compileDecl"
  let act : M BytecodeDecl := do
    setupParams d.type
    visit code #[]
    ToBytecode.assemble
  act.run { currDecl := d.name, params := d.params } |>.run' {}

private partial def setClosureMeta (name : Name) : CompilerM Unit := do
  let some decl := findBytecodeDecl (← getEnv) name | return
  for ref in decl.symbols do
    if isDeclMeta (← getEnv) ref then
      continue
    unless impureSigExt.getState (← getEnv) |>.contains ref do
      -- not declared in the current module
      continue
    trace[compiler.ir.inferMeta] m!"Marking {ref} as meta because it is in `meta` closure"
    modifyEnv (setDeclMeta · ref)
    setClosureMeta ref

private partial def inferMeta (decls : Array (Decl .impure)) : CompilerM Unit := do
  if !(← getEnv).header.isModule then
    return
  for decl in decls do
    if isMarkedMeta (← getEnv) decl.name then
      trace[compiler.ir.inferMeta] m!"Marking {decl.name} as meta because it is tagged with `meta`"
      modifyEnv (setDeclMeta · decl.name)
      unless impureSigExt.getState (← getEnv) |>.contains decl.name do
        -- not declared in the current module
        continue
      setClosureMeta decl.name

def compile (decls : Array (Decl .impure)) : CompilerM Unit := do
  let mut bytecodeDecls : Array BytecodeDecl := #[]
  for d in decls do
    match d.value with
    | .code _ =>
      let decl ← compileBytecodeDecl d
      trace[Compiler.bytecode.result] m!"{disassemble decl}"
      bytecodeDecls := bytecodeDecls.push decl
    | .extern data =>
      if data.entries.isEmpty then
        let decl : BytecodeDecl := {
          name := d.name
          code := assemble #[.skipIfCached 1, .unreachable, .ret 0]
          stackReserved := 1
          stackSpace := 0
          symbols := #[]
          arity := 0
          constants := #[]
          cache := .mkEmpty ..
        }
        bytecodeDecls := bytecodeDecls.push decl
  bytecodeDecls ← updateSorryDep bytecodeDecls
  bytecodeDecls.forM fun decl =>
    modifyEnv (declMapExt.addEntry · decl)
  inferMeta decls

builtin_initialize
  registerTraceClass `Compiler.bytecode
  registerTraceClass `Compiler.bytecode.result (inherited := true)
  registerTraceClass `compiler.ir.inferMeta

end Lean.Compiler.Bytecode
