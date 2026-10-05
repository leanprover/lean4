/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Lean.Compiler.LCNF.Basic
public import Lean.Compiler.Bytecode.Instruction
import Lean.Compiler.LCNF.PrettyPrinter
import Init.While

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
  fixUps : Array FixUp := #[]
  regAlloc : RegAlloc := {}
  returnBb : Option Nat := none -- only for constants

structure Context where
  currDecl : Name
  params : Array (Param .impure)

abbrev M := ReaderT Context <| StateRefT State CompilerM

def emit (instr : Instruction) : M Unit := do
  modify fun state => { state with revCurrBlock := state.revCurrBlock.push instr }

@[inline]
def addFixup (f : (whereBbRev whereIndexRev : Nat) → FixUp) : M Unit := do
  let currBbRev := (← get).revBasicBlocks.size
  let currIndexRev := (← get).revCurrBlock.size
  modify fun state => { state with fixUps := state.fixUps.push (f currBbRev currIndexRev) }

def emitJump (targetBb : Nat) : M Unit := do
  if (← get).revCurrBlock.isEmpty ∧ targetBb + 1 = (← get).revBasicBlocks.size then
    return
  emit .nojump
  addFixup (.basicBlockRef · · targetBb 26)

def emitMove (tgt src : Nat) : M Unit := do
  emit (.move tgt.toUInt32 src.toUInt32)

def emitMoveToTemp (tgt src : Nat) : M Unit := do
  emit (.move tgt.toUInt32 src.toUInt32)
  addFixup (.argRel · · 13 13)

def emitMoveFromTemp (tgt src : Nat) : M Unit := do
  emit (.move tgt.toUInt32 src.toUInt32)
  addFixup (.argRel · · 0 13)

def emitMoveWithinTemp (tgt src : Nat) : M Unit := do
  emit (.move tgt.toUInt32 src.toUInt32)
  addFixup (.argRel · · 0 13)
  addFixup (.argRel · · 13 13)

def emitErasedTo (tgt : Nat) : M Unit := do
  emit (.uconst tgt.toUInt32 1)

def emitErasedToTemp (tgt : Nat) : M Unit := do
  emit (.uconst tgt.toUInt32 1)
  addFixup (.argRel · · 18 8)

def endBlock : M Nat := do
  let bb := (← get).revBasicBlocks.size
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
      emitMoveFromTemp lhs tmpIdx
    else
      emitMove lhs rhs
  for (rhs, tmpIdx) in tempVars do
    emitMoveToTemp tmpIdx rhs

def prepareCallArgs (args : Array (Arg .impure)) (params : Array (Param .impure)) : M Unit := do
  let mut pos := 0
  let mut sizes := #[]
  for param in params do
    -- erased specifically has size one
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
        emitErasedToTemp pos
    | .fvar var =>
      let x ← useVar var
      if size = 0 then
        emitErasedToTemp pos
      else
        assert! x.size = size
        for j in 0...size do
          emitMoveToTemp (pos + j) x[j]!

-- equivalent to `prepareCallArgs args (Array.replicate { type := tobject, .. } args.size)`
def prepareCallArgsSimple (args : Array (Arg .impure)) : M Unit := do
  let mut i := args.size
  while i > 0 do
    i := i - 1
    let arg := args[i]!
    match arg with
    | .erased => emitErasedToTemp i
    | .fvar var =>
      let x ← useVar var
      if x.isEmpty then
        emitErasedToTemp i
      else
        assert! x.size = 1
        emitMoveToTemp i x[0]!

def setCtorArgs (tgt : Nat) (args : Array (Arg .impure)) : M Unit := do
  let mut i := args.size
  let mut hadErased := false
  while i > 0 do
    i := i - 1
    let arg := args[i]!
    match arg with
    | .fvar var =>
      let #[v] ← useVar var | throwError "Unexpected size for constructor argument"
      emit (.set tgt.toUInt32 v.toUInt32 i.toUInt32)
    | .erased =>
      emit (.set tgt.toUInt32 0 i.toUInt32)
      addFixup (.argRel · · 8 8)
      hadErased := true
  if hadErased then
    emitErasedToTemp 0

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

def processLetDecl (decl : LetDecl .impure) : M Unit := do
  let vars? := (← get).regAlloc.map[decl.fvarId]?
  match decl.value with
  | .lit value =>
    let some #[var] := vars? | return -- return if unused
    match value with
    | .uint8 val => emit (.uconst var.toUInt32 val.toUInt32)
    | .uint16 val => emit (.uconst var.toUInt32 val.toUInt32)
    | .uint32 val =>
      if val.toNat ≤ maxUConst then
        emit (.uconst var.toUInt32 val)
      else
        let constId ← unsafe addConstant value val
        emit (.unboxUInt32 var.toUInt32 var.toUInt32)
        emit (.declConst var.toUInt32 constId.toUInt32)
    | .uint64 val =>
      if val.toNat ≤ maxUConst then
        emit (.uconst var.toUInt32 val.toUInt32)
      else
        let constId ← unsafe addConstant value val
        emit (.unboxUInt64 var.toUInt32 var.toUInt32)
        emit (.declConst var.toUInt32 constId.toUInt32)
    | .usize val =>
      if val.toNat ≤ maxUConst then
        emit (.uconst var.toUInt32 val.toUInt32)
      else
        let constId ← unsafe addConstant value val
        emit (.unboxUSize var.toUInt32 var.toUInt32)
        emit (.declConst var.toUInt32 constId.toUInt32)
    | .nat val =>
      if val ≤ maxNConst then
        emit (.nconst var.toUInt32 val.toUInt32)
      else
        let constId ← unsafe addConstant value val
        unless unsafe isScalarObj val do
          emit (.inc var.toUInt32 1)
        emit (.declConst var.toUInt32 constId.toUInt32)
    | .str s =>
      let constId ← unsafe addConstant value s
      emit (.inc var.toUInt32 1)
      emit (.declConst var.toUInt32 constId.toUInt32)
  | .erased =>
    let some #[var] := vars? | return -- return if unused
    emitErasedTo var
  | .fvar fvarId as =>
    let #[fn] ← useVar fvarId | throwError "Unexpected size for function"
    if let some #[var] := vars? then
      emitMoveFromTemp var 0
      declareVar decl.fvarId
    emit (.app fn.toUInt32 as.size.toUInt32)
    prepareCallArgsSimple as
  | .ctor info args =>
    if info.isScalar then
      if let some #[tgt] := vars? then
        emit (.nconst tgt.toUInt32 info.cidx.toUInt32)
      return
    let some #[tgt] := vars? | throwError "Result of constructor leaked"
    setCtorArgs tgt args
    emit (.allocCtor tgt.toUInt32 info.cidx.toUInt32 info.size.toUInt32)
    declareVar decl.fvarId
  | .fap fn as =>
    let some sig ← getImpureSignature? fn | throwError "Missing impure signature for `{fn}`"
    if let some vars := vars? then
      let mut i := vars.size
      while i > 0 do
        i := i - 1
        emitMoveFromTemp vars[i]! i
      declareVar decl.fvarId
    if as.isEmpty then
      emit (.loadConst (← recordSymbol fn).toUInt32)
    else
      emit (.call (← recordSymbol fn).toUInt32)
      prepareCallArgs as sig.params
  | .pap fn as =>
    if let some #[var] := vars? then
      emitMoveFromTemp var 0
      declareVar decl.fvarId
    emit (.pap (← recordSymbol fn).toUInt32 as.size.toUInt32)
    prepareCallArgsSimple as
  | .oproj i var =>
    let some #[tgt] := vars? | return -- return if unused
    let #[src] ← useVar var | throwError "Unexpected input size for projection"
    emit (.proj tgt.toUInt32 src.toUInt32 i.toUInt32)
  | .uproj i var =>
    let some #[tgt] := vars? | return -- return if unused
    let #[src] ← useVar var | throwError "Unexpected input size for projection"
    emit (.uproj tgt.toUInt32 src.toUInt32 i.toUInt32)
  | .sproj i offset var =>
    let some #[tgt] := vars? | return -- return if unused
    let #[src] ← useVar var | throwError "Unexpected input size for projection"
    match decl.type with
    | uint8 => emit (.sproj8 tgt.toUInt32 src.toUInt32)
    | uint16 => emit (.sproj16 tgt.toUInt32 src.toUInt32)
    | uint32 => emit (.sproj32 tgt.toUInt32 src.toUInt32)
    | uint64 => emit (.sproj64 tgt.toUInt32 src.toUInt32)
    | float32 => emit (.sproj32 tgt.toUInt32 src.toUInt32)
    | float => emit (.sproj64 tgt.toUInt32 src.toUInt32)
    | _ => unreachable!
    emit (.computeScalar i.toUInt32 offset.toUInt32)
  | .reset n var =>
    let some #[tgt] := vars? | throwError "Result of reset leaked"
    let #[src] ← useVar var | throwError "Unexpected input size for reset"
    emit (.reset n.toUInt32 tgt.toUInt32 src.toUInt32)
  | .reuse var i _updateHeader args =>
    let some #[tgt] := vars? | throwError "Result of reuse leaked"
    let #[src] ← useVar var | throwError "Unexpected input size for reuse"
    setCtorArgs tgt args
    emit (.reuse tgt.toUInt32 i.cidx.toUInt32 i.size.toUInt32)
    unless src = tgt do
      emitMove tgt src
  | .box ty var =>
    let some #[tgt] := vars? | throwError "Result of box leaked"
    let #[src] ← useVar var | throwError "Unexpected input size for boxing function"
    match ty with
    | uint8 | uint16 => emit (.boxSmall tgt.toUInt32 src.toUInt32)
    | uint32 => emit (.boxUInt32 tgt.toUInt32 src.toUInt32)
    | uint64 => emit (.boxUInt64 tgt.toUInt32 src.toUInt32)
    | usize => emit (.boxUSize tgt.toUInt32 src.toUInt32)
    | float32 => emit (.boxFloat32 tgt.toUInt32 src.toUInt32)
    | float => emit (.boxFloat tgt.toUInt32 src.toUInt32)
    | _ => unreachable!
  | .unbox var =>
    let some #[tgt] := vars? | return -- return if unused
    let #[src] ← useVar var | throwError "Unexpected input size for boxing function"
    match decl.type with
    | uint8 | uint16 => emit (.unboxSmall tgt.toUInt32 src.toUInt32)
    | uint32 => emit (.unboxUInt32 tgt.toUInt32 src.toUInt32)
    | uint64 => emit (.unboxUInt64 tgt.toUInt32 src.toUInt32)
    | usize => emit (.unboxUSize tgt.toUInt32 src.toUInt32)
    | float32 => emit (.unboxFloat32 tgt.toUInt32 src.toUInt32)
    | float => emit (.unboxFloat tgt.toUInt32 src.toUInt32)
    | _ => unreachable!
  | .isShared fvarId =>
    let some #[tgt] := vars? | return -- return if unused
    let #[src] ← useVar fvarId | throwError "Unexpected input size for boxing function"
    emit (.isShared tgt.toUInt32 src.toUInt32)

def processInstruction (decl : CodeDecl .impure) : M Unit := do
  match decl with
  | .let ldecl =>
    processLetDecl ldecl
    declareVar ldecl.fvarId -- if not already done above
  | .oset v i y =>
    let #[tgt] ← useVar v | throwError "Unexpected target size for set"
    match y with
    | .fvar var =>
      let #[src] ← useVar var | throwError "Unexpected input size for projection"
      emit (.set tgt.toUInt32 src.toUInt32 i.toUInt32)
    | .erased =>
      emit (.set tgt.toUInt32 0 i.toUInt32)
      addFixup (.argRel · · 8 8)
      emitErasedToTemp 0
  | .uset v i y =>
    let #[tgt] ← useVar v | throwError "Unexpected target size for uset"
    let #[src] ← useVar y | throwError "Unexpected input size for projection"
    emit (.set tgt.toUInt32 src.toUInt32 i.toUInt32)
  | .sset v i off y ty =>
    let #[tgt] ← useVar v | throwError "Unexpected target size for uset"
    let #[src] ← useVar y | throwError "Unexpected input size for projection"
    match ty with
    | uint8 => emit (.sset8 tgt.toUInt32 src.toUInt32)
    | uint16 => emit (.sset16 tgt.toUInt32 src.toUInt32)
    | uint32 => emit (.sset32 tgt.toUInt32 src.toUInt32)
    | uint64 => emit (.sset64 tgt.toUInt32 src.toUInt32)
    | float32 => emit (.sset32 tgt.toUInt32 src.toUInt32)
    | float => emit (.sset64 tgt.toUInt32 src.toUInt32)
    | _ => unreachable!
    emit (.computeScalar i.toUInt32 off.toUInt32)
  | .inc v n _c _p =>
    let #[tgt] ← useVar v | throwError "Unexpected target size for inc"
    emit (.inc tgt.toUInt32 n.toUInt32)
  | .dec v n _c _p _o? =>
    let #[tgt] ← useVar v | throwError "Unexpected target size for dec"
    emit (.dec tgt.toUInt32 n.toUInt32)
  | .del v =>
    let #[tgt] ← useVar v | throwError "Unexpected target size for del"
    emit (.del tgt.toUInt32)
  | .setTag v i =>
    let #[tgt] ← useVar v | throwError "Unexpected target size for setTag"
    emit (.setTag tgt.toUInt32 i.toUInt32)
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
    if type.isScalar then
      emit (.jumpTable discr[0]!.toUInt32 bbs.size.toUInt32)
    else
      -- todo: unboxed types when we have them
      emit (.jumpTable 0 bbs.size.toUInt32)
      addFixup (.argRel · · 10 16)
      emit (.loadTag 0 discr[0]!.toUInt32)
      addFixup (.argRel · · 8 18)
    processBacklog backlog
  | .unreach _ =>
    processBacklog backlog
  | .return var =>
    let pos ← useVar var
    if let some bb := (← get).returnBb then
      emitJump bb
      if pos.size = 1 then
        if pos[0]!.toUInt32 != 0 then
          emit (.move 0 pos[0]!.toUInt32)
      else if pos.isEmpty then
        pure ()
      else
        unreachable! -- todo for unboxing
    else
      if pos.size = 1 then
        emit (.ret pos[0]!.toUInt32)
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
      emit .nojump
      addFixup (.beginRef · · 26)
    else
      let sym ← recordSymbol nm
      emit (.retcall sym.toUInt32)
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

def State.assemble (s : State) (name : Name) (arity : Nat) : BytecodeDecl := Id.run do
  let mut bbLocsRev : Array Nat := #[]
  let mut bbPos := 0
  for bb in s.revBasicBlocks do
    bbLocsRev := bbLocsRev.push bbPos
    bbPos := bbPos + bb.size
  bbLocsRev := bbLocsRev.push bbPos
  let mut flatCodeRev := s.revBasicBlocks.flatten
  let mut tempSize := 0
  for fix in s.fixUps do
    match fix with
    | .basicBlockRef whereBbRev whereIndexRev targetBb bitlen =>
      -- because we are just looking at reversed code,
      -- we can figure out the reversed position easily
      -- off-by-one because we register fixups after emitting instructions
      let whereRev := bbLocsRev[whereBbRev]! + whereIndexRev - 1
      -- we want the beginning of the basic block; `bbLocsRev` points to the beginning
      let targetRev := bbLocsRev[targetBb + 1]! - 1
      -- wrong way around because reversed,
      -- off-by-one because the interpreter advances the pointer before running instructions
      let diff : Int := whereRev - 1 - targetRev
      let val := diff + 1 <<< (bitlen - 1)
      flatCodeRev := flatCodeRev.modify whereRev fun instr => ⟨instr.value ||| val.toNat.toUInt32⟩
    | .beginRef whereBbRev whereIndexRev bitlen =>
      -- see above
      let whereRev := bbLocsRev[whereBbRev]! + whereIndexRev - 1
      -- point to the beginning = point to reversed end
      let targetRev := bbPos - 1
      let diff : Int := whereRev - 1 - targetRev
      let val := diff + 1 <<< (bitlen - 1)
      flatCodeRev := flatCodeRev.modify whereRev fun instr => ⟨instr.value ||| val.toNat.toUInt32⟩
    | .argRel whereBbRev whereIndexRev bitoff bitlen =>
      -- see above
      let whereRev := bbLocsRev[whereBbRev]! + whereIndexRev - 1
      let origValue := flatCodeRev[whereRev]!.value.toNat >>> bitoff &&& (1 <<< bitlen - 1)
      tempSize := max tempSize (origValue + 1)
      flatCodeRev := flatCodeRev.modify whereRev fun instr =>
        ⟨instr.value + (s.regAlloc.max.toUInt32 <<< bitoff.toUInt32)⟩
  if arity = 0 then
    -- we need to add a jump to the last basic block
    let jmpAmount := bbPos - bbLocsRev[1]!
    flatCodeRev := flatCodeRev.push (.skipIfCached jmpAmount.toUInt32)
  let flatCode := flatCodeRev.reverse
  return {
    name, arity,
    symbols := s.symbols
    code := Bytecode.assemble flatCode
    stackReserved := s.regAlloc.max + tempSize
    stackSpace := s.regAlloc.max
    constants := s.constants
  }

end ToBytecode

open ToBytecode
def compileBytecodeDecl (d : Decl .impure) : CompilerM BytecodeDecl := do
  let d ← d.internalize
  let .code code := d.value |
    throwError "Unexpected extern decl for Bytecode.compileDecl"
  let act : M Unit := do
    setupParams d.type
    visit code #[]
    discard <| endBlock
  let ((), state) ← act.run { currDecl := d.name, params := d.params } |>.run {}
  return state.assemble d.name d.params.size

def compile (d : Decl .impure) : CompilerM Unit := do
  unless d.value matches .code _ do
    return
  let decl ← compileBytecodeDecl d
  modifyEnv (declMapExt.addEntry · decl)
  trace[Compiler.bytecode.result] m!"{disassemble decl}"

builtin_initialize
  registerTraceClass `Compiler.bytecode
  registerTraceClass `Compiler.bytecode.result (inherited := true)

end Lean.Compiler.Bytecode
