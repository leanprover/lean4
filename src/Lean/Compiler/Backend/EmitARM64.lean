/-
Copyright (c) 2025 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Assistant
-/
module

prelude
public import Lean.Compiler.Backend.ARM64
public import Lean.Compiler.Backend.InstrSelect
public import Lean.Compiler.IR.Basic
public import Lean.Compiler.IR.CompilerM
public import Lean.Compiler.ExportAttr
public import Lean.Compiler.ModPkgExt
public import Lean.Compiler.NameMangling
public import Lean.Compiler.ClosedTermCache
public import Lean.Compiler.InitAttr
public import Lean.Runtime

public section

namespace Lean.Compiler.Backend
namespace EmitARM64

open Lean.Compiler.Backend.ARM64
open Lean.Compiler.Backend.InstrSelect

/-- Basic prefix check on character lists. -/
private def startsWithList : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | c1 :: rest1, c2 :: rest2 => c1 = c2 && startsWithList rest1 rest2

/-- Split a string on a separator character into a list of strings -/
private def splitOnChar (s : String) (sep : Char) : List String :=
  let rec go (chars : List Char) (acc : List Char) (result : List String) : List String :=
    match chars with
    | [] => (result ++ [String.ofList acc.reverse]).reverse
    | c :: rest =>
      if c == sep then
        go rest [] (String.ofList acc.reverse :: result)
      else
        go rest (c :: acc) result
  go s.toList [] []

/-- Simple substring check implemented via a sliding window on the underlying
    character lists. -/
def containsSubstr (s sub : String) : Bool :=
  let target := sub.toList
  let rec loop : List Char → Bool
    | [] => target.isEmpty
    | xs@( _ :: tail ) =>
        if startsWithList target xs then true else loop tail
  loop s.toList

/-- Determine whether a declaration corresponds to a closed constant that must be
    materialized in the data section. Besides the standard closed-term cache,
    we also consider the `_boxed_const` helpers generated during extraction. -/
def isClosedConstName (env : Environment) (n : Name) : Bool :=
  isClosedTermName env n || containsSubstr n.mangle "___boxed__const__"

/-- Emit state for tracking output -/
structure EmitState where
  output : String
  deriving Inhabited

abbrev EmitM := StateM EmitState

/-- Mangle Lean function name to match C backend convention -/
def mangleName (name : Name) : String :=
  -- Use Lean's built-in name mangling, which adds "l_" prefix and mangles components
  -- Then add underscore prefix for macOS symbol compatibility
  "_" ++ name.mangle

/-- Mangle a string function name (for external runtime functions) -/
def mangleStringName (name : String) : String :=
  -- For external C functions (lean_*), just add underscore prefix for macOS
  if name.startsWith "lean_" || name.startsWith "_" then
    if name.startsWith "_" then name else s!"_{name}"
  else
    -- Treat as Lean function name - convert to Name and mangle
    -- This handles cases like "String.append" passed as string
    let parts := splitOnChar name '.'
    let leanName := parts.foldl (fun n s => Name.str n s) Name.anonymous
    mangleName leanName

/-- Ensure a symbol name has the macOS underscore prefix. -/
private def withSymbolPrefix (name : String) : String :=
  if name.startsWith "_" then name else s!"_{name}"

/-- Get the export symbol name for a declaration, if any. -/
private def exportSymbolName? (env : Environment) (name : Name) : Option String :=
  match Lean.getExportNameFor? env name with
  | some (.str .anonymous s) => some (withSymbolPrefix s)
  | some _ => panic! s!"invalid export name '{name}'"
  | none => none

/-- Base symbol stem for a declaration, including any package prefix. -/
private def symbolStem (env : Environment) (name : Name) : String :=
  Lean.getSymbolStem env name

/-- Compute the symbol name for a declaration, respecting @[export]. -/
private def symbolName (env : Environment) (name : Name) : String :=
  match exportSymbolName? env name with
  | some s => s
  | none =>
    if name == `main then "_lean_main"
    else withSymbolPrefix (symbolStem env name)

/-- Emit a string to the output -/
def emit (s : String) : EmitM Unit :=
  modify fun st => { st with output := st.output ++ s }

/-- Emit a line to the output -/
def emitLn (s : String := "") : EmitM Unit := do
  emit s
  emit "\n"


def hexDigit (n : Nat) : Char :=
  match n % 16 with
  | 0  => '0' | 1  => '1' | 2  => '2' | 3  => '3'
  | 4  => '4' | 5  => '5' | 6  => '6' | 7  => '7'
  | 8  => '8' | 9  => '9' | 10 => 'A' | 11 => 'B'
  | 12 => 'C' | 13 => 'D' | 14 => 'E' | _ => 'F'

/-- Escape a string literal so it can be emitted via `.asciz`.
    This processes UTF-8 bytes, not characters, to properly handle multi-byte sequences. -/
def escapeString (s : String) : String :=
  let bytes := s.toUTF8
  let step (acc : String) (b : UInt8) : String :=
    let byte := b.toNat
    match byte with
    | 92  => acc ++ "\\\\"  -- backslash
    | 34  => acc ++ "\\\""  -- quote
    | 10  => acc ++ "\\n"   -- newline
    | 13  => acc ++ "\\r"   -- carriage return
    | 9   => acc ++ "\\t"   -- tab
    | _   =>
      -- Only ASCII printable characters are emitted directly
      if byte >= 32 && byte <= 126 then
        acc.push (Char.ofNat byte)
      else
        -- Non-ASCII bytes are hex-escaped
        let hi := hexDigit (byte / 16)
        let lo := hexDigit (byte % 16)
        acc ++ "\\x" ++ String.ofList [hi, lo]
  bytes.foldl step ""

/-- Emit data for a gathered string literal using .byte directives.
    We use .byte instead of .asciz with \xhh escapes because the macOS assembler
    doesn't correctly parse consecutive hex escapes like "\xCE\xB1" (it treats
    \xB1 as \xB followed by literal '1').

    String literals are just raw C string data - they get converted to Lean string
    objects at runtime via lean_mk_string_unchecked. -/
def emitStringLiteral (lit : StringLiteral) : EmitM Unit := do
  emitLn "  .align 3"
  emitLn s!"{lit.dataLabel}:"
  -- Emit string as individual bytes (raw C string data for lean_mk_string_unchecked)
  let bytes := lit.value.toUTF8.toList
  if bytes.isEmpty then
    emitLn "  .byte 0x00  // empty string (null terminator only)"
  else
    let byteStrs := bytes.map fun b => s!"0x{hexDigit (b.toNat / 16)}{hexDigit (b.toNat % 16)}"
    let bytesLine := ", ".intercalate byteStrs
    emitLn s!"  .byte {bytesLine}, 0x00  // null terminator"

/-- Emit an operand as assembly text -/
def emitOperand (op : Operand) : String :=
  match op with
  | .reg r => toString r
  | .imm n => s!"#{n}"
  | .mem base offset =>
    if offset = 0 then
      s!"[{base}]"
    else
      s!"[{base}, #{offset}]"
  | .label name => name

/-- Check if a physical register is a floating-point register -/
private def isFPReg (r : PhysReg) : Bool := r.isFP

/-- Convert condition code to string -/
private def condToString (c : Cond) : String :=
  match c with
  | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le"
  | .gt => "gt" | .ge => "ge" | .lo => "lo" | .ls => "ls"
  | .hi => "hi" | .hs => "hs"

/-- Render FP register based on precision (s0-s31 for single, d0-d31 for double) -/
private def fpReg (prec : FloatPrec) (r : Reg) : String :=
  match r with
  | .phys p =>
    if p.isFP then
      let idx := p.toNat - 32  -- v0 is 32, so subtract to get 0-31
      match prec with
      | .single => s!"s{idx}"
      | .double => s!"d{idx}"
    else
      toString r
  | _ => toString r

/-- Emit arithmetic instruction -/
private def emitArithInstr (instr : Instr) : EmitM Unit := do
  match instr with
  | .add dst src1 src2 => emitLn s!"  add {dst}, {src1}, {emitOperand src2}"
  | .sub dst src1 src2 => emitLn s!"  sub {dst}, {src1}, {emitOperand src2}"
  | .mul dst src1 src2 => emitLn s!"  mul {dst}, {src1}, {src2}"
  | .sdiv dst src1 src2 => emitLn s!"  sdiv {dst}, {src1}, {src2}"
  | .udiv dst src1 src2 => emitLn s!"  udiv {dst}, {src1}, {src2}"
  | .uxtb dst src => emitLn s!"  uxtb {dst}, {src}"
  | .uxth dst src => emitLn s!"  uxth {dst}, {src}"
  | .and dst src1 src2 => emitLn s!"  and {dst}, {src1}, {emitOperand src2}"
  | .orr dst src1 src2 => emitLn s!"  orr {dst}, {src1}, {emitOperand src2}"
  | .eor dst src1 src2 => emitLn s!"  eor {dst}, {src1}, {emitOperand src2}"
  | .lsl dst src shift => emitLn s!"  lsl {dst}, {src}, {emitOperand shift}"
  | .lsr dst src shift => emitLn s!"  lsr {dst}, {src}, {emitOperand shift}"
  | .asr dst src shift => emitLn s!"  asr {dst}, {src}, {emitOperand shift}"
  | _ => pure ()

/-- Emit move instruction -/
private def emitMoveInstr (instr : Instr) : EmitM Unit := do
  match instr with
  | .mov dst src => emitLn s!"  mov {dst}, {emitOperand src}"
  | .movz dst imm shift => emitLn s!"  movz {dst}, #{imm}, lsl #{shift}"
  | .movk dst imm shift => emitLn s!"  movk {dst}, #{imm}, lsl #{shift}"
  | .adrp dst lbl => emitLn s!"  adrp {dst}, {lbl}"
  | _ => pure ()

/-- Emit load/store instruction -/
private def emitMemInstr (instr : Instr) : EmitM Unit := do
  match instr with
  | .ldr dst src suffix =>
    let dstStr := match dst with
      | .phys r => if isFPReg r then fpReg FloatPrec.double dst else toString dst
      | _ => toString dst
    if suffix.isEmpty then emitLn s!"  ldr {dstStr}, {emitOperand src}"
    else emitLn s!"  ldr {dstStr}, [{emitOperand src}{suffix}]"
  | .ldrw dst src => emitLn s!"  ldr {ARM64.Reg.toGPR32String dst}, {emitOperand src}"
  | .ldrs dst src =>
    let dstStr := match dst with
      | .phys r => if isFPReg r then fpReg FloatPrec.single dst else toString dst
      | _ => toString dst
    emitLn s!"  ldr {dstStr}, {emitOperand src}"
  | .ldrd dst src =>
    let dstStr := match dst with
      | .phys r => if isFPReg r then fpReg FloatPrec.double dst else toString dst
      | _ => toString dst
    emitLn s!"  ldr {dstStr}, {emitOperand src}"
  | .ldrb dst src => emitLn s!"  ldrb {ARM64.Reg.toGPR32String dst}, {emitOperand src}"
  | .ldrh dst src => emitLn s!"  ldrh {ARM64.Reg.toGPR32String dst}, {emitOperand src}"
  | .str src dst =>
    let srcStr := match src with
      | .phys r => if isFPReg r then fpReg FloatPrec.double src else toString src
      | _ => toString src
    emitLn s!"  str {srcStr}, {emitOperand dst}"
  | .strb src dst => emitLn s!"  strb {ARM64.Reg.toGPR32String src}, {emitOperand dst}"
  | .strh src dst => emitLn s!"  strh {ARM64.Reg.toGPR32String src}, {emitOperand dst}"
  | .strw src dst => emitLn s!"  str {ARM64.Reg.toGPR32String src}, {emitOperand dst}"
  | .strs src dst =>
    let srcStr := match src with
      | .phys r => if isFPReg r then fpReg FloatPrec.single src else toString src
      | _ => toString src
    emitLn s!"  str {srcStr}, {emitOperand dst}"
  | .strd src dst =>
    let srcStr := match src with
      | .phys r => if isFPReg r then fpReg FloatPrec.double src else toString src
      | _ => toString src
    emitLn s!"  str {srcStr}, {emitOperand dst}"
  | .ldp dst1 dst2 base offset =>
    if offset = 0 then emitLn s!"  ldp {dst1}, {dst2}, [{base}]"
    else emitLn s!"  ldp {dst1}, {dst2}, [{base}, #{offset}]"
  | .stp src1 src2 base offset =>
    if offset = 0 then emitLn s!"  stp {src1}, {src2}, [{base}]"
    else emitLn s!"  stp {src1}, {src2}, [{base}, #{offset}]"
  | _ => pure ()

/-- Emit comparison/select instruction -/
private def emitCmpInstr (instr : Instr) : EmitM Unit := do
  match instr with
  | .cmp src1 src2 => emitLn s!"  cmp {src1}, {emitOperand src2}"
  | .tst src1 src2 => emitLn s!"  tst {src1}, {emitOperand src2}"
  | .csel dst src1 src2 cond => emitLn s!"  csel {dst}, {src1}, {src2}, {condToString cond}"
  | .cset dst cond => emitLn s!"  cset {dst}, {condToString cond}"
  | _ => pure ()

/-- Emit branch instruction -/
private def emitBranchInstr (instr : Instr) : EmitM Unit := do
  match instr with
  | .branch label => emitLn s!"  b {label}"
  | .bl fn => emitLn s!"  bl {mangleStringName fn}"
  | .br reg => emitLn s!"  br {reg}"
  | .blr reg => emitLn s!"  blr {reg}"
  | .ret => emitLn "  ret"
  | .bCond cond label => emitLn s!"  b.{condToString cond} {label}"
  | _ => pure ()

/-- Emit push/pop instruction -/
private def emitStackInstr (instr : Instr) : EmitM Unit := do
  let stackReg (r : Reg) : String :=
    match r with
    | .phys p => if p.isFP then fpReg FloatPrec.double r else toString r
    | _ => toString r
  match instr with
  | .push regs =>
    let mut i := 0
    while i + 1 < regs.size do
      let r1 := regs[i]!
      let r2 := regs[i+1]!
      emitLn s!"  stp {stackReg r1}, {stackReg r2}, [sp, #-16]!"
      i := i + 2
    if i < regs.size then
      let r := regs[i]!
      emitLn s!"  str {stackReg r}, [sp, #-8]!"
  | .pop regs =>
    let mut i := 0
    while i + 1 < regs.size do
      let r1 := regs[i]!
      let r2 := regs[i+1]!
      emitLn s!"  ldp {stackReg r1}, {stackReg r2}, [sp], #16"
      i := i + 2
    if i < regs.size then
      let r := regs[i]!
      emitLn s!"  ldr {stackReg r}, [sp], #8"
  | _ => pure ()

/-- Emit floating-point instruction -/
private def emitFPInstr (instr : Instr) : EmitM Unit := do
  match instr with
  | .fadd prec dst src1 src2 => emitLn s!"  fadd {fpReg prec dst}, {fpReg prec src1}, {fpReg prec src2}"
  | .fsub prec dst src1 src2 => emitLn s!"  fsub {fpReg prec dst}, {fpReg prec src1}, {fpReg prec src2}"
  | .fmul prec dst src1 src2 => emitLn s!"  fmul {fpReg prec dst}, {fpReg prec src1}, {fpReg prec src2}"
  | .fdiv prec dst src1 src2 => emitLn s!"  fdiv {fpReg prec dst}, {fpReg prec src1}, {fpReg prec src2}"
  | .fneg prec dst src => emitLn s!"  fneg {fpReg prec dst}, {fpReg prec src}"
  | .fcmp prec src1 src2 => emitLn s!"  fcmp {fpReg prec src1}, {fpReg prec src2}"
  | .fmov prec dst src =>
    match dst, src with
    | .phys dstP, .phys srcP =>
      if isFPReg dstP && isFPReg srcP then
        emitLn s!"  fmov {fpReg prec dst}, {fpReg prec src}"
      else if isFPReg dstP && !isFPReg srcP then
        let gpSrc := if prec == .single then ARM64.Reg.toGPR32String src else toString src
        emitLn s!"  fmov {fpReg prec dst}, {gpSrc}"
      else if !isFPReg dstP && isFPReg srcP then
        let gpDst := if prec == .single then ARM64.Reg.toGPR32String dst else toString dst
        emitLn s!"  fmov {gpDst}, {fpReg prec src}"
      else
        panic! s!"fmov between two GP registers: {dst}, {src}"
    | _, _ => panic! s!"fmov with virtual registers at emission time: {dst}, {src}"
  | .scvtf prec dst src => emitLn s!"  scvtf {fpReg prec dst}, {src}"
  | .ucvtf prec dst src => emitLn s!"  ucvtf {fpReg prec dst}, {src}"
  | .fcvtzs prec dst src => emitLn s!"  fcvtzs {dst}, {fpReg prec src}"
  | .fcvtzu prec dst src => emitLn s!"  fcvtzu {dst}, {fpReg prec src}"
  | _ => pure ()

/-- Emit misc instruction -/
private def emitMiscInstr (instr : Instr) : EmitM Unit := do
  match instr with
  | .label name => emitLn s!"{name}:"
  | .comment text => emitLn s!"  // {text}"
  | _ => pure ()

/-- Emit an instruction as assembly text -/
def emitInstr (instr : Instr) : EmitM Unit := do
  -- Try each category of instruction
  emitArithInstr instr
  emitMoveInstr instr
  emitMemInstr instr
  emitCmpInstr instr
  emitBranchInstr instr
  emitStackInstr instr
  emitFPInstr instr
  emitMiscInstr instr

/-- Emit a basic block -/
def emitBasicBlock (bb : BasicBlock) : EmitM Unit := do
  emitLn s!"{bb.label}:"
  for instr in bb.instrs do
    emitInstr instr

/-- Emit a machine function -/
def emitMachineFunction (fn : MachineFunction) (customName? : Option String := none) : EmitM Unit := do
  emitLn ""
  -- macOS requires underscore prefix for C-compatible symbols
  let exportName := match customName? with
    | some name => name
    | none =>
      if fn.name == `main then "_lean_main"  -- Special case: export main as _lean_main
      else mangleName fn.name
  emitLn s!"  .globl {exportName}"
  emitLn s!"  .align 2"
  emitLn s!"{exportName}:"

  for block in fn.blocks do
    for instr in block.instrs do
      emitInstr instr

  if !fn.stringLits.isEmpty then
    emitLn ""
    emitLn "  .data"
    for lit in fn.stringLits do
      emitStringLiteral lit
    emitLn "  .text"

/-- Extract trailing numeric suffix from a name, defaulting to `0` if absent. -/
def trailingNumber (n : Name) : Nat :=
  let s := n.toString
  let digits := (s.toList.reverse.takeWhile Char.isDigit).reverse
  if digits.isEmpty then
    0
  else
    match String.ofList digits |>.toNat? with
    | some v => v
    | none => 0

/-- Emit external runtime function declarations -/
def emitExternals : EmitM Unit := do
  emitLn "  // External runtime functions (macOS requires _ prefix)"
  emitLn "  .extern _lean_alloc_ctor"
  emitLn "  .extern _lean_ctor_set"
  emitLn "  .extern _lean_ctor_get"
  emitLn "  .extern _lean_ctor_get_usize"
  emitLn "  .extern _lean_alloc_closure"
  emitLn "  .extern _lean_closure_set"
  emitLn "  .extern _lean_inc"
  emitLn "  .extern _lean_inc_ref"
  emitLn "  .extern _lean_inc_n"
  emitLn "  .extern _lean_inc_ref_n"
  emitLn "  .extern _lean_dec"
  emitLn "  .extern _lean_dec_ref"
  emitLn "  .extern _lean_mark_persistent"
  emitLn "  .extern _lean_is_shared"
  emitLn "  .extern _lean_internal_panic_unreachable"
  emitLn "  .extern _lean_setup_args"
  emitLn "  .extern _lean_initialize_runtime_module"
  emitLn "  .extern _lean_io_mark_end_initialization"
  emitLn "  .extern _lean_io_result_show_error"
  emitLn "  .extern _lean_init_task_manager"
  emitLn "  .extern _lean_finalize_task_manager"
  emitLn "  .extern _lean_task_spawn"
  emitLn "  .extern _lean_task_get_own"
  emitLn "  .extern _lean_mk_string"
  emitLn "  .extern _lean_mk_string_unchecked"
  for i in [:Lean.closureMaxArgs] do
    let idx := i + 1
    emitLn s!"  .extern _lean_apply_{idx}"
  emitLn "  .extern _lean_apply_m"
  emitLn ""

/-- Emit assembly preamble -/
def emitPreamble : EmitM Unit := do
  emitLn "  .arch armv8-a"
  emitLn "  .file \"lean_output.s\""
  emitExternals
  emitLn "  .text"

/-- Emit .data section with global variable declarations -/
def emitDataSection (env : Environment) (decls : Array IR.Decl) : EmitM Unit := do
  emitLn ""
  emitLn "  .data"
  emitLn "  .align 3"
  -- Emit global flag for initialization
  emitLn "  .globl _G_initialized"
  emitLn "_G_initialized:"
  emitLn "  .byte 0"
  emitLn ""
  -- Emit closed constants and 0-param defs as global pointers (8 bytes each)
  for decl in decls do
    match decl with
    | .fdecl name params retType _ _ =>
      if params.isEmpty then
        let mangledName := symbolName env name
        -- Add alignment before each global constant
        match retType with
        | .uint8 => emitLn "  .align 0  // byte alignment"
        | .uint16 => emitLn "  .align 1  // halfword alignment"
        | .uint32 | .float32 => emitLn "  .align 2  // word alignment"
        | _ => emitLn "  .align 3  // doubleword alignment"
        emitLn s!"  .globl {mangledName}"
        emitLn s!"{mangledName}:"
        -- Emit appropriate storage size based on return type
        match retType with
        | .uint8 => emitLn "  .byte 0  // uint8 initialized at startup"
        | .uint16 => emitLn "  .short 0  // uint16 initialized at startup"
        | .uint32 | .float32 => emitLn "  .long 0  // uint32/float32 initialized at startup"
        | .uint64 | .usize | .float => emitLn "  .quad 0  // uint64/usize/float initialized at startup"
        | _ => emitLn "  .quad 0  // Object initialized at startup"
    | _ => pure ()
  emitLn ""
  emitLn "  .text"

/-- Compile a declaration to ARM64 assembly -/
def emitDecl (env : Environment) (decl : IR.Decl) : String :=
  let machineFunc := InstrSelect.compileDecl env decl
  let initState : EmitState := { output := "" }
  let customName? :=
    match decl with
    | .fdecl name params _ _ _ =>
      if params.isEmpty then
        some ("__init_" ++ symbolStem env name)
      else
        some (symbolName env name)
    | _ => none
  let (_result, finalState) := (emitMachineFunction machineFunc customName?).run initState
  finalState.output

/-- Check if declarations contain a main function -/
def hasMainFn (decls : List IR.Decl) : Bool :=
  decls.any (fun d => d.name == `main)

/-- Emit module initialization function -/
def emitInitFunction (env : Environment) (modName : Name) (decls : Array IR.Decl) : EmitM Unit := do
  let pkg? := env.getModulePackage?
  let initFnName := withSymbolPrefix (Lean.mkModuleInitializationFunctionName modName pkg?)

  emitLn ""
  emitLn "  // Module initialization function"
  -- Declare imported module initializers as extern
  for imp in env.imports do
    let impPkg? :=
      match env.getModuleIdxFor? imp.module with
      | some idx => env.getModulePackageByIdx? idx
      | none => none
    let impInitFn := withSymbolPrefix (Lean.mkModuleInitializationFunctionName imp.module impPkg?)
    emitLn s!"  .extern {impInitFn}"

  emitLn s!"  .globl {initFnName}"
  emitLn "  .align 2"
  emitLn s!"{initFnName}:"
  emitLn "  // Parameters: x0 = builtin (uint8_t), x1 = world"
  emitLn "  stp x29, x30, [sp, #-32]!"
  emitLn "  mov x29, sp"
  emitLn "  stp x19, x20, [sp, #16]"
  emitLn ""

  -- Check if already initialized
  emitLn "  // Check if already initialized"
  emitLn "  adrp x8, _G_initialized@PAGE"
  emitLn "  add x8, x8, _G_initialized@PAGEOFF"
  emitLn "  ldrb w9, [x8]"
  emitLn "  cbnz w9, .Lalready_initialized"
  emitLn ""
  emitLn "  // Mark as initialized"
  emitLn "  mov w10, #1"
  emitLn "  strb w10, [x8]"
  emitLn ""

  -- Call each imported module initializer
  for _h : idx in [:env.imports.size] do
    let imp := env.imports[idx]!
    let decDoneLabel := s!".Linit_dec_done_{idx}"
    let impPkg? :=
      match env.getModuleIdxFor? imp.module with
      | some idx => env.getModulePackageByIdx? idx
      | none => none
    let impInitFn := withSymbolPrefix (Lean.mkModuleInitializationFunctionName imp.module impPkg?)
    emitLn s!"  // Initialize {imp.module}"
    emitLn "  mov x0, #1  // builtin"
    -- NOTE: Import init functions take only uint8_t builtin, not a world object
    emitLn s!"  bl {impInitFn}"
    emitLn "  mov x19, x0"
    emitLn "  // Check for error (inline lean_io_result_is_ok)"
    emitLn "  ldrb w8, [x19, #7]  // Load m_tag"
    emitLn "  cbnz w8, .Linit_error  // If tag != 0, error"
    emitLn "  // Dec ref (simplified for init)"
    emitLn "  ldr w8, [x19]  // Load m_rc"
    emitLn "  cmp w8, #1"
    emitLn s!"  ble {decDoneLabel}"
    emitLn "  sub w8, w8, #1"
    emitLn "  str w8, [x19]"
    emitLn s!"{decDoneLabel}:"
    emitLn ""

  -- Process all declarations for initialization
  emitLn "  // Initialize all declarations"
  for decl in decls.toList.reverse do
    match decl with
    | .fdecl name params ty body _ =>
      -- Check if this is an IO Unit initialize block (declaration itself is the initFn)
      if isIOUnitInitFn env name then
        let funcName := symbolName env name
        emitLn s!"  // Initialize IO Unit block {name}"
        emitLn s!"  mov x0, #1  // lean_io_mk_world() inlined as lean_box(0)"
        emitLn s!"  bl {funcName}"
        emitLn "  mov x19, x0  // Save IO result"
        emitLn "  ldrb w8, [x19, #7]  // Load m_tag from IO result"
        emitLn "  cbnz w8, .Linit_error  // If tag != 0, error"
        emitLn "  // Dec ref IO result"
        emitLn "  mov x0, x19"
        emitLn "  bl _lean_dec_ref"
        emitLn ""
      -- Check if this is a 0-param declaration with a separate initFn
      else if params.isEmpty then
        match getInitFnNameFor? env name with
        | some initFnName =>
          -- Named initialize block (e.g., initialize ref : IO.Ref Nat ← ...)
          let constName := symbolName env name
          let initFnMangledName := symbolName env initFnName
          emitLn s!"  // Initialize {name} via initFn {initFnName}"
          emitLn s!"  mov x0, #1  // lean_io_mk_world() inlined as lean_box(0)"
          emitLn s!"  bl {initFnMangledName}"
          emitLn "  mov x19, x0  // Save IO result"
          emitLn "  ldrb w8, [x19, #7]  // Load m_tag from IO result"
          emitLn "  cbnz w8, .Linit_error  // If tag != 0, error"
          emitLn s!"  // Extract value from IO result and store in {constName}"
          emitLn "  ldr x0, [x19, #8]  // Get field 0 (the value)"
          -- For scalar types, unbox the value; for objects, inc ref and mark persistent
          if ty.isScalar then
            -- Unbox scalar value based on type
            -- Note: uint64, usize, float, float32 are heap-allocated; uint8/16/32 are inline boxed
            match ty with
            | .uint8 | .uint16 | .uint32 =>
              emitLn "  bl _lean_unbox  // Unbox inline scalar to native integer"
            | .uint64 =>
              emitLn "  bl _lean_unbox_uint64  // Unbox heap-allocated uint64"
            | .usize =>
              emitLn "  bl _lean_unbox_usize  // Unbox heap-allocated usize"
            | .float =>
              emitLn "  bl _lean_unbox_float  // Unbox heap-allocated float"
            | .float32 =>
              emitLn "  bl _lean_unbox_float32  // Unbox heap-allocated float32"
            | _ =>
              emitLn "  bl _lean_unbox  // Default unbox"
            -- Store the unboxed scalar value
            emitLn s!"  adrp x8, {constName}@PAGE"
            emitLn s!"  add x8, x8, {constName}@PAGEOFF"
            match ty with
            | .uint8 =>
              emitLn "  strb w0, [x8]"
            | .uint16 =>
              emitLn "  strh w0, [x8]"
            | .uint32 =>
              emitLn "  str w0, [x8]"
            | .float =>
              emitLn "  str d0, [x8]  // Float returns in d0"
            | _ =>
              emitLn "  str x0, [x8]"
          else
            -- Object type: inc ref count and mark persistent
            emitLn "  bl _lean_inc  // Inc ref count before storing"
            emitLn s!"  adrp x8, {constName}@PAGE"
            emitLn s!"  add x8, x8, {constName}@PAGEOFF"
            emitLn "  str x0, [x8]"
            if ty.isObj then
              emitLn "  // Mark persistent"
              emitLn "  bl _lean_mark_persistent"
          emitLn "  // Dec ref IO result"
          emitLn "  mov x0, x19"
          emitLn "  bl _lean_dec_ref"
          emitLn ""
        | none =>
          -- Regular closed constant
          match body with
          | .unreachable =>
            -- Unreachable but no initFn - skip it
            pure ()
          | _ =>
            let constName := symbolName env name
            let initName := "__init_" ++ symbolStem env name
            emitLn s!"  // Initialize {constName}"
            emitLn s!"  bl {initName}"
            emitLn s!"  adrp x8, {constName}@PAGE"
            emitLn s!"  add x8, x8, {constName}@PAGEOFF"
            match ty with
            | .uint8 =>
              emitLn "  strb w0, [x8]"
            | .uint16 =>
              emitLn "  strh w0, [x8]"
            | .uint32 =>
              emitLn "  str w0, [x8]"
            | .float32 =>
              emitLn "  str s0, [x8]"
            | .float =>
              emitLn "  str d0, [x8]"
            | _ =>
              emitLn "  str x0, [x8]"
            if ty.isObj then
              emitLn "  // Mark persistent"
              emitLn s!"  adrp x8, {constName}@PAGE"
              emitLn s!"  add x8, x8, {constName}@PAGEOFF"
              emitLn "  ldr x0, [x8]"
              emitLn "  bl _lean_mark_persistent"
            emitLn ""
    | _ => pure ()

  emitLn ".Lalready_initialized:"
  emitLn "  // Return success - inline lean_io_result_mk_ok(lean_box(0))"
  emitLn "  mov x0, #0  // tag"
  emitLn "  mov x1, #2  // num_objs"
  emitLn "  mov x2, #0  // num_scalars"
  emitLn "  bl _lean_alloc_ctor"
  emitLn "  mov x20, x0  // Save result in callee-saved register"
  emitLn "  mov x0, x20"
  emitLn "  mov x1, #0  // field index"
  emitLn "  mov x2, #1  // lean_box(0)"
  emitLn "  bl _lean_ctor_set"
  emitLn "  mov x0, x20"
  emitLn "  mov x1, #1  // field index"
  emitLn "  mov x2, #1  // lean_box(0)"
  emitLn "  bl _lean_ctor_set"
  emitLn "  mov x0, x20  // Return result"
  emitLn "  ldp x19, x20, [sp, #16]"
  emitLn "  ldp x29, x30, [sp], #32"
  emitLn "  ret"
  emitLn ""
  emitLn ".Linit_error:"
  emitLn "  // Return error result"
  emitLn "  mov x0, x19"
  emitLn "  ldp x19, x20, [sp, #16]"
  emitLn "  ldp x29, x30, [sp], #32"
  emitLn "  ret"

/-- Emit ARM64 main wrapper function -/
def emitMainFn (modName : Name) (env : Environment) : EmitM Unit := do
  -- Check if main function exists and get its arity
  match IR.findEnvDecl env `main with
  | none => pure ()
  | some (.fdecl _ params _ _ _) =>
    let arity := params.size
    unless arity == 1 || arity == 2 do
      return ()

    emitLn ""
    emitLn "  // C-compatible main entry point"
    emitLn "  .globl _main"  -- macOS requires underscore prefix
    emitLn "  .align 2"
    emitLn "_main:"
    emitLn "  // Save frame pointer and link register"
    emitLn "  stp x29, x30, [sp, #-16]!"
    emitLn "  mov x29, sp"
    emitLn "  // Save argc and argv"
    emitLn "  stp x0, x1, [sp, #-16]!"
    emitLn ""
    emitLn "  // Call lean_setup_args(argc, argv)"
    emitLn "  bl _lean_setup_args"
    emitLn "  str x0, [sp, #8]  // Save updated argv"
    emitLn ""
    emitLn "  // Call lean_initialize_runtime_module()"
    emitLn "  bl _lean_initialize_runtime_module"
    emitLn ""
    emitLn "  // Call module initializer"
    emitLn "  mov x0, #1  // builtin flag"
    emitLn "  bl _lean_io_mk_world"
    let initPkg? := env.getModulePackage?
    let initFnName := withSymbolPrefix (Lean.mkModuleInitializationFunctionName modName initPkg?)
    emitLn s!"  bl {initFnName}"
    emitLn "  mov x19, x0  // Save init result"
    emitLn ""
    emitLn "  // Mark end of initialization"
    emitLn "  bl _lean_io_mark_end_initialization"
    emitLn ""
    emitLn "  // Check if initialization succeeded"
    emitLn "  mov x0, x19"
    emitLn "  bl _lean_io_result_is_ok"
    emitLn "  cbz x0, .Linit_failed"
    emitLn ""
    emitLn "  // Init succeeded, dec result and init task manager"
    emitLn "  mov x0, x19"
    emitLn "  bl _lean_dec_ref"
    emitLn "  bl _lean_init_task_manager"
    emitLn ""

    if arity == 2 then
      -- Build argument list from argv
      emitLn "  // Build argument list from argv"
      emitLn "  ldp x20, x21, [sp]  // Load argc and argv"
      emitLn "  mov x0, #0"
      emitLn "  bl _lean_box  // Empty list"
      emitLn "  mov x22, x0"
      emitLn ".Lbuild_args:"
      emitLn "  subs x20, x20, #1"
      emitLn "  ble .Largs_done"
      emitLn "  ldr x0, [x21, x20, lsl #3]  // argv[i]"
      emitLn "  bl _lean_mk_string"
      emitLn "  mov x23, x0"
      emitLn "  // Allocate cons cell"
      emitLn "  mov x0, #1  // tag for cons"
      emitLn "  mov x1, #2  // 2 fields"
      emitLn "  mov x2, #0  // 0 scalars"
      emitLn "  bl _lean_alloc_ctor"
      emitLn "  mov x1, #0"
      emitLn "  mov x2, x23"
      emitLn "  bl _lean_ctor_set  // Set head"
      emitLn "  mov x1, #1"
      emitLn "  mov x2, x22"
      emitLn "  bl _lean_ctor_set  // Set tail"
      emitLn "  mov x22, x0"
      emitLn "  b .Lbuild_args"
      emitLn ".Largs_done:"
      emitLn "  // Call _lean_main(args, world)"
      emitLn "  mov x0, x22"
      emitLn "  bl _lean_io_mk_world"
      emitLn "  mov x1, x0"
      emitLn "  mov x0, x22"
      emitLn "  bl _lean_main"
    else
      emitLn "  // Call _lean_main(world)"
      emitLn "  bl _lean_io_mk_world"
      emitLn "  bl _lean_main"

    emitLn "  mov x19, x0  // Save main result"
    emitLn ""
    emitLn ".Linit_failed:"
    emitLn "  // Finalize task manager"
    emitLn "  bl _lean_finalize_task_manager"
    emitLn ""
    emitLn "  // Check if result is ok"
    emitLn "  mov x0, x19"
    emitLn "  bl _lean_io_result_is_ok"
    emitLn "  cbz x0, .Lmain_error"
    emitLn ""
    emitLn "  // Success path - get return value"
    emitLn "  mov x0, x19"
    emitLn "  bl _lean_io_result_get_value"
    emitLn "  mov x20, x0"

    -- For simplicity, always check if scalar (UInt32) or return 0
    emitLn "  // Check if return value is scalar (UInt32)"
    emitLn "  mov x0, x20"
    emitLn "  bl _lean_is_scalar"
    emitLn "  cbz x0, .Lreturn_zero"
    emitLn "  // Unbox UInt32"
    emitLn "  mov x0, x20"
    emitLn "  bl _lean_unbox_uint32"
    emitLn "  mov x20, x0"
    emitLn "  b .Lreturn_value"
    emitLn ".Lreturn_zero:"
    emitLn "  mov x20, #0"

    emitLn ".Lreturn_value:"
    emitLn "  mov x0, x19"
    emitLn "  bl _lean_dec_ref"
    emitLn "  mov x0, x20"
    emitLn "  ldp xzr, xzr, [sp], #16"
    emitLn "  ldp x29, x30, [sp], #16"
    emitLn "  ret"
    emitLn ""
    emitLn ".Lmain_error:"
    emitLn "  // Error path"
    emitLn "  mov x0, x19"
    emitLn "  bl _lean_io_result_show_error"
    emitLn "  mov x0, x19"
    emitLn "  bl _lean_dec_ref"
    emitLn "  mov x0, #1"
    emitLn "  ldp xzr, xzr, [sp], #16"
    emitLn "  ldp x29, x30, [sp], #16"
    emitLn "  ret"
  | _ => pure ()

/-- Compile multiple declarations to ARM64 assembly -/
def emitDecls (env : Environment) (modName : Name) (decls : Array IR.Decl) : String :=
  let initState : EmitState := { output := "" }
  let (_result, finalState) := (do
    emitPreamble
    emitDataSection env decls  -- Emit .data section with globals

    -- Emit all function declarations
    for decl in decls do
      match decl with
      | .fdecl name params _ body _ =>
        -- For 0-param functions, emit init functions with double underscore prefix
        -- but skip those with unreachable bodies (IO initializers)
        if params.isEmpty then
          match body with
          | .unreachable =>
            -- Skip unreachable 0-param functions (they are IO refs initialized by initFn calls)
            pure ()
          | _ =>
            let initFnName := "__init_" ++ symbolStem env name
            let machineFunc := InstrSelect.compileDecl env decl
            emitMachineFunction machineFunc (some initFnName)
        else
          let machineFunc := InstrSelect.compileDecl env decl
          emitMachineFunction machineFunc (some (symbolName env name))
      | _ => pure ()

    -- Emit module initialization routine
    -- NOTE: We don't emit the C main wrapper here because it needs to use
    -- inline runtime functions. Instead, users should provide a C shim that
    -- calls into the ARM64-compiled _lean_main function.
    emitInitFunction env modName decls
    -- emitMainFn modName env  -- Disabled: use C shim instead
  ).run initState
  finalState.output

/-- Main entry point for compiling to ARM64 assembly -/
def compileToARM64 (env : Environment) (modName : Name) (decls : Array IR.Decl) : String :=
  emitDecls env modName decls

/-- Emit ARM64 assembly for a module (matches emitC API) -/
@[export lean_ir_emit_arm64]
def emitARM64 (env : Environment) (modName : Name) : Except String String :=
  let decls := IR.getDecls env
  Except.ok (emitDecls env modName decls.toArray)

end EmitARM64
end Lean.Compiler.Backend
