/-
Copyright (c) 2025 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Assistant
-/

module

prelude
public import Lean.Compiler.Backend.ARM64.Reg
public import Lean.Compiler.Backend.ARM64.RegClass

public section

namespace Lean.Compiler.Backend.ARM64

/-!
# ARM64 Instructions

This module defines the instruction representation for the ARM64 backend.
Instructions operate on either physical registers (after allocation) or
virtual registers (before allocation).
-/

/-- Condition codes for conditional instructions. -/
inductive Cond where
  | eq | ne | lt | le | gt | ge | lo | ls | hi | hs
  deriving Inhabited, BEq, DecidableEq, Repr, Hashable

instance : ToString Cond where
  toString
    | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le"
    | .gt => "gt" | .ge => "ge" | .lo => "lo" | .ls => "ls"
    | .hi => "hi" | .hs => "hs"

namespace Cond

/-- Negate a condition -/
def negate : Cond → Cond
  | .eq => .ne | .ne => .eq
  | .lt => .ge | .ge => .lt
  | .le => .gt | .gt => .le
  | .lo => .hs | .hs => .lo
  | .ls => .hi | .hi => .ls

end Cond

/-- Operand for ARM64 instructions. -/
inductive Operand where
  | reg (r : Reg)
  | imm (n : Int)
  | mem (base : Reg) (offset : Int)
  | label (name : String)
  deriving Inhabited, BEq, Repr

instance : ToString Operand where
  toString
    | .reg r => toString r
    | .imm n => s!"#{n}"
    | .mem base offset =>
      if offset = 0 then s!"[{base}]"
      else s!"[{base}, #{offset}]"
    | .label name => name

namespace Operand

/-- Create register operand from physical register -/
def ofPhys (r : PhysReg) : Operand := .reg (.phys r)

/-- Create register operand from VarId -/
def ofVar (v : IR.VarId) : Operand := .reg (.virt v)

/-- Check if operand is a register -/
def isReg : Operand → Bool
  | .reg _ => true
  | _ => false

/-- Check if operand is an immediate -/
def isImm : Operand → Bool
  | .imm _ => true
  | _ => false

/-- Get register if operand is a register -/
def getReg? : Operand → Option Reg
  | .reg r => some r
  | _ => none

/-- Get immediate value if operand is an immediate -/
def getImm? : Operand → Option Int
  | .imm n => some n
  | _ => none

end Operand

/-!
## Instruction Definitions

ARM64 instruction set used by the backend, covering:
- Data processing (add, sub, mul, div, logical, shifts)
- Move operations (mov, movz, movk, adrp)
- Load/Store (ldr, str, ldp, stp variants)
- Comparisons (cmp, tst, csel)
- Branches (b, bl, br, blr, ret, conditional)
- Stack operations (push, pop)
- Floating-point (fadd, fsub, fmul, fdiv, fcmp, fmov, conversions)
- Pseudo-instructions (label, comment)
-/

/-- Subset of the ARM64 instruction set used by the backend. -/
inductive Instr where
  -- Data processing instructions
  | add (dst : Reg) (src1 : Reg) (src2 : Operand)
  | sub (dst : Reg) (src1 : Reg) (src2 : Operand)
  | mul (dst : Reg) (src1 : Reg) (src2 : Reg)
  | sdiv (dst : Reg) (src1 : Reg) (src2 : Reg)
  | udiv (dst : Reg) (src1 : Reg) (src2 : Reg)
  | uxtb (dst : Reg) (src : Reg)  -- zero-extend byte (8 bits) to 64 bits
  | uxth (dst : Reg) (src : Reg)  -- zero-extend halfword (16 bits) to 64 bits
  | madd (dst : Reg) (src1 : Reg) (src2 : Reg) (acc : Reg)  -- dst = src1 * src2 + acc
  | msub (dst : Reg) (src1 : Reg) (src2 : Reg) (acc : Reg)  -- dst = acc - src1 * src2
  | neg (dst : Reg) (src : Reg)   -- dst = -src

  -- Logical instructions
  | and (dst : Reg) (src1 : Reg) (src2 : Operand)
  | orr (dst : Reg) (src1 : Reg) (src2 : Operand)
  | eor (dst : Reg) (src1 : Reg) (src2 : Operand)
  | lsl (dst : Reg) (src : Reg) (shift : Operand)
  | lsr (dst : Reg) (src : Reg) (shift : Operand)
  | asr (dst : Reg) (src : Reg) (shift : Operand)
  | mvn (dst : Reg) (src : Reg)   -- bitwise NOT

  -- Move instructions
  | mov (dst : Reg) (src : Operand)
  | movz (dst : Reg) (imm : Nat) (shift : Nat)
  | movk (dst : Reg) (imm : Nat) (shift : Nat)
  | adrp (dst : Reg) (label : String)

  -- Load / store instructions
  | ldr (dst : Reg) (src : Operand) (suffix : String := "")
  | ldrw (dst : Reg) (src : Operand)  -- Load word (32-bit) - renders dst as w register
  | ldrs (dst : Reg) (src : Operand)  -- Load single-precision float (32-bit)
  | ldrd (dst : Reg) (src : Operand)  -- Load double-precision float (64-bit)
  | ldrb (dst : Reg) (src : Operand)
  | ldrh (dst : Reg) (src : Operand)
  | ldrsb (dst : Reg) (src : Operand) -- load signed byte
  | ldrsh (dst : Reg) (src : Operand) -- load signed halfword
  | ldrsw (dst : Reg) (src : Operand) -- load signed word
  | str (src : Reg) (dst : Operand)
  | strw (src : Reg) (dst : Operand)  -- Store word (32-bit)
  | strs (src : Reg) (dst : Operand)  -- Store single-precision float (32-bit)
  | strd (src : Reg) (dst : Operand)  -- Store double-precision float (64-bit)
  | strb (src : Reg) (dst : Operand)
  | strh (src : Reg) (dst : Operand)

  -- Load / store pair
  | ldp (dst1 : Reg) (dst2 : Reg) (base : Reg) (offset : Int)
  | stp (src1 : Reg) (src2 : Reg) (base : Reg) (offset : Int)

  -- Comparison
  | cmp (src1 : Reg) (src2 : Operand)
  | cmn (src1 : Reg) (src2 : Operand)  -- compare negative
  | tst (src1 : Reg) (src2 : Operand)

  -- Conditional select
  | csel (dst : Reg) (src1 : Reg) (src2 : Reg) (cond : Cond)
  | cset (dst : Reg) (cond : Cond)    -- set to 1 if cond, else 0
  | csinc (dst : Reg) (src1 : Reg) (src2 : Reg) (cond : Cond) -- if cond then src1 else src2+1

  -- Branch instructions
  | branch (label : String)
  | bl (fn : String)
  | br (reg : Reg)
  | blr (reg : Reg)
  | ret
  | bCond (cond : Cond) (label : String)
  | cbz (reg : Reg) (label : String)   -- compare and branch if zero
  | cbnz (reg : Reg) (label : String)  -- compare and branch if not zero
  | tbz (reg : Reg) (bit : Nat) (label : String)  -- test bit and branch if zero
  | tbnz (reg : Reg) (bit : Nat) (label : String) -- test bit and branch if not zero

  -- Stack operations (pseudo-instructions expanded during emission)
  | push (regs : Array Reg)
  | pop (regs : Array Reg)

  -- Floating point
  | fadd (prec : FloatPrec) (dst : Reg) (src1 : Reg) (src2 : Reg)
  | fsub (prec : FloatPrec) (dst : Reg) (src1 : Reg) (src2 : Reg)
  | fmul (prec : FloatPrec) (dst : Reg) (src1 : Reg) (src2 : Reg)
  | fdiv (prec : FloatPrec) (dst : Reg) (src1 : Reg) (src2 : Reg)
  | fneg (prec : FloatPrec) (dst : Reg) (src : Reg)
  | fabs (prec : FloatPrec) (dst : Reg) (src : Reg)
  | fsqrt (prec : FloatPrec) (dst : Reg) (src : Reg)
  | fcmp (prec : FloatPrec) (src1 : Reg) (src2 : Reg)
  | fmov (prec : FloatPrec) (dst : Reg) (src : Reg)
  | scvtf (prec : FloatPrec) (dst : Reg) (src : Reg)  -- signed int to float
  | ucvtf (prec : FloatPrec) (dst : Reg) (src : Reg)  -- unsigned int to float
  | fcvtzs (prec : FloatPrec) (dst : Reg) (src : Reg) -- float to signed int (toward zero)
  | fcvtzu (prec : FloatPrec) (dst : Reg) (src : Reg) -- float to unsigned int (toward zero)
  | fcvt (dstPrec : FloatPrec) (srcPrec : FloatPrec) (dst : Reg) (src : Reg) -- float precision conversion

  -- Pseudo-instructions
  | label (name : String)
  | comment (text : String)
  | nop
  deriving Inhabited, Repr

namespace Instr

set_option maxHeartbeats 0 in
/-- Get registers read by this instruction -/
def uses : Instr → Array Reg
  | .add _ s1 (.reg s2) => #[s1, s2]
  | .add _ s1 _ => #[s1]
  | .sub _ s1 (.reg s2) => #[s1, s2]
  | .sub _ s1 _ => #[s1]
  | .mul _ s1 s2 => #[s1, s2]
  | .sdiv _ s1 s2 => #[s1, s2]
  | .udiv _ s1 s2 => #[s1, s2]
  | .uxtb _ s => #[s]
  | .uxth _ s => #[s]
  | .madd _ s1 s2 acc => #[s1, s2, acc]
  | .msub _ s1 s2 acc => #[s1, s2, acc]
  | .neg _ s => #[s]
  | .and _ s1 (.reg s2) => #[s1, s2]
  | .and _ s1 _ => #[s1]
  | .orr _ s1 (.reg s2) => #[s1, s2]
  | .orr _ s1 _ => #[s1]
  | .eor _ s1 (.reg s2) => #[s1, s2]
  | .eor _ s1 _ => #[s1]
  | .lsl _ s (.reg sh) => #[s, sh]
  | .lsl _ s _ => #[s]
  | .lsr _ s (.reg sh) => #[s, sh]
  | .lsr _ s _ => #[s]
  | .asr _ s (.reg sh) => #[s, sh]
  | .asr _ s _ => #[s]
  | .mvn _ s => #[s]
  | .mov _ (.reg s) => #[s]
  | .mov _ _ => #[]
  | .movz _ _ _ => #[]
  | .movk d _ _ => #[d]  -- movk reads dst before modifying
  | .adrp _ _ => #[]
  | .ldr _ (.mem base _) _ => #[base]
  | .ldr _ (.reg r) _ => #[r]
  | .ldr _ _ _ => #[]
  | .ldrw _ (.mem base _) => #[base]
  | .ldrw _ (.reg r) => #[r]
  | .ldrw _ _ => #[]
  | .ldrs _ (.mem base _) => #[base]
  | .ldrs _ (.reg r) => #[r]
  | .ldrs _ _ => #[]
  | .ldrd _ (.mem base _) => #[base]
  | .ldrd _ (.reg r) => #[r]
  | .ldrd _ _ => #[]
  | .ldrb _ (.mem base _) => #[base]
  | .ldrb _ _ => #[]
  | .ldrh _ (.mem base _) => #[base]
  | .ldrh _ _ => #[]
  | .ldrsb _ (.mem base _) => #[base]
  | .ldrsb _ _ => #[]
  | .ldrsh _ (.mem base _) => #[base]
  | .ldrsh _ _ => #[]
  | .ldrsw _ (.mem base _) => #[base]
  | .ldrsw _ _ => #[]
  | .str s (.mem base _) => #[s, base]
  | .str s _ => #[s]
  | .strw s (.mem base _) => #[s, base]
  | .strw s _ => #[s]
  | .strs s (.mem base _) => #[s, base]
  | .strs s _ => #[s]
  | .strd s (.mem base _) => #[s, base]
  | .strd s _ => #[s]
  | .strb s (.mem base _) => #[s, base]
  | .strb s _ => #[s]
  | .strh s (.mem base _) => #[s, base]
  | .strh s _ => #[s]
  | .ldp _ _ base _ => #[base]
  | .stp s1 s2 base _ => #[s1, s2, base]
  | .cmp s1 (.reg s2) => #[s1, s2]
  | .cmp s1 _ => #[s1]
  | .cmn s1 (.reg s2) => #[s1, s2]
  | .cmn s1 _ => #[s1]
  | .tst s1 (.reg s2) => #[s1, s2]
  | .tst s1 _ => #[s1]
  | .csel _ s1 s2 _ => #[s1, s2]
  | .cset _ _ => #[]
  | .csinc _ s1 s2 _ => #[s1, s2]
  | .branch _ => #[]
  | .bl _ => #[]
  | .br r => #[r]
  | .blr r => #[r]
  | .ret => #[.phys .x0]  -- implicitly reads return value
  | .bCond _ _ => #[]
  | .cbz r _ => #[r]
  | .cbnz r _ => #[r]
  | .tbz r _ _ => #[r]
  | .tbnz r _ _ => #[r]
  | .push regs => regs
  | .pop _ => #[]
  | .fadd _ _ s1 s2 => #[s1, s2]
  | .fsub _ _ s1 s2 => #[s1, s2]
  | .fmul _ _ s1 s2 => #[s1, s2]
  | .fdiv _ _ s1 s2 => #[s1, s2]
  | .fneg _ _ s => #[s]
  | .fabs _ _ s => #[s]
  | .fsqrt _ _ s => #[s]
  | .fcmp _ s1 s2 => #[s1, s2]
  | .fmov _ _ s => #[s]
  | .scvtf _ _ s => #[s]
  | .ucvtf _ _ s => #[s]
  | .fcvtzs _ _ s => #[s]
  | .fcvtzu _ _ s => #[s]
  | .fcvt _ _ _ s => #[s]
  | .label _ => #[]
  | .comment _ => #[]
  | .nop => #[]

set_option maxHeartbeats 0 in
/-- Get register defined by this instruction (if any) -/
def defs : Instr → Array Reg
  | .add d _ _ => #[d]
  | .sub d _ _ => #[d]
  | .mul d _ _ => #[d]
  | .sdiv d _ _ => #[d]
  | .udiv d _ _ => #[d]
  | .uxtb d _ => #[d]
  | .uxth d _ => #[d]
  | .madd d _ _ _ => #[d]
  | .msub d _ _ _ => #[d]
  | .neg d _ => #[d]
  | .and d _ _ => #[d]
  | .orr d _ _ => #[d]
  | .eor d _ _ => #[d]
  | .lsl d _ _ => #[d]
  | .lsr d _ _ => #[d]
  | .asr d _ _ => #[d]
  | .mvn d _ => #[d]
  | .mov d _ => #[d]
  | .movz d _ _ => #[d]
  | .movk d _ _ => #[d]
  | .adrp d _ => #[d]
  | .ldr d _ _ => #[d]
  | .ldrw d _ => #[d]
  | .ldrs d _ => #[d]
  | .ldrd d _ => #[d]
  | .ldrb d _ => #[d]
  | .ldrh d _ => #[d]
  | .ldrsb d _ => #[d]
  | .ldrsh d _ => #[d]
  | .ldrsw d _ => #[d]
  | .str _ _ => #[]
  | .strw _ _ => #[]
  | .strs _ _ => #[]
  | .strd _ _ => #[]
  | .strb _ _ => #[]
  | .strh _ _ => #[]
  | .ldp d1 d2 _ _ => #[d1, d2]
  | .stp _ _ _ _ => #[]
  | .cmp _ _ => #[]
  | .cmn _ _ => #[]
  | .tst _ _ => #[]
  | .csel d _ _ _ => #[d]
  | .cset d _ => #[d]
  | .csinc d _ _ _ => #[d]
  | .branch _ => #[]
  | .bl _ => #[.phys .x0]  -- implicitly defines return value (and clobbers caller-saved)
  | .br _ => #[]
  | .blr _ => #[.phys .x0]
  | .ret => #[]
  | .bCond _ _ => #[]
  | .cbz _ _ => #[]
  | .cbnz _ _ => #[]
  | .tbz _ _ _ => #[]
  | .tbnz _ _ _ => #[]
  | .push _ => #[]
  | .pop regs => regs
  | .fadd _ d _ _ => #[d]
  | .fsub _ d _ _ => #[d]
  | .fmul _ d _ _ => #[d]
  | .fdiv _ d _ _ => #[d]
  | .fneg _ d _ => #[d]
  | .fabs _ d _ => #[d]
  | .fsqrt _ d _ => #[d]
  | .fcmp _ _ _ => #[]
  | .fmov _ d _ => #[d]
  | .scvtf _ d _ => #[d]
  | .ucvtf _ d _ => #[d]
  | .fcvtzs _ d _ => #[d]
  | .fcvtzu _ d _ => #[d]
  | .fcvt _ _ d _ => #[d]
  | .label _ => #[]
  | .comment _ => #[]
  | .nop => #[]

/-- Check if instruction is a branch -/
def isBranch : Instr → Bool
  | .branch _ | .bl _ | .br _ | .blr _ | .ret
  | .bCond _ _ | .cbz _ _ | .cbnz _ _ | .tbz _ _ _ | .tbnz _ _ _ => true
  | _ => false

/-- Check if instruction is a call -/
def isCall : Instr → Bool
  | .bl _ | .blr _ => true
  | _ => false

/-- Check if instruction is a return -/
def isReturn : Instr → Bool
  | .ret => true
  | _ => false

/-- Check if instruction is a label -/
def isLabel : Instr → Bool
  | .label _ => true
  | _ => false

/-- Check if instruction has side effects -/
def hasSideEffects : Instr → Bool
  | .str _ _ | .strw _ _ | .strs _ _ | .strd _ _ | .strb _ _ | .strh _ _ | .stp _ _ _ _
  | .bl _ | .blr _ | .push _ => true
  | _ => false

set_option maxHeartbeats 0 in
/-- Render an instruction using GNU assembler syntax. -/
def toString : Instr → String
  | add dst src1 src2 => s!"add {dst}, {src1}, {src2}"
  | sub dst src1 src2 => s!"sub {dst}, {src1}, {src2}"
  | mul dst src1 src2 => s!"mul {dst}, {src1}, {src2}"
  | sdiv dst src1 src2 => s!"sdiv {dst}, {src1}, {src2}"
  | udiv dst src1 src2 => s!"udiv {dst}, {src1}, {src2}"
  | uxtb dst src => s!"uxtb {dst}, {src}"
  | uxth dst src => s!"uxth {dst}, {src}"
  | madd dst s1 s2 acc => s!"madd {dst}, {s1}, {s2}, {acc}"
  | msub dst s1 s2 acc => s!"msub {dst}, {s1}, {s2}, {acc}"
  | neg dst src => s!"neg {dst}, {src}"
  | and dst src1 src2 => s!"and {dst}, {src1}, {src2}"
  | orr dst src1 src2 => s!"orr {dst}, {src1}, {src2}"
  | eor dst src1 src2 => s!"eor {dst}, {src1}, {src2}"
  | lsl dst src shift => s!"lsl {dst}, {src}, {shift}"
  | lsr dst src shift => s!"lsr {dst}, {src}, {shift}"
  | asr dst src shift => s!"asr {dst}, {src}, {shift}"
  | mvn dst src => s!"mvn {dst}, {src}"
  | mov dst src => s!"mov {dst}, {src}"
  | movz dst imm shift => s!"movz {dst}, #{imm}, lsl #{shift}"
  | movk dst imm shift => s!"movk {dst}, #{imm}, lsl #{shift}"
  | adrp dst lbl => s!"adrp {dst}, {lbl}"
  | ldr dst src suffix =>
    if suffix.isEmpty then s!"ldr {dst}, {src}"
    else s!"ldr {dst}, {src}{suffix}"
  | ldrw dst src =>
    let dstStr := Reg.toGPR32String dst
    s!"ldr {dstStr}, {src}"
  | ldrs dst src =>
    let dstStr := match dst with
      | .phys p => PhysReg.toFPString .single p
      | _ => s!"{dst}"
    s!"ldr {dstStr}, {src}"
  | ldrd dst src =>
    let dstStr := match dst with
      | .phys p => PhysReg.toFPString .double p
      | _ => s!"{dst}"
    s!"ldr {dstStr}, {src}"
  | ldrb dst src =>
    let dstStr := Reg.toGPR32String dst
    s!"ldrb {dstStr}, {src}"
  | ldrh dst src =>
    let dstStr := Reg.toGPR32String dst
    s!"ldrh {dstStr}, {src}"
  | ldrsb dst src => s!"ldrsb {dst}, {src}"
  | ldrsh dst src => s!"ldrsh {dst}, {src}"
  | ldrsw dst src => s!"ldrsw {dst}, {src}"
  | str src dst => s!"str {src}, {dst}"
  | strw src dst =>
    let srcStr := Reg.toGPR32String src
    s!"str {srcStr}, {dst}"
  | strs src dst =>
    let srcStr := match src with
      | .phys p => PhysReg.toFPString .single p
      | _ => s!"{src}"
    s!"str {srcStr}, {dst}"
  | strd src dst =>
    let srcStr := match src with
      | .phys p => PhysReg.toFPString .double p
      | _ => s!"{src}"
    s!"str {srcStr}, {dst}"
  | strb src dst =>
    let srcStr := Reg.toGPR32String src
    s!"strb {srcStr}, {dst}"
  | strh src dst =>
    let srcStr := Reg.toGPR32String src
    s!"strh {srcStr}, {dst}"
  | ldp dst1 dst2 base offset => s!"ldp {dst1}, {dst2}, [{base}, #{offset}]"
  | stp src1 src2 base offset => s!"stp {src1}, {src2}, [{base}, #{offset}]"
  | cmp src1 src2 => s!"cmp {src1}, {src2}"
  | cmn src1 src2 => s!"cmn {src1}, {src2}"
  | tst src1 src2 => s!"tst {src1}, {src2}"
  | csel dst src1 src2 cond => s!"csel {dst}, {src1}, {src2}, {cond}"
  | cset dst cond => s!"cset {dst}, {cond}"
  | csinc dst s1 s2 cond => s!"csinc {dst}, {s1}, {s2}, {cond}"
  | branch lbl => s!"b {lbl}"
  | bl fn => s!"bl {fn}"
  | br reg => s!"br {reg}"
  | blr reg => s!"blr {reg}"
  | ret => "ret"
  | bCond cond lbl => s!"b.{cond} {lbl}"
  | cbz reg lbl => s!"cbz {reg}, {lbl}"
  | cbnz reg lbl => s!"cbnz {reg}, {lbl}"
  | tbz reg bit lbl => s!"tbz {reg}, #{bit}, {lbl}"
  | tbnz reg bit lbl => s!"tbnz {reg}, #{bit}, {lbl}"
  | push _ => "stp ..." -- TODO: pretty print stack ops if needed
  | pop _ => "ldp ..."
  | fadd prec dst src1 src2 => s!"fadd.{prec} {dst}, {src1}, {src2}"
  | fsub prec dst src1 src2 => s!"fsub.{prec} {dst}, {src1}, {src2}"
  | fmul prec dst src1 src2 => s!"fmul.{prec} {dst}, {src1}, {src2}"
  | fdiv prec dst src1 src2 => s!"fdiv.{prec} {dst}, {src1}, {src2}"
  | fneg prec dst src => s!"fneg.{prec} {dst}, {src}"
  | fabs prec dst src => s!"fabs.{prec} {dst}, {src}"
  | fsqrt prec dst src => s!"fsqrt.{prec} {dst}, {src}"
  | fcmp prec src1 src2 => s!"fcmp.{prec} {src1}, {src2}"
  | fmov prec dst src => s!"fmov.{prec} {dst}, {src}"
  | scvtf prec dst src => s!"scvtf.{prec} {dst}, {src}"
  | ucvtf prec dst src => s!"ucvtf.{prec} {dst}, {src}"
  | fcvtzs prec dst src => s!"fcvtzs.{prec} {dst}, {src}"
  | fcvtzu prec dst src => s!"fcvtzu.{prec} {dst}, {src}"
  | fcvt dstP srcP dst src => s!"fcvt {dstP}:{srcP} {dst}, {src}"
  | label name => s!"{name}:"
  | comment text => s!"// {text}"
  | nop => "nop"

instance : ToString Instr := ⟨toString⟩

end Instr

/-!
## Basic Block and Machine Function
-/

/-- A basic block in the generated machine function. -/
structure BasicBlock where
  label : String
  instrs : Array Instr
  deriving Inhabited

/-- Record representing an emitted string literal. -/
structure StringLiteral where
  id : Nat := 0
  ptrLabel : String
  dataLabel : String
  value : String
  deriving Inhabited

/-- Machine function produced by instruction selection. -/
structure MachineFunction where
  name : Name
  blocks : Array BasicBlock
  stringLits : Array StringLiteral
  deriving Inhabited

end Lean.Compiler.Backend.ARM64

end
