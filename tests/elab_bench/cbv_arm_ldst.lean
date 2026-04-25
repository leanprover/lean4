/-
Tests that `decide_cbv` can evaluate ARMv8 load/store instruction decoding and
execution, serving as a stress test for the CBV evaluator on nested pattern
matching over bitvectors.

All types are complete for exhaustive pattern matching, but only LDST
instruction handlers have real implementations.

Extracted from `LNSym` (https://github.com/leanprover/LNSym), an ARMv8
symbolic simulator. Original code released under Apache 2.0 license.
-/

----------------------------------------------------------------------
-- match_bv macro infrastructure (from Arm/BitVec.lean)
----------------------------------------------------------------------

namespace BitVec

open BitVec

abbrev partInstall (hi lo : Nat) (val : BitVec (hi - lo + 1)) (x : BitVec n): BitVec n :=
  let mask := allOnes (hi - lo + 1)
  let val_aligned := (zeroExtend n val) <<< lo
  let mask_with_hole := ~~~ ((zeroExtend n mask) <<< lo)
  let x_with_hole := x &&& mask_with_hole
  x_with_hole ||| val_aligned

open Lean

abbrev BVPatComp := TSyntax `bvpat_comp
abbrev BVPat := TSyntax `bvpat

declare_syntax_cat bvpat_comp
syntax num : bvpat_comp
syntax ident ":" num : bvpat_comp

declare_syntax_cat bvpat
syntax "[" bvpat_comp,* "]" : bvpat

def BVPatComp.length (c : BVPatComp) : Nat := Id.run do
  match c with
  | `(bvpat_comp| $n:num) =>
    let some str := n.raw.isLit? `num | pure 0
    return str.length
  | `(bvpat_comp| $_:ident : $n:num) =>
    return n.raw.toNat
  | _ =>
    return 0

def BVPatComp.toBVLit? (c : BVPatComp) : MacroM (Option Term) := do
  match c with
  | `(bvpat_comp| $n:num) =>
    let len := c.length
    let some str := n.raw.isLit? `num | Macro.throwErrorAt c "invalid bit-vector literal"
    let bs := str.toList
    let mut val := 0
    for b in bs do
      if b = '1' then
        val := 2*val + 1
      else if b = '0' then
        val := 2*val
      else
        Macro.throwErrorAt c "invalid bit-vector literal, '0'/'1's expected"
    let r ← `(BitVec.ofNat $(quote len) $(quote val))
    return some r
  | _ => return none

def BVPatComp.toBVVar? (c : BVPatComp) : MacroM (Option (TSyntax `ident)) := do
  match c with
  | `(bvpat_comp| $x:ident : $_:num) =>
    return some x
  | _ => return none

def BVPat.getComponents (p : BVPat) : Array BVPatComp :=
  match p with
  | `(bvpat| [$comp,*]) => comp.getElems.reverse
  | _ => #[]

def BVPat.length (p : BVPat) : Nat := Id.run do
  let mut sz := 0
  for c in p.getComponents do
    sz := sz + c.length
  return sz

def genBVPatMatchTest (var : Term) (pat : BVPat) : MacroM Term := do
  let mut shift := 0
  let mut result ← `(true)
  for c in pat.getComponents do
    let len := c.length
    if let some bv ← c.toBVLit? then
      let test ← `(extractLsb $(quote (shift + (len - 1))) $(quote shift) $var == $bv)
      result ← `($result && $test)
    shift := shift + len
  return result

def declBVPatVars (var : Term) (pat : BVPat) (rhs : Term) : MacroM Term := do
  let mut result := rhs
  let mut shift  := 0
  for c in pat.getComponents do
    let len := c.length
    if let some y ← c.toBVVar? then
      let rhs ← `(extractLsb $(quote (shift + (len - 1))) $(quote shift) $var)
      result ← `(let $y := $rhs; $result)
    shift := shift + len
  return result

syntax "match_bv " term "with" (atomic("| " bvpat) " => " term)* ("| " "_ " " => " term) : term
macro_rules
  | `(match_bv $discr:term with
      $[ | $ps:bvpat => $rhss:term ]*
         | _ => $rhsElse:term) => do
  let mut result := rhsElse
  let x ← `(discr)
  for p in ps.reverse, rhs in rhss.reverse do
    let test ← genBVPatMatchTest x p
    let rhs ← declBVPatVars x p rhs
    result ← `(if $test then $rhs else $result)
  `(let discr := $discr; $result)

abbrev lsb (x : BitVec n) (i : Nat) : BitVec 1 :=
  BitVec.ofBool (getLsbD x i)

end BitVec

open BitVec (lsb)

----------------------------------------------------------------------
-- Map type (from Arm/Map.lean)
----------------------------------------------------------------------

def Map (α : Type u) (β : Type v) := List (α × β)

def Map.find? [DecidableEq α] (m : Map α β) (a' : α) : Option β :=
  match m with
  | [] => none
  | (a, b) :: m => if a = a' then some b else find? m a'

----------------------------------------------------------------------
-- Program type
----------------------------------------------------------------------

abbrev Program := Map (BitVec 64) (BitVec 32)

----------------------------------------------------------------------
-- State (from Arm/State.lean)
----------------------------------------------------------------------

section State

abbrev Store α β := α → β

def read_store {α β : Type} [DecidableEq α]
  (a : α) (store : Store α β) : β :=
  store a

def write_store {α β : Type} [DecidableEq α]
  (a : α) (b : β) (store : Store α β) : Store α β :=
  fun x => if x = a then b else (store x)

inductive StateError where
  | None                       : StateError
  | NotFound (e : String)      : StateError
  | Unimplemented (e : String) : StateError
  | Illegal (e : String)       : StateError
  | Fault (e : String)         : StateError
  | Other (e : String)         : StateError
deriving DecidableEq, Repr

inductive PFlag where
  | N : PFlag
  | Z : PFlag
  | C : PFlag
  | V : PFlag
deriving DecidableEq, Repr

structure PState where
  n : BitVec 1
  z : BitVec 1
  c : BitVec 1
  v : BitVec 1
deriving DecidableEq, Repr

structure ArmState where
  gpr        : Store (BitVec 5) (BitVec 64)
  sfp        : Store (BitVec 5) (BitVec 128)
  pc         : BitVec 64
  pstate     : PState
  mem        : Store (BitVec 64) (BitVec 8)
  program    : Program
  error      : StateError


-- Basic State Accessors and Updaters

def read_base_gpr (idx : BitVec 5) (s : ArmState) : BitVec 64 :=
  read_store idx s.gpr

def write_base_gpr (idx : BitVec 5) (val : BitVec 64) (s : ArmState)
  : ArmState :=
    let new_gpr := write_store idx val s.gpr
    { s with gpr := new_gpr }

def read_base_sfp (idx : BitVec 5) (s : ArmState) : BitVec 128 :=
    read_store idx s.sfp

def write_base_sfp (idx : BitVec 5) (val : BitVec 128) (s : ArmState) : ArmState :=
   let new_sfp := write_store idx val s.sfp
   { s with sfp := new_sfp }

def read_base_pc (s : ArmState) : BitVec 64 :=
  s.pc

def write_base_pc (val : BitVec 64) (s : ArmState) : ArmState :=
  { s with pc := val }

def read_base_flag (flag : PFlag) (s : ArmState) : BitVec 1 :=
  open PFlag in
  let pstate := s.pstate
  match flag with
  | N => pstate.n
  | Z => pstate.z
  | C => pstate.c
  | V => pstate.v

def write_base_flag (flag : PFlag) (val : BitVec 1) (s : ArmState) : ArmState :=
  open PFlag in
  let pstate := s.pstate
  let new_pstate :=
    match flag with
    | N => { pstate with n := val }
    | Z => { pstate with z := val }
    | C => { pstate with c := val }
    | V => { pstate with v := val }
  { s with pstate := new_pstate }

def fetch_inst (addr : BitVec 64) (s : ArmState) : Option (BitVec 32) :=
  s.program.find? addr

def read_base_error (s : ArmState) : StateError :=
  s.error

def write_base_error (val : StateError) (s : ArmState) : ArmState :=
  { s with error := val }

----------------------------------------------------------------------
-- StateField and r/w functions
----------------------------------------------------------------------

section Accessor_updater_functions

open BitVec

inductive StateField where
  | GPR    : BitVec 5 → StateField
  | SFP    : BitVec 5 → StateField
  | PC     : StateField
  | FLAG   : PFlag → StateField
  | ERR    : StateField
deriving DecidableEq, Repr

def state_value (fld : StateField) : Type :=
  open StateField in
  match fld with
  | GPR _   => BitVec 64
  | SFP _   => BitVec 128
  | PC      => BitVec 64
  | FLAG _  => BitVec 1
  | ERR     => StateError

def r (fld : StateField) (s : ArmState) : (state_value fld) :=
  open StateField in
  match fld with
  | GPR i   => read_base_gpr i s
  | SFP i   => read_base_sfp i s
  | PC      => read_base_pc s
  | FLAG i  => read_base_flag i s
  | ERR     => read_base_error s

def w (fld : StateField) (v : (state_value fld)) (s : ArmState) : ArmState :=
  open StateField in
  match fld with
  | GPR i  => write_base_gpr i v s
  | SFP i  => write_base_sfp i v s
  | PC     => write_base_pc v s
  | FLAG i => write_base_flag i v s
  | ERR    => write_base_error v s

def read_gpr (width : Nat) (idx : BitVec 5) (s : ArmState)
  : BitVec width :=
    let val := r (StateField.GPR idx) s
    BitVec.zeroExtend width val

def write_gpr (width : Nat) (idx : BitVec 5) (val : BitVec width) (s : ArmState)
  : ArmState :=
    let val := BitVec.zeroExtend 64 val
    w (StateField.GPR idx) val s

def read_sfp (width : Nat) (idx : BitVec 5) (s : ArmState) : BitVec width :=
  let val := r (StateField.SFP idx) s
  BitVec.zeroExtend width val

def write_sfp (n : Nat) (idx : BitVec 5) (val : BitVec n) (s : ArmState) : ArmState :=
   let val := BitVec.zeroExtend 128 val
   w (StateField.SFP idx) val s

def read_pc (s : ArmState) : BitVec 64 :=
  r StateField.PC s

def write_pc (v : BitVec 64) (s : ArmState) : ArmState :=
  w StateField.PC v s

def read_flag (flag : PFlag) (s : ArmState) : BitVec 1 :=
  r (StateField.FLAG flag) s

def write_flag (flag : PFlag) (val : BitVec 1) (s : ArmState) : ArmState :=
  w (StateField.FLAG flag) val s

def read_err (s : ArmState) : StateError :=
  r StateField.ERR s

def write_err (v : StateError) (s : ArmState) : ArmState :=
  w StateField.ERR v s

def make_pstate (n z c v : BitVec 1) : PState :=
  { n, z, c, v }

def zero_pstate : PState :=
  { n := 0#1, z := 0#1, c := 0#1, v := 0#1 }

end Accessor_updater_functions

----------------------------------------------------------------------
-- Program loading
----------------------------------------------------------------------

def def_program (p : Program) : Program :=
  p

end State

----------------------------------------------------------------------
-- Memory (from Arm/Memory.lean)
----------------------------------------------------------------------

section Memory

open BitVec

def read_mem (addr : BitVec 64) (s : ArmState) : BitVec 8 :=
  read_store addr s.mem

def read_mem_bytes (n : Nat) (addr : BitVec 64) (s : ArmState) : BitVec (n * 8) :=
  match n with
  | 0 => 0#0
  | n' + 1 =>
    let byte := read_mem addr s
    let rest := read_mem_bytes n' (addr + 1#64) s
    have h: n' * 8 + 8 = (n' + 1) * 8 := by omega
    BitVec.cast h (rest ++ byte)

def write_mem (addr : BitVec 64) (val : BitVec 8) (s : ArmState) : ArmState :=
  let new_mem := write_store addr val s.mem
  { s with mem := new_mem }

def write_mem_bytes (n : Nat) (addr : BitVec 64) (val : BitVec (n * 8)) (s : ArmState) : ArmState :=
  match n with
  | 0 => s
  | n' + 1 =>
    let byte := extractLsb 7 0 val
    let s := write_mem addr byte s
    let val_rest := BitVec.zeroExtend (n' * 8) (val >>> 8)
    write_mem_bytes n' (addr + 1#64) val_rest s

end Memory

----------------------------------------------------------------------
-- Decode types: DPI (from Arm/Decode/DPI.lean)
----------------------------------------------------------------------

section Decode

open BitVec

structure Add_sub_imm_cls where
  sf     : BitVec 1
  op     : BitVec 1
  S      : BitVec 1
  _fixed : BitVec 6 := 0b100010#6
  sh     : BitVec 1
  imm12  : BitVec 12
  Rn     : BitVec 5
  Rd     : BitVec 5
deriving DecidableEq, Repr

structure Logical_imm_cls where
  sf     : BitVec 1
  opc    : BitVec 2
  _fixed : BitVec 6 := 0b100100#6
  N      : BitVec 1
  immr   : BitVec 6
  imms   : BitVec 6
  Rn     : BitVec 5
  Rd     : BitVec 5
deriving DecidableEq, Repr

structure PC_rel_addressing_cls where
  op     : BitVec 1
  immlo  : BitVec 2
  _fixed : BitVec 5 := 0b10000#5
  immhi  : BitVec 19
  Rd     : BitVec 5
deriving DecidableEq, Repr

structure Bitfield_cls where
  sf     : BitVec 1
  opc    : BitVec 2
  _fixed : BitVec 6 := 0b100110#6
  N      : BitVec 1
  immr   : BitVec 6
  imms   : BitVec 6
  Rn     : BitVec 5
  Rd     : BitVec 5
deriving DecidableEq, Repr

structure Move_wide_imm_cls where
  sf     : BitVec 1
  opc    : BitVec 2
  _fixed : BitVec 6 := 0b100101#6
  hw     : BitVec 2
  imm16  : BitVec 16
  Rd     : BitVec 5
deriving DecidableEq, Repr

inductive DataProcImmInst where
  | Add_sub_imm       : Add_sub_imm_cls → DataProcImmInst
  | Logical_imm       : Logical_imm_cls → DataProcImmInst
  | PC_rel_addressing : PC_rel_addressing_cls → DataProcImmInst
  | Bitfield           : Bitfield_cls → DataProcImmInst
  | Move_wide_imm      : Move_wide_imm_cls → DataProcImmInst
deriving DecidableEq, Repr

----------------------------------------------------------------------
-- Decode types: BR (from Arm/Decode/BR.lean)
----------------------------------------------------------------------

structure Compare_branch_cls where
  sf     : BitVec 1
  _fixed : BitVec 5 := 0b011010#5
  op     : BitVec 1
  imm19  : BitVec 19
  Rt     : BitVec 5
deriving DecidableEq, Repr

structure Uncond_branch_imm_cls where
  op     : BitVec 1
  _fixed : BitVec 5 := 0b00101#5
  imm26  : BitVec 26
deriving DecidableEq, Repr

structure Uncond_branch_reg_cls where
  _fixed : BitVec 7 := 0b1101011#7
  opc    : BitVec 4
  op2    : BitVec 5
  op3    : BitVec 6
  Rn     : BitVec 5
  op4    : BitVec 5
deriving DecidableEq, Repr

structure Cond_branch_imm_cls where
  _fixed : BitVec 8 := 0b01010100#8
  imm19  : BitVec 19
  o0     : BitVec 1
  cond   : BitVec 4
deriving DecidableEq, Repr

structure Hints_cls where
  _fixed1 : BitVec 20 := 0b11010101000000110010#20
  CRm     : BitVec 4
  op2     : BitVec 3
  _fixed2 : BitVec 5 := 0b11111#5
deriving DecidableEq, Repr

inductive BranchInst where
  | Compare_branch      : Compare_branch_cls → BranchInst
  | Uncond_branch_imm   : Uncond_branch_imm_cls → BranchInst
  | Uncond_branch_reg   : Uncond_branch_reg_cls → BranchInst
  | Cond_branch_imm     : Cond_branch_imm_cls → BranchInst
  | Hints               : Hints_cls → BranchInst
deriving DecidableEq, Repr

----------------------------------------------------------------------
-- Decode types: DPR (from Arm/Decode/DPR.lean)
----------------------------------------------------------------------

structure Add_sub_carry_cls where
  sf      : BitVec 1
  op      : BitVec 1
  S       : BitVec 1
  _fixed1 : BitVec 8 := 0b11010000#8
  Rm      : BitVec 5
  _fixed2 : BitVec 6 := 0b000000#6
  Rn      : BitVec 5
  Rd      : BitVec 5
deriving DecidableEq, Repr

structure Add_sub_shifted_reg_cls where
  sf      : BitVec 1
  op      : BitVec 1
  S       : BitVec 1
  _fixed1 : BitVec 5 := 0b01011#5
  shift   : BitVec 2
  _fixed2 : BitVec 1 := 0
  Rm      : BitVec 5
  imm6    : BitVec 6
  Rn      : BitVec 5
  Rd      : BitVec 5
deriving DecidableEq, Repr

structure Conditional_select_cls where
  sf     : BitVec 1
  op     : BitVec 1
  S      : BitVec 1
  _fixed : BitVec 8 := 0b11010100#8
  Rm     : BitVec 5
  cond   : BitVec 4
  op2    : BitVec 2
  Rn     : BitVec 5
  Rd     : BitVec 5
deriving DecidableEq, Repr

structure Data_processing_one_source_cls where
  sf      : BitVec 1
  _fixed1 : BitVec 1 := 0b1#1
  S       : BitVec 1
  _fixed2 : BitVec 8 := 0b11010110#8
  opcode2 : BitVec 5
  opcode  : BitVec 6
  Rn      : BitVec 5
  Rd      : BitVec 5
deriving DecidableEq, Repr

structure Data_processing_two_source_cls where
  sf      : BitVec 1
  _fixed1 : BitVec 1 := 0b0#1
  S       : BitVec 1
  _fixed2 : BitVec 8 := 0b11010110#8
  Rm      : BitVec 5
  opcode  : BitVec 6
  Rn      : BitVec 5
  Rd      : BitVec 5
deriving DecidableEq, Repr

structure Logical_shifted_reg_cls where
  sf     : BitVec 1
  opc    : BitVec 2
  _fixed : BitVec 5 := 0b01010#5
  shift  : BitVec 2
  N      : BitVec 1
  Rm     : BitVec 5
  imm6   : BitVec 6
  Rn     : BitVec 5
  Rd     : BitVec 5
deriving DecidableEq, Repr

inductive DataProcRegInst where
  | Add_sub_carry              : Add_sub_carry_cls → DataProcRegInst
  | Add_sub_shifted_reg        : Add_sub_shifted_reg_cls → DataProcRegInst
  | Conditional_select         : Conditional_select_cls → DataProcRegInst
  | Data_processing_one_source : Data_processing_one_source_cls → DataProcRegInst
  | Data_processing_two_source : Data_processing_two_source_cls → DataProcRegInst
  | Logical_shifted_reg        : Logical_shifted_reg_cls → DataProcRegInst
deriving DecidableEq, Repr

----------------------------------------------------------------------
-- Decode types: DPSFP (from Arm/Decode/DPSFP.lean)
----------------------------------------------------------------------

structure Crypto_aes_cls where
  _fixed1 : BitVec 8 := 0b01001110#8
  size    : BitVec 2
  _fixed2 : BitVec 5 := 0b10100#5
  opcode  : BitVec 5
  _fixed3 : BitVec 2 := 0b10#2
  Rn      : BitVec 5
  Rd      : BitVec 5
deriving DecidableEq, Repr

structure Crypto_three_reg_sha512_cls where
  _fixed1 : BitVec 11 := 0b11001110011#11
  Rm      : BitVec 5
  _fixed2 : BitVec 1 := 0b1#1
  O       : BitVec 1
  _fixed3 : BitVec 2 := 0b00#2
  opcode  : BitVec 2
  Rn      : BitVec 5
  Rd      : BitVec 5
deriving DecidableEq, Repr

structure Crypto_two_reg_sha512_cls where
  _fixed : BitVec 20 := 0b11001110110000001000#20
  opcode: BitVec 2
  Rn    : BitVec 5
  Rd    : BitVec 5
deriving DecidableEq, Repr

structure Crypto_four_reg_cls where
  _fixed1 : BitVec 9 := 0b110011100#9
  Op0     : BitVec 2
  Rm      : BitVec 5
  _fixed2 : BitVec 1 := 0b0#1
  Ra      : BitVec 5
  Rn      : BitVec 5
  Rd      : BitVec 5
deriving DecidableEq, Repr

structure Advanced_simd_two_reg_misc_cls where
  _fixed1 : BitVec 1 := 0b0#1
  Q       : BitVec 1
  U       : BitVec 1
  _fixed2 : BitVec 5 := 0b01110#5
  size    : BitVec 2
  _fixed3 : BitVec 5 := 0b10000#5
  opcode  : BitVec 5
  _fixed4 : BitVec 2 := 0b10#2
  Rn      : BitVec 5
  Rd      : BitVec 5
deriving DecidableEq, Repr

structure Advanced_simd_copy_cls where
  _fixed1 : BitVec 1 := 0b0#1
  Q       : BitVec 1
  op      : BitVec 1
  _fixed2 : BitVec 8 := 0b01110000#8
  imm5    : BitVec 5
  _fixed3 : BitVec 1 := 0b0#1
  imm4    : BitVec 4
  _fixed4 : BitVec 1 := 0b1#1
  Rn      : BitVec 5
  Rd      : BitVec 5
deriving DecidableEq, Repr

structure Advanced_simd_scalar_copy_cls where
  _fixed1 : BitVec 2 := 0b01#2
  op      : BitVec 1
  _fixed2 : BitVec 8 := 0b11110000#8
  imm5    : BitVec 5
  _fixed3 : BitVec 1 := 0b0#1
  imm4    : BitVec 4
  _fixed4 : BitVec 1 := 0b1#1
  Rn      : BitVec 5
  Rd      : BitVec 5
deriving DecidableEq, Repr

structure Advanced_simd_extract_cls where
  _fixed1 : BitVec 1 := 0b0#1
  Q       : BitVec 1
  _fixed2 : BitVec 6 := 0b101110#6
  op2     : BitVec 2
  _fixed3 : BitVec 1 := 0b0#1
  Rm      : BitVec 5
  _fixed4 : BitVec 1 := 0b0#1
  imm4    : BitVec 4
  _fixed5 : BitVec 1 := 0b0#1
  Rn      : BitVec 5
  Rd      : BitVec 5
deriving DecidableEq, Repr

structure Advanced_simd_permute_cls where
  _fixed1 : BitVec 1 := 0b0#1
  Q       : BitVec 1
  _fixed2 : BitVec 6 := 0b001110#6
  size    : BitVec 2
  _fixed3 : BitVec 1 := 0b0#1
  Rm      : BitVec 5
  _fixed4 : BitVec 1 := 0b0#1
  opcode  : BitVec 3
  _fixed5 : BitVec 2 := 0b10#2
  Rn      : BitVec 5
  Rd      : BitVec 5
deriving DecidableEq, Repr

structure Advanced_simd_modified_immediate_cls where
  _fixed1 : BitVec 1 := 0b0#1
  Q       : BitVec 1
  op      : BitVec 1
  _fixed2 : BitVec 10 := 0b0111100000#10
  a       : BitVec 1
  b       : BitVec 1
  c       : BitVec 1
  cmode   : BitVec 4
  o2      : BitVec 1
  _fixed3 : BitVec 1 := 0b1#1
  d       : BitVec 1
  e       : BitVec 1
  f       : BitVec 1
  g       : BitVec 1
  h       : BitVec 1
  Rd      : BitVec 5
deriving DecidableEq, Repr

structure Advanced_simd_shift_by_immediate_cls where
  _fixed1 : BitVec 1 := 0b0#1
  Q       : BitVec 1
  U       : BitVec 1
  _fixed2 : BitVec 6 := 0b011110#6
  immh    : BitVec 4
  immb    : BitVec 3
  opcode  : BitVec 5
  _fixed3 : BitVec 1 := 0b1#1
  Rn      : BitVec 5
  Rd      : BitVec 5
deriving DecidableEq, Repr

structure Advanced_simd_scalar_shift_by_immediate_cls where
  _fixed1 : BitVec 2 := 0b01#2
  U       : BitVec 1
  _fixed2 : BitVec 6 := 0b111110#6
  immh    : BitVec 4
  immb    : BitVec 3
  opcode  : BitVec 5
  _fixed3 : BitVec 1 := 0b1#1
  Rn      : BitVec 5
  Rd      : BitVec 5
deriving DecidableEq, Repr

structure Advanced_simd_table_lookup_cls where
  _fixed1 : BitVec 1 := 0b0#1
  Q       : BitVec 1
  _fixed2 : BitVec 6 := 0b001110#6
  op2     : BitVec 2
  _fixed3 : BitVec 1 := 0b0#1
  Rm      : BitVec 5
  _fixed4 : BitVec 1 := 0b0#1
  len     : BitVec 2
  op      : BitVec 1
  _fixed5 : BitVec 2 := 0b00#2
  Rn      : BitVec 5
  Rd      : BitVec 5
deriving DecidableEq, Repr

structure Advanced_simd_three_same_cls where
  _fixed1 : BitVec 1 := 0b0#1
  Q       : BitVec 1
  U       : BitVec 1
  _fixed2 : BitVec 5 := 0b01110#5
  size    : BitVec 2
  _fixed3 : BitVec 1 := 0b1#1
  Rm      : BitVec 5
  opcode  : BitVec 5
  _fixed4 : BitVec 1 := 0b1#1
  Rn      : BitVec 5
  Rd      : BitVec 5
deriving DecidableEq, Repr

structure Advanced_simd_three_different_cls where
  _fixed1 : BitVec 1 := 0b0#1
  Q       : BitVec 1
  U       : BitVec 1
  _fixed2 : BitVec 5 := 0b01110#5
  size    : BitVec 2
  _fixed3 : BitVec 1 := 0b1#1
  Rm      : BitVec 5
  opcode  : BitVec 4
  _fixed4 : BitVec 2 := 0b00#2
  Rn      : BitVec 5
  Rd      : BitVec 5
deriving DecidableEq, Repr

structure Conversion_between_FP_and_Int_cls where
  sf      : BitVec 1
  _fixed1 : BitVec 1 := 0b0#1
  S       : BitVec 1
  _fixed2 : BitVec 5 := 0b11110#5
  ftype   : BitVec 2
  _fixed3 : BitVec 1 := 0b1#1
  rmode   : BitVec 2
  opcode  : BitVec 3
  _fixed4 : BitVec 6 := 0b000000#6
  Rn      : BitVec 5
  Rd      : BitVec 5
deriving DecidableEq, Repr

inductive DataProcSFPInst where
  | Crypto_aes                              : Crypto_aes_cls → DataProcSFPInst
  | Crypto_two_reg_sha512                   : Crypto_two_reg_sha512_cls → DataProcSFPInst
  | Crypto_three_reg_sha512                 : Crypto_three_reg_sha512_cls → DataProcSFPInst
  | Crypto_four_reg                         : Crypto_four_reg_cls → DataProcSFPInst
  | Advanced_simd_two_reg_misc              : Advanced_simd_two_reg_misc_cls → DataProcSFPInst
  | Advanced_simd_copy                      : Advanced_simd_copy_cls → DataProcSFPInst
  | Advanced_simd_extract                   : Advanced_simd_extract_cls → DataProcSFPInst
  | Advanced_simd_permute                   : Advanced_simd_permute_cls → DataProcSFPInst
  | Advanced_simd_modified_immediate        : Advanced_simd_modified_immediate_cls → DataProcSFPInst
  | Advanced_simd_shift_by_immediate        : Advanced_simd_shift_by_immediate_cls → DataProcSFPInst
  | Advanced_simd_scalar_shift_by_immediate : Advanced_simd_scalar_shift_by_immediate_cls → DataProcSFPInst
  | Advanced_simd_scalar_copy               : Advanced_simd_scalar_copy_cls → DataProcSFPInst
  | Advanced_simd_table_lookup              : Advanced_simd_table_lookup_cls → DataProcSFPInst
  | Advanced_simd_three_same                : Advanced_simd_three_same_cls → DataProcSFPInst
  | Advanced_simd_three_different           : Advanced_simd_three_different_cls → DataProcSFPInst
  | Conversion_between_FP_and_Int           : Conversion_between_FP_and_Int_cls → DataProcSFPInst
deriving DecidableEq, Repr

----------------------------------------------------------------------
-- Decode types: LDST (from Arm/Decode/LDST.lean)
----------------------------------------------------------------------

structure Reg_imm_post_indexed_cls where
  size    : BitVec 2
  _fixed1 : BitVec 3 := 0b111#3
  V       : BitVec 1
  _fixed2 : BitVec 2 := 0b00#2
  opc     : BitVec 2
  _fixed3 : BitVec 1 := 0b0#1
  imm9    : BitVec 9
  _fixed4 : BitVec 2 := 0b01#2
  Rn      : BitVec 5
  Rt      : BitVec 5
deriving DecidableEq, Repr

instance : ToString Reg_imm_post_indexed_cls where toString a := toString (repr a)

structure Reg_unsigned_imm_cls where
  size    : BitVec 2
  _fixed1 : BitVec 3 := 0b111#3
  V       : BitVec 1
  _fixed2 : BitVec 2 := 0b01#2
  opc     : BitVec 2
  imm12   : BitVec 12
  Rn      : BitVec 5
  Rt      : BitVec 5
deriving DecidableEq, Repr

instance : ToString Reg_unsigned_imm_cls where toString a := toString (repr a)

structure Reg_unscaled_imm_cls where
  size    : BitVec 2
  _fixed1 : BitVec 3 := 0b111#3
  VR      : BitVec 1
  _fixed2 : BitVec 2 := 0b00#2
  opc     : BitVec 2
  _fixed3 : BitVec 1 := 0b0#1
  imm9    : BitVec 9
  _fixed4 : BitVec 2 := 0b00#2
  Rn      : BitVec 5
  Rt      : BitVec 5
deriving DecidableEq, Repr

instance : ToString Reg_unscaled_imm_cls where toString a := toString (repr a)

structure Reg_pair_pre_indexed_cls where
  opc     : BitVec 2
  _fixed1 : BitVec 3 := 0b101#3
  V       : BitVec 1
  _fixed2 : BitVec 3 := 0b011#3
  L       : BitVec 1
  imm7    : BitVec 7
  Rt2     : BitVec 5
  Rn      : BitVec 5
  Rt      : BitVec 5
deriving DecidableEq, Repr

instance : ToString Reg_pair_pre_indexed_cls where toString a := toString (repr a)

structure Reg_pair_post_indexed_cls where
  opc     : BitVec 2
  _fixed1 : BitVec 3 := 0b101#3
  V       : BitVec 1
  _fixed2 : BitVec 3 := 0b001#3
  L       : BitVec 1
  imm7    : BitVec 7
  Rt2     : BitVec 5
  Rn      : BitVec 5
  Rt      : BitVec 5
deriving DecidableEq, Repr

instance : ToString Reg_pair_post_indexed_cls where toString a := toString (repr a)

structure Reg_pair_signed_offset_cls where
  opc     : BitVec 2
  _fixed1 : BitVec 3 := 0b101#3
  V       : BitVec 1
  _fixed2 : BitVec 3 := 0b010#3
  L       : BitVec 1
  imm7    : BitVec 7
  Rt2     : BitVec 5
  Rn      : BitVec 5
  Rt      : BitVec 5
deriving DecidableEq, Repr

instance : ToString Reg_pair_signed_offset_cls where toString a := toString (repr a)

structure Advanced_simd_multiple_struct_cls where
  _fixed1 : BitVec 1 := 0b0#1
  Q       : BitVec 1
  _fixed2 : BitVec 7 := 0b0011000#7
  L       : BitVec 1
  _fixed3 : BitVec 6 := 0b000000#6
  opcode  : BitVec 4
  size    : BitVec 2
  Rn      : BitVec 5
  Rt      : BitVec 5
deriving DecidableEq, Repr

instance : ToString Advanced_simd_multiple_struct_cls where toString a := toString (repr a)

structure Advanced_simd_multiple_struct_post_indexed_cls where
  _fixed1 : BitVec 1 := 0b0#1
  Q       : BitVec 1
  _fixed2 : BitVec 7 := 0b0011001#7
  L       : BitVec 1
  _fixed3 : BitVec 1 := 0b0#1
  Rm      : BitVec 5
  opcode  : BitVec 4
  size    : BitVec 2
  Rn      : BitVec 5
  Rt      : BitVec 5
deriving DecidableEq, Repr

instance : ToString Advanced_simd_multiple_struct_post_indexed_cls where toString a := toString (repr a)

inductive LDSTInst where
  | Reg_imm_post_indexed :
    Reg_imm_post_indexed_cls → LDSTInst
  | Reg_unsigned_imm :
    Reg_unsigned_imm_cls → LDSTInst
  | Reg_unscaled_imm :
    Reg_unscaled_imm_cls  → LDSTInst
  | Reg_pair_pre_indexed :
    Reg_pair_pre_indexed_cls → LDSTInst
  | Reg_pair_post_indexed :
    Reg_pair_post_indexed_cls → LDSTInst
  | Reg_pair_signed_offset :
    Reg_pair_signed_offset_cls → LDSTInst
  | Advanced_simd_multiple_struct :
    Advanced_simd_multiple_struct_cls → LDSTInst
  | Advanced_simd_multiple_struct_post_indexed :
    Advanced_simd_multiple_struct_post_indexed_cls → LDSTInst
deriving DecidableEq, Repr

----------------------------------------------------------------------
-- ArmInst (from Arm/Decode.lean)
----------------------------------------------------------------------

inductive ArmInst where
  | DPI   : DataProcImmInst → ArmInst
  | BR    : BranchInst      → ArmInst
  | DPR   : DataProcRegInst → ArmInst
  | DPSFP : DataProcSFPInst → ArmInst
  | LDST  : LDSTInst        → ArmInst
deriving DecidableEq, Repr

----------------------------------------------------------------------
-- Decode functions (from Arm/Decode.lean)
-- Non-LDST decoders are stubbed since those instructions won't appear
----------------------------------------------------------------------

def decode_data_proc_imm (_i : BitVec 32) : Option ArmInst := none
def decode_branch (_i : BitVec 32) : Option ArmInst := none
def decode_data_proc_reg (_i : BitVec 32) : Option ArmInst := none
def decode_data_proc_sfp (_i : BitVec 32) : Option ArmInst := none

-- Full LDST decode (from Arm/Decode.lean)
def decode_ldst_inst (i : BitVec 32) : Option ArmInst :=
  open ArmInst in
  open LDSTInst in
  match_bv i with
  | [size:2, 111, V:1, 00, opc:2, 0, imm9:9, 01, Rn:5, Rt:5] =>
    LDST (Reg_imm_post_indexed {size, V, opc, imm9, Rn, Rt})
  | [size:2, 111, V:1, 01, opc:2, imm12:12, Rn:5, Rt:5] =>
    LDST (Reg_unsigned_imm {size, V, opc, imm12, Rn, Rt})
  | [size:2, 111, VR:1, 00, opc:2, 0, imm9:9, 00, Rn:5, Rt:5] =>
    LDST (Reg_unscaled_imm {size, VR, opc, imm9, Rn, Rt})
  | [opc:2, 101, V:1, 011, L:1, imm7:7, Rt2:5, Rn:5, Rt:5] =>
    LDST (Reg_pair_pre_indexed {opc, V, L, imm7, Rt2, Rn, Rt})
  | [opc:2, 101, V:1, 001, L:1, imm7:7, Rt2:5, Rn:5, Rt:5] =>
    LDST (Reg_pair_post_indexed {opc, V, L, imm7, Rt2, Rn, Rt})
  | [opc:2, 101, V:1, 010, L:1, imm7:7, Rt2:5, Rn:5, Rt:5] =>
    LDST (Reg_pair_signed_offset {opc, V, L, imm7, Rt2, Rn, Rt})
  | [0, Q:1, 0011000, L:1, 000000, opcode:4, size:2, Rn:5, Rt:5] =>
    LDST (Advanced_simd_multiple_struct {Q, L, opcode, size, Rn, Rt})
  | [0, Q:1, 0011001, L:1, 0, Rm:5, opcode:4, size:2, Rn:5, Rt:5] =>
    LDST (Advanced_simd_multiple_struct_post_indexed {Q, L, Rm, opcode, size, Rn, Rt})
  | _ => none

-- Top-level decode (from Arm/Decode.lean)
def decode_raw_inst (i : BitVec 32) : Option ArmInst :=
  open ArmInst in
  match_bv i with
  | [op0:1, _x:2, op1:4, _y:25] =>
    match op0, op1 with
    | _, 0b1000#4 | _, 0b1001#4 => decode_data_proc_imm i
    | _, 0b1010#4 | _, 0b1011#4 => decode_branch i
    | _, 0b1101#4 | _, 0b0101#4 => decode_data_proc_reg i
    | _, 0b0111#4 | _, 0b1111#4 => decode_data_proc_sfp i
    | _, 0b0100#4 | _, 0b1100#4 | _, 0b0110#4 | _, 0b1110#4 => decode_ldst_inst i
    | _, _ => none
  | _ => none

end Decode

----------------------------------------------------------------------
-- Common LDST helpers (from Arm/Insts/Common.lean)
----------------------------------------------------------------------

section Common

open BitVec

inductive MemOp where
  | MemOp_LOAD : MemOp
  | MemOp_STORE : MemOp
  | MemOp_PREFETCH : MemOp
deriving DecidableEq, Repr

def CheckSPAlignment (s : ArmState) : Bool :=
  let sp := read_gpr 64 31#5 s
  ((extractLsb 3 0 sp) &&& 0xF#4) = 0#4

def ldst_read (SIMD? : Bool) (width : Nat) (idx : BitVec 5) (s : ArmState)
  : BitVec width :=
  if SIMD? then read_sfp width idx s else read_gpr width idx s

def ldst_write (SIMD? : Bool) (width : Nat) (idx : BitVec 5) (val : BitVec width) (s : ArmState)
  : ArmState :=
  if SIMD? then write_sfp width idx val s else write_gpr width idx val s

end Common

----------------------------------------------------------------------
-- LDST Reg_imm implementation (from Arm/Insts/LDST/Reg_imm.lean)
----------------------------------------------------------------------

namespace LDST

open BitVec

structure Reg_imm_cls where
  size      : BitVec 2
  opc       : BitVec 2
  Rn        : BitVec 5
  Rt        : BitVec 5
  SIMD?     : Bool
  wback     : Bool
  postindex : Bool
  imm       : BitVec 12 ⊕ (BitVec 9)
deriving DecidableEq, Repr

instance : ToString Reg_imm_cls where toString a := toString (repr a)

def reg_imm_operation (inst_str : String) (op : BitVec 1)
  (wback : Bool) (postindex : Bool) (SIMD? : Bool)
  (datasize : Nat) (regsize : Option Nat) (Rn : BitVec 5)
  (Rt : BitVec 5) (offset : BitVec 64) (s : ArmState)
  (H : 8 ∣ datasize) : ArmState :=
  let address := read_gpr 64 Rn s
  if Rn = 31#5 ∧ not (CheckSPAlignment s) then
      write_err (StateError.Fault s!"[Inst: {inst_str}] SP {address} is not aligned!") s
  else
    let address := if postindex then address else address + offset
    have h : datasize / 8 * 8 = datasize := by
      exact Nat.div_mul_cancel H
    let s :=
      match op with
      | 0#1 => -- STORE
        let data := ldst_read SIMD? datasize Rt s
        write_mem_bytes (datasize / 8) address (h.symm ▸ data) s
      | _ => -- LOAD
        let data := read_mem_bytes (datasize / 8) address s
        if SIMD? then write_sfp datasize Rt (h.symm ▸ data) s
        else write_gpr regsize.get! Rt (zeroExtend regsize.get! data) s
    if wback then
      let address := if postindex then address + offset else address
      write_gpr 64 Rn address s
    else
      s

def reg_imm_constrain_unpredictable (wback : Bool) (SIMD? : Bool) (Rn : BitVec 5)
  (Rt : BitVec 5) : Bool :=
  if SIMD? then false else wback ∧ Rn = Rt ∧ Rn ≠ 31#5

def supported_reg_imm (size : BitVec 2) (opc : BitVec 2) (SIMD? : Bool) : Bool :=
  match size, opc, SIMD? with
  | 0b00#2, 0b00#2, false => true -- STRB, 32-bit, GPR
  | 0b00#2, 0b01#2, false => true -- LDRB, 32-bit, GPR
  | 0b10#2, 0b00#2, false => true -- STR, 32-bit, GPR
  | 0b10#2, 0b01#2, false => true -- LDR, 32-bit, GPR
  | 0b11#2, 0b00#2, false => true -- STR, 64-bit, GPR
  | 0b11#2, 0b01#2, false => true -- LDR, 64-bit, GPR
  | _, 0b00#2, true => true      -- STR, 8-bit, 16-bit, 32-bit, 64-bit, SIMD&FP
  | _, 0b01#2, true => true      -- LDR, 8-bit, 16-bit, 32-bit, 64-bit, SIMD&FP
  | 0b00#2, 0b10#2, true => true -- STR, 128-bit, SIMD&FP
  | 0b00#2, 0b11#2, true => true -- LDR, 128-bit, SIMD&FP
  | _, _, _ => false

def exec_reg_imm_common
  (inst : Reg_imm_cls) (inst_str : String) (s : ArmState) : ArmState :=
  let scale :=
    if inst.SIMD? then ((lsb inst.opc 1) ++ inst.size).toNat
    else inst.size.toNat
  if not $ supported_reg_imm inst.size inst.opc inst.SIMD? then
    write_err (StateError.Unimplemented "Unsupported instruction {inst_str} encountered!") s
  else if inst.SIMD? ∧ scale > 4 then
    write_err (StateError.Illegal "Illegal instruction {inst_str} encountered!") s
  else if reg_imm_constrain_unpredictable inst.wback inst.SIMD? inst.Rn inst.Rt then
    write_err (StateError.Illegal "Illegal instruction {inst_str} encountered!") s
  else
    let offset := match inst.imm with
      | Sum.inl imm12 => (BitVec.zeroExtend 64 imm12) <<< scale
      | Sum.inr imm9 => signExtend 64 imm9
    let datasize := 8 <<< scale
    let regsize :=
      if inst.SIMD? then none
      else if inst.size = 0b11#2 then some 64 else some 32
    have H : 8 ∣ datasize := by
      simp_all! only [Nat.shiftLeft_eq, Nat.dvd_mul_right, datasize]
    let s' := reg_imm_operation inst_str
              (lsb inst.opc 0) inst.wback inst.postindex
              inst.SIMD? datasize regsize inst.Rn inst.Rt offset s (H)
    let s' := write_pc ((read_pc s) + 4#64) s'
    s'

def exec_reg_imm_unsigned_offset
  (inst : Reg_unsigned_imm_cls) (s : ArmState) : ArmState :=
  let extracted_inst : Reg_imm_cls :=
    { size      := inst.size,
      opc       := inst.opc,
      Rn        := inst.Rn,
      Rt        := inst.Rt,
      SIMD?     := inst.V = 1#1,
      wback     := false,
      postindex := false,
      imm       := Sum.inl inst.imm12 }
  exec_reg_imm_common extracted_inst s!"{inst}" s

def exec_reg_imm_post_indexed
  (inst : Reg_imm_post_indexed_cls) (s : ArmState) : ArmState :=
  let extracted_inst : Reg_imm_cls :=
    { size      := inst.size,
      opc       := inst.opc,
      Rn        := inst.Rn,
      Rt        := inst.Rt,
      SIMD?     := inst.V = 1#1,
      wback     := true,
      postindex := true,
      imm       := Sum.inr inst.imm9 }
  exec_reg_imm_common extracted_inst s!"{inst}" s

----------------------------------------------------------------------
-- LDST Reg_unscaled_imm implementation (from Arm/Insts/LDST/Reg_unscaled_imm.lean)
----------------------------------------------------------------------

def exec_ldstur
  (inst : Reg_unscaled_imm_cls) (s : ArmState) : ArmState :=
  let scale := (extractLsb 1 1 inst.opc ++ inst.size).toNat
  if scale > 4 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let offset := signExtend 64 inst.imm9
    let memop := if getLsb inst.opc 0 then MemOp.MemOp_LOAD else MemOp.MemOp_STORE
    let datasize := 8 <<< scale
    let address := read_gpr 64 inst.Rn s
    if inst.Rn = 31#5 ∧ not (CheckSPAlignment s) then
      write_err (StateError.Fault s!"[Inst: {inst}] SP {address} is not aligned!") s
    else
      let address := address + offset
      let s := if memop = MemOp.MemOp_STORE then
                 have h : datasize = datasize / 8 * 8 := by omega
                 let data := read_sfp datasize inst.Rt s
                 write_mem_bytes (datasize / 8) address (h ▸ data) s
               else
                 have h : datasize / 8 * 8 = datasize := by omega
                 let data := read_mem_bytes (datasize / 8) address s
                 write_sfp datasize inst.Rt (h ▸ data) s
      let s := write_pc ((read_pc s) + 4#64) s
      s

def exec_reg_unscaled_imm
  (inst : Reg_unscaled_imm_cls) (s : ArmState) : ArmState :=
  if inst.VR = 0b1#1 then
    exec_ldstur inst s
  else
    write_err (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!") s

----------------------------------------------------------------------
-- LDST Reg_pair implementation (from Arm/Insts/LDST/Reg_pair.lean)
----------------------------------------------------------------------

structure Reg_pair_cls where
  opc       : BitVec 2
  SIMD?     : Bool
  L?        : Bool
  wback     : Bool
  postindex : Bool
  imm7      : BitVec 7
  Rt2       : BitVec 5
  Rn        : BitVec 5
  Rt        : BitVec 5
deriving DecidableEq, Repr

instance : ToString Reg_pair_cls where toString a := toString (repr a)

def reg_pair_constrain_unpredictable (wback : Bool) (inst : Reg_pair_cls) : Bool :=
  match inst.SIMD?, inst.L? with
  | false, false => wback ∧ ((inst.Rt = inst.Rn) ∨ inst.Rt2 = inst.Rn) ∧ inst.Rn ≠ 31#5
  | false, true => (wback ∧ ((inst.Rt = inst.Rn) ∨ inst.Rt2 = inst.Rn) ∧ inst.Rn ≠ 31#5)
                ∨ (inst.Rt = inst.Rt2)
  | true, false => false
  | true, true => inst.Rt = inst.Rt2

def zero_lt_shift_left_pos {x n : Nat} (h : 0 < x) :
  0 < x <<< n := by
  simp_all only [Nat.shiftLeft_eq, Nat.zero_lt_succ,
  Nat.pow_pos, Nat.mul_pos_iff_of_pos_left]
  done

def reg_pair_operation (inst : Reg_pair_cls) (inst_str : String) (signed : Bool)
  (datasize : Nat) (offset : BitVec 64) (s : ArmState)
  (H1 : 8 ∣ datasize) (H2 : 0 < datasize) : ArmState :=
  let address := read_gpr 64 inst.Rn s
  if inst.Rn = 31#5 ∧ not (CheckSPAlignment s) then
    write_err (StateError.Fault s!"[Inst: {inst_str}] SP {address} is not aligned!") s
  else
    let address := if inst.postindex then address else address + offset
    let s :=
      match inst.L? with
      | false => -- STORE
        have h1 : datasize / 8 * 8 = datasize := by
          exact Nat.div_mul_cancel H1
        have h2 : datasize + datasize = 2 * datasize := by
          omega
        have h3 : (2 * (datasize / 8) * 8) = datasize + datasize := by
          rw [Nat.mul_assoc, h1, h2]
        let data1 := ldst_read inst.SIMD? datasize inst.Rt s
        let data2 := ldst_read inst.SIMD? datasize inst.Rt2 s
        let full_data := data2 ++ data1
        write_mem_bytes (2 * (datasize / 8)) address (h3 ▸ full_data) s
      | _ => -- LOAD
        have h4 : datasize - 1 - 0 + 1 = datasize := by
          simp; apply Nat.sub_add_cancel H2
        have h5 : 2 * datasize - 1 - datasize + 1 = datasize := by omega
        let full_data := read_mem_bytes (2 * (datasize / 8)) address s
        let data1 := extractLsb (datasize - 1) 0 full_data
        let data2 := extractLsb ((2 * datasize) - 1) datasize full_data
        if not inst.SIMD? ∧ signed then
          let s := write_gpr 64 inst.Rt (signExtend 64 data1) s
          write_gpr 64 inst.Rt2 (signExtend 64 data2) s
        else
          let s:= ldst_write inst.SIMD? datasize inst.Rt (h4 ▸ data1) s
          ldst_write inst.SIMD? datasize inst.Rt2 (h5 ▸ data2) s
    if inst.wback then
      let address := if inst.postindex then address + offset else address
      write_gpr 64 inst.Rn address s
    else
      s

def exec_reg_pair_common (inst : Reg_pair_cls) (inst_str : String) (s : ArmState) : ArmState :=
  if not inst.SIMD? ∧
     ((not inst.L? ∧ lsb inst.opc 0 = 1#1) ∨ (inst.opc = 0b11#2))
     ∨ inst.SIMD? ∧ (inst.opc = 0b11#2)
     ∨ reg_pair_constrain_unpredictable inst.wback inst
  then
    write_err (StateError.Illegal "Illegal instruction {inst_str} encountered!") s
  else
    let signed := (lsb inst.opc 0) != 0#1
    let scale := if not inst.SIMD?
                 then 2 + (BitVec.toNat (lsb inst.opc 1))
                 else 2 + (BitVec.toNat inst.opc)
    let datasize := 8 <<< scale
    let offset := (signExtend 64 inst.imm7) <<< scale
    have H1 : 8 ∣ datasize := by
      simp_all! only [gt_iff_lt, Nat.shiftLeft_eq, Nat.dvd_mul_right, datasize]
    have H2 : 0 < datasize := by
      simp_all! only [datasize]
      apply zero_lt_shift_left_pos (by decide)
    let s' := reg_pair_operation inst inst_str signed datasize offset s H1 H2
    let s' := write_pc ((read_pc s) + 4#64) s'
    s'

def exec_reg_pair_pre_indexed
  (inst : Reg_pair_pre_indexed_cls) (s : ArmState) : ArmState :=
  let extracted_inst : Reg_pair_cls :=
    { opc := inst.opc,
      SIMD? := inst.V = 1#1,
      L? := inst.L = 1#1,
      wback := true,
      postindex := false,
      imm7 := inst.imm7,
      Rt2 := inst.Rt2,
      Rn := inst.Rn,
      Rt := inst.Rt }
  exec_reg_pair_common extracted_inst s!"{inst}" s

def exec_reg_pair_post_indexed
  (inst : Reg_pair_post_indexed_cls) (s : ArmState) : ArmState :=
  let extracted_inst : Reg_pair_cls :=
    { opc := inst.opc,
      SIMD? := inst.V = 1#1,
      L? := inst.L = 1#1,
      wback := true,
      postindex := true,
      imm7 := inst.imm7,
      Rt2 := inst.Rt2,
      Rn := inst.Rn,
      Rt := inst.Rt }
  exec_reg_pair_common extracted_inst s!"{inst}" s

def exec_reg_pair_signed_offset
  (inst : Reg_pair_signed_offset_cls) (s : ArmState) : ArmState :=
  let extracted_inst : Reg_pair_cls :=
    { opc := inst.opc,
      SIMD? := inst.V = 1#1,
      L? := inst.L = 1#1,
      wback := false,
      postindex := false,
      imm7 := inst.imm7,
      Rt2 := inst.Rt2,
      Rn := inst.Rn,
      Rt := inst.Rt }
  exec_reg_pair_common extracted_inst s!"{inst}" s

----------------------------------------------------------------------
-- LDST Advanced SIMD multiple struct (stubbed)
----------------------------------------------------------------------

def exec_advanced_simd_multiple_struct
  (_inst : Advanced_simd_multiple_struct_cls) (s : ArmState) : ArmState := s

def exec_advanced_simd_multiple_struct_post_indexed
  (_inst : Advanced_simd_multiple_struct_post_indexed_cls) (s : ArmState) : ArmState := s

end LDST

----------------------------------------------------------------------
-- exec_inst (from Arm/Exec.lean)
-- Non-LDST branches stubbed as identity on state
----------------------------------------------------------------------

def exec_inst (ai : ArmInst) (s : ArmState) : ArmState :=
  open ArmInst in
  match ai with
  | DPI (DataProcImmInst.Add_sub_imm _) => s
  | DPI (DataProcImmInst.PC_rel_addressing _) => s
  | DPI (DataProcImmInst.Logical_imm _) => s
  | DPI (DataProcImmInst.Bitfield _) => s
  | DPI (DataProcImmInst.Move_wide_imm _) => s

  | BR (BranchInst.Compare_branch _) => s
  | BR (BranchInst.Uncond_branch_imm _) => s
  | BR (BranchInst.Uncond_branch_reg _) => s
  | BR (BranchInst.Cond_branch_imm _) => s
  | BR (BranchInst.Hints _) => s

  | DPR (DataProcRegInst.Add_sub_carry _) => s
  | DPR (DataProcRegInst.Add_sub_shifted_reg _) => s
  | DPR (DataProcRegInst.Conditional_select _) => s
  | DPR (DataProcRegInst.Data_processing_one_source _) => s
  | DPR (DataProcRegInst.Data_processing_two_source _) => s
  | DPR (DataProcRegInst.Logical_shifted_reg _) => s

  | DPSFP (DataProcSFPInst.Advanced_simd_copy _) => s
  | DPSFP (DataProcSFPInst.Crypto_aes _) => s
  | DPSFP (DataProcSFPInst.Crypto_two_reg_sha512 _) => s
  | DPSFP (DataProcSFPInst.Crypto_three_reg_sha512 _) => s
  | DPSFP (DataProcSFPInst.Crypto_four_reg _) => s
  | DPSFP (DataProcSFPInst.Advanced_simd_two_reg_misc _) => s
  | DPSFP (DataProcSFPInst.Advanced_simd_extract _) => s
  | DPSFP (DataProcSFPInst.Advanced_simd_permute _) => s
  | DPSFP (DataProcSFPInst.Advanced_simd_modified_immediate _) => s
  | DPSFP (DataProcSFPInst.Advanced_simd_shift_by_immediate _) => s
  | DPSFP (DataProcSFPInst.Advanced_simd_scalar_shift_by_immediate _) => s
  | DPSFP (DataProcSFPInst.Advanced_simd_scalar_copy _) => s
  | DPSFP (DataProcSFPInst.Advanced_simd_table_lookup _) => s
  | DPSFP (DataProcSFPInst.Advanced_simd_three_same _) => s
  | DPSFP (DataProcSFPInst.Advanced_simd_three_different _) => s
  | DPSFP (DataProcSFPInst.Conversion_between_FP_and_Int _) => s

  | LDST (LDSTInst.Reg_imm_post_indexed i) =>
    LDST.exec_reg_imm_post_indexed i s
  | LDST (LDSTInst.Reg_unsigned_imm i) =>
    LDST.exec_reg_imm_unsigned_offset i s
  | LDST (LDSTInst.Reg_unscaled_imm i) =>
    LDST.exec_reg_unscaled_imm i s
  | LDST (LDSTInst.Reg_pair_pre_indexed i) =>
    LDST.exec_reg_pair_pre_indexed i s
  | LDST (LDSTInst.Reg_pair_post_indexed i) =>
    LDST.exec_reg_pair_post_indexed i s
  | LDST (LDSTInst.Reg_pair_signed_offset i) =>
    LDST.exec_reg_pair_signed_offset i s
  | LDST (LDSTInst.Advanced_simd_multiple_struct i) =>
    LDST.exec_advanced_simd_multiple_struct i s
  | LDST (LDSTInst.Advanced_simd_multiple_struct_post_indexed i) =>
    LDST.exec_advanced_simd_multiple_struct_post_indexed i s

----------------------------------------------------------------------
-- stepi and run (from Arm/Exec.lean)
----------------------------------------------------------------------

def stepi (s : ArmState) : ArmState :=
  let err := read_err s
  match err with
  | StateError.None =>
    (let pc := read_pc s
     let raw_inst := fetch_inst pc s
     match raw_inst with
      | none =>
        write_err (StateError.NotFound s!"No instruction found at PC {pc}!") s
      | some i =>
        let eai := decode_raw_inst i
        match eai with
          | none =>
            write_err (StateError.Unimplemented s!"Could not decode instruction {i} at PC {pc}!") s
          | some arm_inst => exec_inst arm_inst s)
  | _ => s

def run (n : Nat) (s : ArmState) : ArmState :=
  match n with
  | 0 => s
  | n' + 1 =>
    let s' := stepi s
    run n' s'

----------------------------------------------------------------------
-- LDST Tests (from Tests/LDSTTest.lean)
----------------------------------------------------------------------

section LDSTTest

open BitVec

def set_init_state (program : Program) : ArmState :=
  let s := { gpr := (fun (_ : BitVec 5) => 0#64),
             sfp := (fun (_ : BitVec 5) => 0#128),
             pc := 0#64,
             pstate := zero_pstate,
             mem := (fun (_ : BitVec 64) => 0#8),
             program := program,
             error := StateError.None}
  s

----------------------------------------------------------------------
-- test ldr, 32-bit gpr, unsigned offset
def ldr_gpr_unsigned_offset : Program :=
  def_program [ (0x0#64, 0xb9400fe0#32) ]  -- ldr w0, [sp, #12]

def ldr_gpr_unsigned_offset_state : ArmState :=
  let s := set_init_state ldr_gpr_unsigned_offset
  let s := write_mem_bytes 4 12#64 20#32 s
  s

def ldr_gpr_unsigned_offset_final_state : ArmState := run 1 ldr_gpr_unsigned_offset_state

example : (read_gpr 64 0#5 ldr_gpr_unsigned_offset_final_state) = 20#64 := by decide_cbv
example : ldr_gpr_unsigned_offset_final_state.pc = 4#64 := by decide_cbv

----------------------------------------------------------------------
-- test str, 64-bit gpr, post-index
def str_gpr_post_index : Program :=
  def_program [ (0x0#64, 0xf8003420#32) ] -- str x0, [x1], #3

def str_gpr_post_index_state : ArmState :=
  let s := set_init_state str_gpr_post_index
  let s := write_gpr 64 0#5 20#64 s
  write_gpr 64 1#5 0#64 s

def str_gpr_post_index_final_state : ArmState := run 1 str_gpr_post_index_state

example : (read_gpr 64 1#5 str_gpr_post_index_final_state) = 3#64 := by decide_cbv
example : (read_mem_bytes 8 0#64 str_gpr_post_index_final_state) = 20#64 := by decide_cbv
example : str_gpr_post_index_final_state.pc = 4#64 := by decide_cbv

----------------------------------------------------------------------
-- test ldr, 64-bit sfp, post-index
def ldr_sfp_post_index : Program :=
  def_program [ (0x0#64, 0xfc408420#32) ] -- ldr d0, [x1], #8

def ldr_sfp_post_index_state : ArmState :=
  let s := set_init_state ldr_sfp_post_index
  let s := write_mem_bytes 8 0#64 20#64 s
  s

def ldr_sfp_post_index_final_state : ArmState := run 1 ldr_sfp_post_index_state

example : (read_sfp 128 0#5 ldr_sfp_post_index_final_state) = 20#128 := by decide_cbv
example : (read_gpr 64 1#5 ldr_sfp_post_index_final_state) = 8#64 := by decide_cbv

----------------------------------------------------------------------
-- test str, 128-bit sfp, unsigned offset
def str_stp_unsigned_offset : Program :=
  def_program [ (0x0#64, 0x3d800420#32) ] -- str q0, [x1, #1]

def str_sfp_unsigned_offset_state : ArmState :=
  let s := set_init_state str_stp_unsigned_offset
  write_sfp 128 0#5 123#128 s

def str_sfp_unsigned_offset_final_state : ArmState := run 1 str_sfp_unsigned_offset_state

example : (read_mem_bytes 16 16#64 str_sfp_unsigned_offset_final_state) = 123#128 := by decide_cbv

----------------------------------------------------------------------
-- test ldrb, unsigned offset
def ldrb_unsigned_offset : Program :=
  def_program [ (0x0#64, 0x39401020#32) ] -- ldrb x0, [x1, #4]

def ldrb_unsigned_offset_state: ArmState :=
  let s := set_init_state ldrb_unsigned_offset
  write_mem_bytes 1 4#64 20#8 s

def ldrb_unsigned_offset_final_state : ArmState := run 1 ldrb_unsigned_offset_state

example : (read_gpr 64 0#5 ldrb_unsigned_offset_final_state) = 20#64 := by decide_cbv

----------------------------------------------------------------------
-- test strb, post-index
def strb_post_index : Program :=
  def_program [ (0x0#64, 0x381fc420#32) ] -- strb x0, [x1], #-4

def strb_post_index_state : ArmState :=
  let s := set_init_state strb_post_index
  let s := write_gpr 64 1#5 5#64 s
  write_gpr 64 0#5 20#64 s

def strb_post_index_final_state : ArmState := run 1 strb_post_index_state

example : (read_gpr 64 0#5 strb_post_index_final_state) = 20#64 := by decide_cbv
example : (read_gpr 64 1#5 strb_post_index_final_state) = 1#64 := by decide_cbv

----------------------------------------------------------------------
-- test ldp
def ldp_gpr_pre_index : Program :=
  def_program [ (0x0#64, 0xa9c00820#32) ] -- ldp x0, x2, [x1]!

def ldp_gpr_pre_index_state : ArmState :=
  let s := set_init_state ldp_gpr_pre_index
  write_mem_bytes 16 0#64 0x1234000000000000ABCD#128 s

def ldp_gpr_pre_index_final_state : ArmState := run 1 ldp_gpr_pre_index_state

example : (read_gpr 64 0#5 ldp_gpr_pre_index_final_state) = 0xABCD#64 := by decide_cbv
example : (read_gpr 64 2#5 ldp_gpr_pre_index_final_state) = 0x1234#64 := by decide_cbv

end LDSTTest
