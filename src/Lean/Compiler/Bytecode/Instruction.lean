/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Lean.Compiler.Bytecode.Basic
import Init.Omega

public section

namespace Lean.Compiler.Bytecode

structure Instruction where
  value : UInt32
deriving Inhabited

def maxUConst : Nat := 1 <<< 18 - 1
def maxNConst : Nat := maxUConst / 2

def Instruction.uconst (target val : UInt32) : Instruction where
  value := (0 : UInt32) <<< 26 ||| target <<< 18 ||| val

def Instruction.nconst (target val : UInt32) : Instruction :=
  .uconst target (val <<< 1 ||| 1)

def Instruction.move (target source : UInt32) : Instruction where
  value := (1 : UInt32) <<< 26 ||| target <<< 13 ||| source

def Instruction.ret (target : UInt32) : Instruction where
  value := (2 : UInt32) <<< 26 ||| target

def Instruction.call (fn : UInt32) : Instruction where
  value := (3 : UInt32) <<< 26 ||| fn

def Instruction.retcall (fn : UInt32) : Instruction where
  value := (4 : UInt32) <<< 26 ||| fn

def Instruction.computeScalar (usize ssize : UInt32) : Instruction where
  value := (5 : UInt32) <<< 26 ||| usize <<< 13 ||| ssize

def Instruction.allocCtor (target tag numObjs : UInt32) : Instruction where
  value := (6 : UInt32) <<< 26 ||| target <<< 18 ||| tag <<< 8 ||| numObjs

def Instruction.proj (target source idx : UInt32) : Instruction where
  value := (7 : UInt32) <<< 26 ||| target <<< 16 ||| source <<< 8 ||| idx

def Instruction.uproj (target source idx : UInt32) : Instruction where
  value := (8 : UInt32) <<< 26 ||| target <<< 16 ||| source <<< 8 ||| idx

def Instruction.sproj8 (target source : UInt32) : Instruction where
  value := (9 : UInt32) <<< 26 ||| target <<< 8 ||| source

def Instruction.sproj16 (target source : UInt32) : Instruction where
  value := (10 : UInt32) <<< 26 ||| target <<< 8 ||| source

def Instruction.sproj32 (target source : UInt32) : Instruction where
  value := (11 : UInt32) <<< 26 ||| target <<< 8 ||| source

def Instruction.sproj64 (target source : UInt32) : Instruction where
  value := (12 : UInt32) <<< 26 ||| target <<< 8 ||| source

def Instruction.set (target source idx : UInt32) : Instruction where
  value := (13 : UInt32) <<< 26 ||| target <<< 16 ||| source <<< 8 ||| idx

def Instruction.uset (target source idx : UInt32) : Instruction where
  value := (14 : UInt32) <<< 26 ||| target <<< 16 ||| source <<< 8 ||| idx

def Instruction.sset8 (target source : UInt32) : Instruction where
  value := (15 : UInt32) <<< 26 ||| target <<< 8 ||| source

def Instruction.sset16 (target source : UInt32) : Instruction where
  value := (16 : UInt32) <<< 26 ||| target <<< 8 ||| source

def Instruction.sset32 (target source : UInt32) : Instruction where
  value := (17 : UInt32) <<< 26 ||| target <<< 8 ||| source

def Instruction.sset64 (target source : UInt32) : Instruction where
  value := (18 : UInt32) <<< 26 ||| target <<< 8 ||| source

def Instruction.boxSmall (target source : UInt32) : Instruction where
  value := (19 : UInt32) <<< 26 ||| target <<< 8 ||| source

def Instruction.boxUInt32 (target source : UInt32) : Instruction where
  value := (20 : UInt32) <<< 26 ||| target <<< 8 ||| source

def Instruction.boxUInt64 (target source : UInt32) : Instruction where
  value := (21 : UInt32) <<< 26 ||| target <<< 8 ||| source

def Instruction.boxUSize (target source : UInt32) : Instruction where
  value := (22 : UInt32) <<< 26 ||| target <<< 8 ||| source

def Instruction.boxFloat (target source : UInt32) : Instruction where
  value := (23 : UInt32) <<< 26 ||| target <<< 8 ||| source

def Instruction.boxFloat32 (target source : UInt32) : Instruction where
  value := (24 : UInt32) <<< 26 ||| target <<< 8 ||| source

def Instruction.unboxSmall (target source : UInt32) : Instruction where
  value := (25 : UInt32) <<< 26 ||| target <<< 8 ||| source

def Instruction.unboxUInt32 (target source : UInt32) : Instruction where
  value := (26 : UInt32) <<< 26 ||| target <<< 8 ||| source

def Instruction.unboxUInt64 (target source : UInt32) : Instruction where
  value := (27 : UInt32) <<< 26 ||| target <<< 8 ||| source

def Instruction.unboxUSize (target source : UInt32) : Instruction where
  value := (28 : UInt32) <<< 26 ||| target <<< 8 ||| source

def Instruction.unboxFloat (target source : UInt32) : Instruction where
  value := (29 : UInt32) <<< 26 ||| target <<< 8 ||| source

def Instruction.unboxFloat32 (target source : UInt32) : Instruction where
  value := (30 : UInt32) <<< 26 ||| target <<< 8 ||| source

def Instruction.inc (target count : UInt32) : Instruction where
  value := (31 : UInt32) <<< 26 ||| target <<< 8 ||| count

def Instruction.dec (target count : UInt32) : Instruction where
  value := (32 : UInt32) <<< 26 ||| target <<< 8 ||| count

def Instruction.isShared (target source : UInt32) : Instruction where
  value := (33 : UInt32) <<< 26 ||| target <<< 8 ||| source

def Instruction.loadTag (target source : UInt32) : Instruction where
  value := (34 : UInt32) <<< 26 ||| target <<< 8 ||| source

def Instruction.jumpTable (source limit : UInt32) : Instruction where
  value := (35 : UInt32) <<< 26 ||| source <<< 10 ||| limit

def Instruction.setTag (target tag : UInt32) : Instruction where
  value := (36 : UInt32) <<< 26 ||| target <<< 10 ||| tag

def Instruction.loadConst (fn : UInt32) : Instruction where
  value := (37 : UInt32) <<< 26 ||| fn

def Instruction.ifTag (target tag : UInt32) (offset : Int32) : Instruction where
  value := (38 : UInt32) <<< 26 ||| target <<< 18 ||| tag <<< 8 ||| (offset + 0x80).toUInt32

def Instruction.jump (offset : Int32) : Instruction where
  value := (39 : UInt32) <<< 26 ||| (offset + 0x200_0000).toUInt32

def Instruction.nojump : Instruction where
  value := (39 : UInt32) <<< 26

def Instruction.app (fn n : UInt32) : Instruction where
  value := (40 : UInt32) <<< 26 ||| n <<< 16 ||| fn

def Instruction.pap (fn n : UInt32) : Instruction where
  value := (41 : UInt32) <<< 26 ||| n <<< 16 ||| fn

def Instruction.del (target : UInt32) : Instruction where
  value := (42 : UInt32) <<< 26 ||| target

def Instruction.reset (n target source : UInt32) : Instruction where
  value := (43 : UInt32) <<< 26 ||| n <<< 16 ||| target <<< 8 ||| source

def Instruction.reuse (target tag numObjs : UInt32) : Instruction where
  value := (44 : UInt32) <<< 26 ||| target <<< 18 ||| tag <<< 8 ||| numObjs

def Instruction.storeCache (target : UInt32) : Instruction where
  value := (45 : UInt32) <<< 26 ||| target

def Instruction.skipIfCached (offset : UInt32) : Instruction where
  value := (46 : UInt32) <<< 26 ||| offset

def Instruction.declConst (tgt id : UInt32) : Instruction where
  value := (47 : UInt32) <<< 26 ||| tgt <<< 18 ||| id

def Instruction.assemblerInternal (idx : UInt32) : Instruction where
  value := (63 : UInt32) <<< 26 ||| idx

def pushInstr (code : ByteArray) (instr : Instruction) : ByteArray :=
  let code := code.push instr.value.toUInt8
  let code := code.push (instr.value >>> 8).toUInt8
  let code := code.push (instr.value >>> 16).toUInt8
  code.push (instr.value >>> 24).toUInt8

def assemble (instrs : Array Instruction) : ByteArray :=
  instrs.foldl pushInstr (.emptyWithCapacity (instrs.size * 4))

def addrToString (addr : Int) : String :=
  let addr := addr.toNat
  let addr := ((16).toDigits addr).leftpad 4 '0'
  "0x" ++ String.ofList addr

def Instruction.toString (instr : Instruction) (pos : Nat) : String :=
  let lo13 := instr.value &&& ((1 : UInt32) <<< 13 - 1)
  let hi13 := (instr.value >>> 13) &&& ((1 : UInt32) <<< 13 - 1)
  let lo8 := instr.value &&& ((1 : UInt32) <<< 8 - 1)
  let mid8 := (instr.value >>> 8) &&& ((1 : UInt32) <<< 8 - 1)
  let hi10 := (instr.value >>> 16) &&& ((1 : UInt32) <<< 10 - 1)
  let lo18 := instr.value &&& ((1 : UInt32) <<< 10 - 1)
  let hi8 := (instr.value >>> 18) &&& ((1 : UInt32) <<< 8 - 1)
  let mid10 := (instr.value >>> 8) &&& ((1 : UInt32) <<< 10 - 1)
  let hi18 := (instr.value >>> 8) &&& ((1 : UInt32) <<< 18 - 1)
  let lo10 := instr.value &&& ((1 : UInt32) <<< 10 - 1)
  let hi16 := (instr.value >>> 10) &&& ((1 : UInt32) <<< 16 - 1)
  let lo16 := instr.value &&& ((1 : UInt32) <<< 16 - 1)
  let all := instr.value &&& ((1 : UInt32) <<< 26 - 1)
  match instr.value >>> 26 with
  | 0 => s!"uconst R{hi8} {lo18}"
  | 1 => s!"move R{hi13} R{lo13}"
  | 2 => s!"ret R{all}"
  | 3 => s!"call #{all}"
  | 4 => s!"retcall #{all}"
  | 5 => s!"scalar {hi13} {lo13}"
  | 6 => s!"ctor R{hi8} {mid10} {lo8}"
  | 7 => s!"proj R{hi10} R{mid8} {lo8}"
  | 8 => s!"uproj R{hi10} R{mid8} {lo8}"
  | 9 => s!"sproj8 R{hi18} R{lo8}"
  | 10 => s!"sproj16 R{hi18} R{lo8}"
  | 11 => s!"sproj32 R{hi18} R{lo8}"
  | 12 => s!"sproj64 R{hi18} R{lo8}"
  | 13 => s!"set R{hi10} R{mid8} {lo8}"
  | 14 => s!"uset R{hi10} R{mid8} {lo8}"
  | 15 => s!"sset8 R{hi18} R{lo8}"
  | 16 => s!"sset16 R{hi18} R{lo8}"
  | 17 => s!"sset32 R{hi18} R{lo8}"
  | 18 => s!"sset64 R{hi18} R{lo8}"
  | 19 => s!"box R{hi18} R{lo8}"
  | 20 => s!"box32 R{hi18} R{lo8}"
  | 21 => s!"box64 R{hi18} R{lo8}"
  | 22 => s!"box_usz R{hi18} R{lo8}"
  | 23 => s!"box_f64 R{hi18} R{lo8}"
  | 24 => s!"box_f32 R{hi18} R{lo8}"
  | 25 => s!"unbox R{hi18} R{lo8}"
  | 26 => s!"unbox32 R{hi18} R{lo8}"
  | 27 => s!"unbox64 R{hi18} R{lo8}"
  | 28 => s!"unbox_usz R{hi18} R{lo8}"
  | 29 => s!"unbox_f64 R{hi18} R{lo8}"
  | 30 => s!"unbox_f32 R{hi18} R{lo8}"
  | 31 => s!"inc R{hi18} {lo8}"
  | 32 => s!"dec R{hi18} {lo8}"
  | 33 => s!"is_shared R{hi18} R{lo8}"
  | 34 => s!"load_tag R{hi18} R{lo8}"
  | 35 => s!"table R{hi16} {lo10}"
  | 36 => s!"set_tag R{hi16} {lo10}"
  | 37 => s!"load_const #{all}"
  | 38 => s!"if_tag R{hi8} {mid10} {addrToString <| pos + lo8.toNat - 0x80}"
  | 39 => s!"jump {addrToString <| pos + all.toNat - 0x200_0000}"
  | 40 => s!"app {hi10} R{lo16}"
  | 41 => s!"pap {hi10} #{lo16}"
  | 42 => s!"del R{lo8}"
  | 43 => s!"reset {hi10} R{mid8} R{lo8}"
  | 44 => s!"reuse R{hi8} {mid10} {lo8}"
  | 45 => s!"store_cache R{lo8}"
  | 46 => s!"skip_if_cached {addrToString <| pos + all.toNat}"
  | 47 => s!"decl_const R{hi18} @{lo8}"
  | _ => s!"0x{instr.value.toBitVec.toHex}"

def disassemble (code : BytecodeDecl) : String := Id.run do
  let mut str := s!"Declaration {code.name} (arity {code.arity}) with {code.stackSpace} stack \
    and {code.stackReserved} reserved\n"
  str := s!"{str}Code:\n"
  let sz : Nat := code.code.size / 4
  for h : i in *...sz do
    let pos := addrToString i
    have : i < code.code.size / 4 := h
    let b1 := code.code[i * 4]
    let b2 := code.code[i * 4 + 1]
    let b3 := code.code[i * 4 + 2]
    let b4 := code.code[i * 4 + 3]
    let val := b1.toUInt32 ||| b2.toUInt32 <<< 8 ||| b3.toUInt32 <<< 16 ||| b4.toUInt32 <<< 24
    let instr : Instruction := ⟨val⟩
    str := s!"{str}{pos}: {instr.toString (i + 1)}\n"
  unless code.symbols.isEmpty do
    str := s!"{str}Symbol table:\n"
    for h : i in *...code.symbols.size do
      str := s!"{str}#{i}: {code.symbols[i]}\n"
  return str
