/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Lean.Compiler.Bytecode.Basic

public section

namespace Lean.Compiler.Bytecode

structure Instruction where
  value : UInt32

def Instruction.uconst (target val : UInt32) : Instruction where
  value := (0 : UInt32) <<< 26 ||| target <<< 18 ||| val

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

def Instruction.ifTag (target tag : UInt32) (offset : Int32) : Instruction where
  value := (38 : UInt32) <<< 26 ||| target <<< 18 ||| tag <<< 8 ||| (offset + 0x80).toUInt32

def Instruction.jump (offset : Int32) : Instruction where
  value := (39 : UInt32) <<< 26 ||| (offset + 0x200_0000).toUInt32

def pushInstr (code : ByteArray) (instr : Instruction) : ByteArray :=
  let code := code.push instr.value.toUInt8
  let code := code.push (instr.value >>> 8).toUInt8
  let code := code.push (instr.value >>> 16).toUInt8
  code.push (instr.value >>> 24).toUInt8

def assemble (instrs : Array Instruction) : ByteArray :=
  instrs.foldl pushInstr (.emptyWithCapacity (instrs.size * 4))
