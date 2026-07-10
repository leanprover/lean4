/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Pehle
-/
module

prelude
public import Lean.Compiler.Backend.Wasm.Encoding
public import Lean.Compiler.Backend.Wasm.Types

public section

namespace Lean.Compiler.Backend.Wasm.Instr

open Lean.Compiler.Backend.Wasm
open Lean.Compiler.Backend.Wasm.Types

/-- Relocation kind (WASM linking meta, reloc.CODE). -/
structure Reloc where
  kind : UInt8
  /-- Byte offset from the start of the enclosing code unit (function body size field excluded
  until the encoder adds it). -/
  offset : Nat
  symbolIndex : Nat
  addend : Option Int := none
  deriving Inhabited

/-- Encoded instruction stream with pending relocations. -/
structure Code where
  bytes : ByteArray := ByteArray.empty
  relocs : Array Reloc := #[]
  deriving Inhabited

namespace Code

def empty : Code := {}

def raw (bytes : ByteArray) : Code := { bytes }

def append (lhs rhs : Code) : Code :=
  { bytes := Encoding.append lhs.bytes rhs.bytes
    relocs := lhs.relocs ++ rhs.relocs.map fun r =>
      { r with offset := lhs.bytes.size + r.offset } }

def appendMany (parts : Array Code) : Code :=
  parts.foldl (init := empty) Code.append

def pushByte (c : Code) (b : UInt8) : Code :=
  { c with bytes := c.bytes.push b }

def pushBytes (c : Code) (bs : ByteArray) : Code :=
  { c with bytes := Encoding.append c.bytes bs }

def withReloc (c : Code) (kind : UInt8) (offsetInInstr : Nat) (symbol : Nat)
    (addend : Option Int := none) : Code :=
  { c with relocs := c.relocs.push { kind, offset := offsetInInstr, symbolIndex := symbol, addend } }

end Code

/-- Block result type encoding. -/
inductive BlockType where
  | void
  | val (t : ValType)
  deriving Inhabited

def encodeBlockType : BlockType → ByteArray
  | .void => ⟨#[0x40]⟩
  | .val t => ⟨#[t.toByte]⟩

/-- Typed WASM instruction AST used by the Lean→WASM lowerer. -/
inductive Instr where
  | unreachable
  | nop
  | drop
  | «end»
  | block (ty : BlockType) (body : Array Instr)
  | loop (ty : BlockType) (body : Array Instr)
  | «if» (ty : BlockType) (thenBody : Array Instr) (elseBody : Array Instr)
  | br (depth : Nat)
  | brIf (depth : Nat)
  | brTable (labels : Array Nat) (defaultLabel : Nat)
  | «return»
  | call (funcIdx : Nat) (symbol : Nat)
  | returnCall (funcIdx : Nat) (symbol : Nat)
  | localGet (idx : Nat)
  | localSet (idx : Nat)
  | localTee (idx : Nat)
  | i32Const (value : Int)
  | i64Const (value : Int)
  | /-- `i32.const` placeholder patched by a relocation (`kind` is the reloc type). -/
    i32ConstReloc (kind : UInt8) (symbol : Nat) (addend : Option Int := none)
  | i32Load (align : Nat) (offset : Nat)
  | i64Load (align : Nat) (offset : Nat)
  | f32Load (align : Nat) (offset : Nat)
  | f64Load (align : Nat) (offset : Nat)
  | i32Load8U (align : Nat) (offset : Nat)
  | i32Load16U (align : Nat) (offset : Nat)
  | i32Store (align : Nat) (offset : Nat)
  | i64Store (align : Nat) (offset : Nat)
  | f32Store (align : Nat) (offset : Nat)
  | f64Store (align : Nat) (offset : Nat)
  | i32Store8 (align : Nat) (offset : Nat)
  | i32Store16 (align : Nat) (offset : Nat)
  | i32Eqz | i32Eq | i32Ne
  | i32LtS | i32LtU | i32GtS | i32GtU | i32LeS | i32LeU | i32GeS | i32GeU
  | i64Eqz | i64Eq | i64Ne
  | i64LtS | i64LtU | i64GtS | i64GtU | i64LeS | i64LeU | i64GeS | i64GeU
  | f32Eq | f32Ne | f32Lt | f32Gt | f32Le | f32Ge
  | f64Eq | f64Ne | f64Lt | f64Gt | f64Le | f64Ge
  | i32Add | i32Sub | i32Mul | i32DivU | i32DivS | i32RemU | i32RemS
  | i32And | i32Or | i32Xor | i32Shl | i32ShrU | i32ShrS
  | i64Add | i64Sub | i64Mul | i64DivU | i64DivS | i64RemU | i64RemS
  | i64And | i64Or | i64Xor | i64Shl | i64ShrU | i64ShrS
  | f32Add | f32Sub | f32Mul | f32Div | f32Neg
  | f64Add | f64Sub | f64Mul | f64Div | f64Neg
  | i32WrapI64
  | i64ExtendI32U
  | select
  deriving Inhabited

private def opByte (op : Nat) : ByteArray := ⟨#[op.toUInt8]⟩

private def memArg (align offset : Nat) : ByteArray :=
  Encoding.append (Encoding.encodeULEB align) (Encoding.encodeULEB offset)

mutual
partial def encodeInstr : Instr → Code
  | .unreachable => Code.raw (opByte 0x00)
  | .nop => Code.raw (opByte 0x01)
  | .drop => Code.raw (opByte 0x1a)
  | .«end» => Code.raw (opByte 0x0b)
  | .block ty body =>
    Code.appendMany #[Code.raw (Encoding.append (opByte 0x02) (encodeBlockType ty)),
      encodeInstrs body, Code.raw (opByte 0x0b)]
  | .loop ty body =>
    Code.appendMany #[Code.raw (Encoding.append (opByte 0x03) (encodeBlockType ty)),
      encodeInstrs body, Code.raw (opByte 0x0b)]
  | .«if» ty thenBody elseBody =>
    if elseBody.isEmpty then
      Code.appendMany #[Code.raw (Encoding.append (opByte 0x04) (encodeBlockType ty)),
        encodeInstrs thenBody, Code.raw (opByte 0x0b)]
    else
      Code.appendMany #[Code.raw (Encoding.append (opByte 0x04) (encodeBlockType ty)),
        encodeInstrs thenBody, Code.raw (opByte 0x05), encodeInstrs elseBody, Code.raw (opByte 0x0b)]
  | .br d => Code.raw (Encoding.append (opByte 0x0c) (Encoding.encodeULEB d))
  | .brIf d => Code.raw (Encoding.append (opByte 0x0d) (Encoding.encodeULEB d))
  | .brTable labels defaultLabel =>
    let payload := labels.foldl (init := Encoding.encodeULEB labels.size) fun out lab =>
      Encoding.append out (Encoding.encodeULEB lab)
    let payload := Encoding.append payload (Encoding.encodeULEB defaultLabel)
    Code.raw (Encoding.append (opByte 0x0e) payload)
  | .«return» => Code.raw (opByte 0x0f)
  | .call idx symbol =>
    let leb := Encoding.encodeULEB5 idx
    { bytes := Encoding.append (opByte 0x10) leb
      relocs := #[{ kind := 0, offset := 1, symbolIndex := symbol }] }
  | .returnCall idx symbol =>
    let leb := Encoding.encodeULEB5 idx
    { bytes := Encoding.append (opByte 0x12) leb
      relocs := #[{ kind := 0, offset := 1, symbolIndex := symbol }] }
  | .localGet i => Code.raw (Encoding.append (opByte 0x20) (Encoding.encodeULEB i))
  | .localSet i => Code.raw (Encoding.append (opByte 0x21) (Encoding.encodeULEB i))
  | .localTee i => Code.raw (Encoding.append (opByte 0x22) (Encoding.encodeULEB i))
  | .i32Const v => Code.raw (Encoding.append (opByte 0x41) (Encoding.encodeSLEB v))
  | .i64Const v => Code.raw (Encoding.append (opByte 0x42) (Encoding.encodeSLEB v))
  | .i32ConstReloc kind symbol addend =>
    let placeholder : Int := if kind == 1 then 1 else 0
    { bytes := Encoding.append (opByte 0x41) (Encoding.encodeSLEB5 placeholder)
      relocs := #[{ kind, offset := 1, symbolIndex := symbol, addend }] }
  | .i32Load a o => Code.raw (Encoding.append (opByte 0x28) (memArg a o))
  | .i64Load a o => Code.raw (Encoding.append (opByte 0x29) (memArg a o))
  | .f32Load a o => Code.raw (Encoding.append (opByte 0x2a) (memArg a o))
  | .f64Load a o => Code.raw (Encoding.append (opByte 0x2b) (memArg a o))
  | .i32Load8U a o => Code.raw (Encoding.append (opByte 0x2d) (memArg a o))
  | .i32Load16U a o => Code.raw (Encoding.append (opByte 0x2f) (memArg a o))
  | .i32Store a o => Code.raw (Encoding.append (opByte 0x36) (memArg a o))
  | .i64Store a o => Code.raw (Encoding.append (opByte 0x37) (memArg a o))
  | .f32Store a o => Code.raw (Encoding.append (opByte 0x38) (memArg a o))
  | .f64Store a o => Code.raw (Encoding.append (opByte 0x39) (memArg a o))
  | .i32Store8 a o => Code.raw (Encoding.append (opByte 0x3a) (memArg a o))
  | .i32Store16 a o => Code.raw (Encoding.append (opByte 0x3b) (memArg a o))
  | .i32Eqz => Code.raw (opByte 0x45) | .i32Eq => Code.raw (opByte 0x46) | .i32Ne => Code.raw (opByte 0x47)
  | .i32LtS => Code.raw (opByte 0x48) | .i32LtU => Code.raw (opByte 0x49)
  | .i32GtS => Code.raw (opByte 0x4a) | .i32GtU => Code.raw (opByte 0x4b)
  | .i32LeS => Code.raw (opByte 0x4c) | .i32LeU => Code.raw (opByte 0x4d)
  | .i32GeS => Code.raw (opByte 0x4e) | .i32GeU => Code.raw (opByte 0x4f)
  | .i64Eqz => Code.raw (opByte 0x50) | .i64Eq => Code.raw (opByte 0x51) | .i64Ne => Code.raw (opByte 0x52)
  | .i64LtS => Code.raw (opByte 0x53) | .i64LtU => Code.raw (opByte 0x54)
  | .i64GtS => Code.raw (opByte 0x55) | .i64GtU => Code.raw (opByte 0x56)
  | .i64LeS => Code.raw (opByte 0x57) | .i64LeU => Code.raw (opByte 0x58)
  | .i64GeS => Code.raw (opByte 0x59) | .i64GeU => Code.raw (opByte 0x5a)
  | .f32Eq => Code.raw (opByte 0x5b) | .f32Ne => Code.raw (opByte 0x5c)
  | .f32Lt => Code.raw (opByte 0x5d) | .f32Gt => Code.raw (opByte 0x5e)
  | .f32Le => Code.raw (opByte 0x5f) | .f32Ge => Code.raw (opByte 0x60)
  | .f64Eq => Code.raw (opByte 0x61) | .f64Ne => Code.raw (opByte 0x62)
  | .f64Lt => Code.raw (opByte 0x63) | .f64Gt => Code.raw (opByte 0x64)
  | .f64Le => Code.raw (opByte 0x65) | .f64Ge => Code.raw (opByte 0x66)
  | .i32Add => Code.raw (opByte 0x6a) | .i32Sub => Code.raw (opByte 0x6b) | .i32Mul => Code.raw (opByte 0x6c)
  | .i32DivS => Code.raw (opByte 0x6d) | .i32DivU => Code.raw (opByte 0x6e)
  | .i32RemS => Code.raw (opByte 0x6f) | .i32RemU => Code.raw (opByte 0x70)
  | .i32And => Code.raw (opByte 0x71) | .i32Or => Code.raw (opByte 0x72) | .i32Xor => Code.raw (opByte 0x73)
  | .i32Shl => Code.raw (opByte 0x74) | .i32ShrS => Code.raw (opByte 0x75) | .i32ShrU => Code.raw (opByte 0x76)
  | .i64Add => Code.raw (opByte 0x7c) | .i64Sub => Code.raw (opByte 0x7d) | .i64Mul => Code.raw (opByte 0x7e)
  | .i64DivS => Code.raw (opByte 0x7f) | .i64DivU => Code.raw (opByte 0x80)
  | .i64RemS => Code.raw (opByte 0x81) | .i64RemU => Code.raw (opByte 0x82)
  | .i64And => Code.raw (opByte 0x83) | .i64Or => Code.raw (opByte 0x84) | .i64Xor => Code.raw (opByte 0x85)
  | .i64Shl => Code.raw (opByte 0x86) | .i64ShrS => Code.raw (opByte 0x87) | .i64ShrU => Code.raw (opByte 0x88)
  | .f32Add => Code.raw (opByte 0x92) | .f32Sub => Code.raw (opByte 0x93) | .f32Mul => Code.raw (opByte 0x94)
  | .f32Div => Code.raw (opByte 0x95) | .f32Neg => Code.raw (opByte 0x8c)
  | .f64Add => Code.raw (opByte 0xa0) | .f64Sub => Code.raw (opByte 0xa1) | .f64Mul => Code.raw (opByte 0xa2)
  | .f64Div => Code.raw (opByte 0xa3) | .f64Neg => Code.raw (opByte 0x9a)
  | .i32WrapI64 => Code.raw (opByte 0xa7)
  | .i64ExtendI32U => Code.raw (opByte 0xad)
  | .select => Code.raw (opByte 0x1b)

partial def encodeInstrs (instrs : Array Instr) : Code :=
  instrs.foldl (init := Code.empty) fun c i => Code.append c (encodeInstr i)
end

/-- Encode a function body: instructions, then `unreachable; end`.

The trailing `unreachable` matches the historical emitter and keeps the implicit
function return well-typed when every real path uses an explicit `return`. -/
def encodeBody (instrs : Array Instr) : Code :=
  Code.appendMany #[encodeInstrs instrs, encodeInstr .unreachable, encodeInstr .«end»]

end Lean.Compiler.Backend.Wasm.Instr
