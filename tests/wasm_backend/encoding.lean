module

public meta import Lean.Compiler.Backend.Wasm

/-!
Tests WebAssembly binary encoding primitives, layout, instruction AST, and minimal modules.
-/

open Lean.Compiler.Backend.Wasm
open Lean.Compiler.Backend.Wasm.Layout
open Lean.Compiler.Backend.Wasm.Instr

#guard Encoding.encodeULEB 0 == ⟨#[0x00]⟩
#guard Encoding.encodeULEB 127 == ⟨#[0x7f]⟩
#guard Encoding.encodeULEB 128 == ⟨#[0x80, 0x01]⟩
#guard Encoding.encodeULEB 624485 == ⟨#[0xe5, 0x8e, 0x26]⟩
#guard Encoding.encodeULEB5 0 == ⟨#[0x80, 0x80, 0x80, 0x80, 0x00]⟩
#guard Encoding.encodeSLEB 0 == ⟨#[0x00]⟩
#guard Encoding.encodeSLEB (-1) == ⟨#[0x7f]⟩
#guard Encoding.encodeSLEB (-624485) == ⟨#[0x9b, 0xf1, 0x59]⟩
#guard Module.empty.encode == ⟨#[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00]⟩
#guard (Module.minimalReturningI32 42).encode == ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f,
  0x03, 0x02, 0x01, 0x00,
  0x07, 0x08, 0x01, 0x04, 0x6d, 0x61, 0x69, 0x6e, 0x00, 0x00,
  0x0a, 0x06, 0x01, 0x04, 0x00, 0x41, 0x2a, 0x0b]⟩

-- wasm32 object layout ABI
#guard Layout.default.ptrSize == 4
#guard Layout.default.headerSize == 8
#guard Layout.default.tagOffset == 7
#guard Layout.default.objField 0 == 8
#guard Layout.default.objField 1 == 12

-- Instruction AST encodes i32.add
#guard (encodeInstr .i32Add).bytes == ⟨#[0x6a]⟩
#guard (encodeInstr (.i32Const 42)).bytes == ⟨#[0x41, 0x2a]⟩
#guard (encodeInstr (.brTable #[0, 1] 2)).bytes == ⟨#[0x0e, 0x02, 0x00, 0x01, 0x02]⟩

#eval IO.println "ok"
