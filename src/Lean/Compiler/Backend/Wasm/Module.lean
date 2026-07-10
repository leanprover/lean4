/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Pehle
-/
module

prelude
public import Lean.Compiler.Backend.Wasm.Encoding
public import Init.Data.Array.Basic

public section

namespace Lean.Compiler.Backend.Wasm

private def bytes (values : Array Nat) : ByteArray :=
  ⟨values.map Nat.toUInt8⟩

private def wasmHeader : ByteArray :=
  bytes #[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00]

structure Section where
  id : UInt8
  payload : ByteArray

namespace Section

def encode (sec : Section) : ByteArray :=
  let header := ByteArray.empty.push sec.id
  Encoding.append header <| Encoding.append (Encoding.encodeULEB sec.payload.size) sec.payload

end Section

structure Module where
  sections : Array Section := #[]

namespace Module

def empty : Module := {}

def encode (module : Module) : ByteArray :=
  module.sections.foldl (init := wasmHeader) fun out sec =>
    Encoding.append out sec.encode

/-- A small complete module used to exercise the core binary encoder. -/
def minimalReturningI32 (value : Int) : Module :=
  let typeSection := bytes #[0x01, 0x60, 0x00, 0x01, 0x7f]
  let functionSection := bytes #[0x01, 0x00]
  let exportSection := Encoding.append (bytes #[0x01]) <|
    Encoding.append (Encoding.encodeName "main") (bytes #[0x00, 0x00])
  let body := Encoding.append (bytes #[0x00, 0x41]) <|
    Encoding.append (Encoding.encodeSLEB value) (bytes #[0x0b])
  let codeSection := Encoding.append (bytes #[0x01]) <|
    Encoding.append (Encoding.encodeULEB body.size) body
  { sections := #[
      ⟨0x01, typeSection⟩,
      ⟨0x03, functionSection⟩,
      ⟨0x07, exportSection⟩,
      ⟨0x0a, codeSection⟩
    ] }

end Module
end Lean.Compiler.Backend.Wasm
