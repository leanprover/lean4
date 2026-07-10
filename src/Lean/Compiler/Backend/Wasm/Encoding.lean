/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Pehle
-/
module

prelude
public import Init.Prelude
public import Init.Data.Array.Basic
public import Init.Data.Int.DivMod
public import Init.Data.String.Defs

public section

namespace Lean.Compiler.Backend.Wasm.Encoding

private partial def encodeULEBAux (value : Nat) (out : ByteArray) : ByteArray :=
  let byte := value % 128
  let rest := value / 128
  let byte := if rest == 0 then byte else byte + 128
  let out := out.push byte.toUInt8
  if rest == 0 then out else encodeULEBAux rest out

/-- Encode an unsigned integer using canonical unsigned LEB128. -/
def encodeULEB (value : Nat) : ByteArray :=
  encodeULEBAux value ByteArray.empty

private def encodeULEB5Aux : Nat → Nat → ByteArray → ByteArray
  | value, 0, out => out.push (value % 128).toUInt8
  | value, remaining + 1, out =>
    encodeULEB5Aux (value / 128) remaining (out.push ((value % 128) + 128).toUInt8)

/-- Encode an unsigned 32-bit relocation operand in the fixed five-byte form. -/
def encodeULEB5 (value : Nat) : ByteArray :=
  encodeULEB5Aux value 4 ByteArray.empty

private partial def encodeSLEBAux (value : Int) (out : ByteArray) : ByteArray :=
  let byte := value % 128
  let rest := value / 128
  let byteNat := byte.toNat
  let signSet := byteNat >= 64
  let done := (rest == 0 && !signSet) || (rest == -1 && signSet)
  let byteNat := if done then byteNat else byteNat + 128
  let out := out.push byteNat.toUInt8
  if done then out else encodeSLEBAux rest out

/-- Encode a signed integer using canonical signed LEB128. -/
def encodeSLEB (value : Int) : ByteArray :=
  encodeSLEBAux value ByteArray.empty

private def encodeSLEB5Aux : Int → Nat → ByteArray → ByteArray
  | value, 0, out => out.push (value % 128).toNat.toUInt8
  | value, remaining + 1, out =>
    encodeSLEB5Aux (value / 128) remaining (out.push ((value % 128).toNat + 128).toUInt8)

/-- Encode a signed 32-bit relocation operand in the fixed five-byte form. -/
def encodeSLEB5 (value : Int) : ByteArray :=
  encodeSLEB5Aux value 4 ByteArray.empty

def append (lhs rhs : ByteArray) : ByteArray :=
  rhs.data.foldl (init := lhs) ByteArray.push

def encodeName (name : String) : ByteArray :=
  append (encodeULEB name.toUTF8.size) name.toUTF8

end Lean.Compiler.Backend.Wasm.Encoding
