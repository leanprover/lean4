/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.ByteArray.Basic
public import Std.Http.Data.Version
import Init.Omega

public section

/-!
# Encode

Appends the wire form of a value for a specific protocol version to a `ByteArray`. With
`open Std.Http.Internal`, `out ++ x` appends the HTTP/1.1 wire form of `x` to `out`.
-/

namespace Std.Http.Internal

set_option linter.all true

/--
Appends the wire form of a `t` for protocol version `v` to a `ByteArray`.
-/
class Encode (v : Version) (t : Type) where
  /--
  Appends the wire form of a `t` to the given bytes.
  -/
  encode : ByteArray → t → ByteArray

/--
`out ++ x` appends the HTTP/1.1 wire form of `x` to `out`. There is no `Encode` instance for
`ByteArray`, so `out ++ bytes` stays the usual append.
-/
scoped instance [Encode .v11 t] : HAppend ByteArray t ByteArray where
  hAppend := Encode.encode (v := .v11)

instance : Encode .v11 String where
  encode out s := out ++ s.toUTF8

/--
A character is written as UTF-8, so an ASCII character is a single byte.
-/
instance : Encode .v11 Char where
  encode out c := if c.val < 128 then out.push c.toUInt8 else out ++ c.toString.toUTF8

/--
Appends the decimal digits of `n`.
-/
def appendNat (out : ByteArray) (n : Nat) : ByteArray :=
  if n < 10 then out.push ('0'.toUInt8 + n.toUInt8)
  else (appendNat out (n / 10)).push ('0'.toUInt8 + (n % 10).toUInt8)

instance : Encode .v11 Nat where
  encode := appendNat

/--
Appends the lowercase hexadecimal digits of `n`.
-/
def appendHex (out : ByteArray) (n : Nat) : ByteArray :=
  let digit (d : Nat) : UInt8 := if d < 10 then '0'.toUInt8 + d.toUInt8 else 'a'.toUInt8 + (d - 10).toUInt8
  if n < 16 then out.push (digit n)
  else (appendHex out (n / 16)).push (digit (n % 16))

instance : Encode .v11 Version where
  encode out
    | .v10 => out ++ "HTTP/1.0"
    | .v11 => out ++ "HTTP/1.1"
    | .v20 => out ++ "HTTP/2.0"
    | .v30 => out ++ "HTTP/3.0"

end Std.Http.Internal
