/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
prelude
import Init.Data.ByteArray.Basic
import Init.Data.List.Control

namespace ByteArray

private def convertUtf8Byte (utf8 : ByteArray) (i : Nat) : Option UInt8 := do
let tailPrefixMask : UInt8 := 0b11000000;
let tailPrefix     : UInt8 := 0b10000000;
let tailMask       : UInt8 := 0b00111111;
byte ← utf8.data.get? i;
guard (byte.land tailPrefixMask = tailPrefix);
some (byte.land tailMask)

private def concatUtf8Bytes (xs : List UInt8) : UInt32 :=
let tailBits := 6;
xs.foldl (fun acc byte => (acc.shiftLeft tailBits).lor byte.toUInt32) 0

private partial def utf8ToStringAux : Nat → ByteArray → Option (List Char)
| i, utf8 =>
  -- mask to extract prefix × expected prefix of first byte ×
  -- mask to extract data from first byte
  let patterns : List (UInt8 × UInt8 × UInt8) := [
    (0b10000000, 0b00000000, 0b01111111),
    (0b11100000, 0b11000000, 0b00011111),
    (0b11110000, 0b11100000, 0b00001111),
    (0b11111000, 0b11110000, 0b00000111)
  ];
  if i < utf8.size then do
    let byte := utf8.get! i;
    (charVal, nextCharOffset) ←
      patterns.enum.firstM
        (fun ⟨j, prefixMask, pre, dataMask⟩ => do
          guard (byte.land prefixMask = pre);
          let msb := byte.land dataMask;
          -- parse the rest of the bytes
          bytes ← (List.range j).mapM (fun k => convertUtf8Byte utf8 (i+k+1));
          some (concatUtf8Bytes (msb :: bytes), j+1));
    ⟨h⟩ ← assert (isValidChar charVal);
    let ch : Char := ⟨charVal, h⟩;
    tail ← utf8ToStringAux (i+nextCharOffset) utf8;
    some (ch :: tail)
  else
    some []

def utf8ToString (b : ByteArray) : Option String :=
List.asString <$> utf8ToStringAux 0 b

end ByteArray

namespace String

private def TAG_CONT    : UInt8  := 0b10000000
private def TAG_TWO_B   : UInt8  := 0b11000000
private def TAG_THREE_B : UInt8  := 0b11100000
private def TAG_FOUR_B  : UInt8  := 0b11110000
private def MAX_ONE_B   : UInt32 := 0x80
private def MAX_TWO_B   : UInt32 := 0x800
private def MAX_THREE_B : UInt32 := 0x10000
private def MAX_FOUR_B  : UInt32 := 0x110000

private def toUtf8Aux (s : String) : List UInt8 :=
s.foldr
  (fun ch acc =>
    let ch := ch.val;
    if ch < MAX_ONE_B then
      ch.toUInt8 :: acc
    else if ch < MAX_TWO_B then
      let a := ((ch.shiftRight  6).land 0x1f).toUInt8.lor TAG_TWO_B;
      let b := (ch.land                 0x3f).toUInt8.lor TAG_CONT;
      a :: b :: acc
    else if ch < MAX_THREE_B then
      let a := ((ch.shiftRight 12).land 0x0f).toUInt8.lor TAG_THREE_B;
      let b := ((ch.shiftRight  6).land 0x3f).toUInt8.lor TAG_CONT;
      let c := (ch.land                 0x3f).toUInt8.lor TAG_CONT;
      a :: b :: c :: acc
    else if ch < MAX_FOUR_B then
      let a := ((ch.shiftRight 18).land 0x07).toUInt8.lor TAG_FOUR_B;
      let b := ((ch.shiftRight 12).land 0x3f).toUInt8.lor TAG_CONT;
      let c := ((ch.shiftRight  6).land 0x3f).toUInt8.lor TAG_CONT;
      let d := (ch.land                 0x3f).toUInt8.lor TAG_CONT;
      a :: b :: c :: d :: acc
    else
      panic! ("Codepoint " ++ toString ch ++ " is not UTF-8 encodable!"))
  []

def toUtf8 (s : String) : ByteArray :=
List.toByteArray $ toUtf8Aux s

end String
