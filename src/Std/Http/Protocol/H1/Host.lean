/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Data

public section

/-!
# Checking a `Host` field on its bytes

`isValid` answers what `Header.Host.parse` would, without parsing, for the common case of a host name
with an optional port. The server checks the `Host` field of every request (`Rules`), and parsing it
was a large part of the cost of a small request.
-/

namespace Std.Http.Protocol.H1.Host

set_option linter.all true

open Std.Http Std.Http.Internal

/--
Whether the bytes of `s` from `i` to `j` are a valid DNS label of a host name: 1 to 63 of
`ALPHA / DIGIT / "-" / "_"`, neither first nor last a `-` (`URI.isValidDomainLabel`). The caller
checked that every byte in range is one of those or `.`.
-/
private def isLabel (s : String) (i j : Nat) : Bool :=
  i < j && j - i ≤ 63 && Bytes.get s i != '-'.toUInt8 && Bytes.get s (j - 1) != '-'.toUInt8

/--
Whether the labels of `s` from `i` to `stop` are all valid (`isLabel`), each ending at a `.`.
-/
private def allLabels (s : String) (i stop : Nat) : Bool :=
  let e := min (Bytes.findByte s '.'.toUInt8 i) stop
  if h : i < e ∧ isLabel s i e then
    if h' : e < stop then allLabels s (e + 1) stop else true
  else
    false
termination_by stop - i
decreasing_by have := h.1; omega

/--
Whether the label of `s` from `i` to `j` is a number to the resolver (`URI.endsInNumber`): decimal
digits, or `0x` followed by hex digits.
-/
private def isNumericLabel (s : String) (i j : Nat) : Bool :=
  let isDigit (b : UInt8) := '0'.toUInt8 ≤ b && b ≤ '9'.toUInt8
  (i < j && Bytes.allBetween isDigit s i j) ||
    (i + 2 ≤ j && Bytes.get s i == '0'.toUInt8 &&
      (Bytes.get s (i + 1) == 'x'.toUInt8 || Bytes.get s (i + 1) == 'X'.toUInt8) &&
      Bytes.allBetween (fun b => isDigit b || ('a'.toUInt8 ≤ b && b ≤ 'f'.toUInt8) ||
        ('A'.toUInt8 ≤ b && b ≤ 'F'.toUInt8)) s (i + 2) j)

/--
Whether the port of a `Host` value, the bytes of `s` after its `:`, is accepted: empty, or decimal
digits whose value without leading zeros has at most 5 digits and is at most 65535.
-/
private def isPort (s : String) (i : Nat) : Bool :=
  let n := s.utf8ByteSize
  Bytes.allBetween (fun b => '0'.toUInt8 ≤ b && b ≤ '9'.toUInt8) s i n &&
    let start := Bytes.skipZeros s i n
    n - start ≤ 5 && digitsValue s start n 0 ≤ 65535
where
  digitsValue (s : String) (i n acc : Nat) : Nat :=
    if i < n then digitsValue s (i + 1) n (acc * 10 + (Bytes.get s i - '0'.toUInt8).toNat) else acc
  termination_by n - i

/--
Whether `Header.Host.parse` accepts `v`. A host name starting with a letter, with an optional port,
is decided on its bytes; other values, such as IP literals or names with percent-encoding, are
parsed.
-/
def isValid (v : Header.Value) : Bool :=
  let s := v.value
  let first := Bytes.get s 0
  let isHostByte (b : UInt8) :=
    ('a'.toUInt8 ≤ b && b ≤ 'z'.toUInt8) || ('A'.toUInt8 ≤ b && b ≤ 'Z'.toUInt8) ||
      ('0'.toUInt8 ≤ b && b ≤ '9'.toUInt8) || b == '-'.toUInt8 || b == '_'.toUInt8 ||
      b == '.'.toUInt8
  let colon := Bytes.findByte s ':'.toUInt8 0
  if (('a'.toUInt8 ≤ first && first ≤ 'z'.toUInt8) ||
      ('A'.toUInt8 ≤ first && first ≤ 'Z'.toUInt8)) &&
      Bytes.allBetween isHostByte s 0 colon then
    -- The name without one trailing `.`, which adds no label.
    let stop := if Bytes.get s (colon - 1) == '.'.toUInt8 then colon - 1 else colon
    let lastLabel := Bytes.findLastByte s '.'.toUInt8 0 stop
    stop ≤ 253 && allLabels s 0 stop && !isNumericLabel s lastLabel stop &&
      (colon == s.utf8ByteSize || isPort s (colon + 1))
  else
    (Header.Host.parse v).isSome

end Std.Http.Protocol.H1.Host
