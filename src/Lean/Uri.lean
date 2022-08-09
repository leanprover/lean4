/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Lovett
-/
import Lean
open Lean Parsec

namespace Uri
namespace UriEscape

def textData : Parsec Char := satisfy fun c =>
  '%' ≠ c

def hexDigitToNat (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then (c.toNat - 'a'.toNat + 10)
  else (c.toNat - 'A'.toNat + 10)

def digitsToNat (base : Nat) (digits : Array Nat) : Nat :=
  digits.foldl (λ r d => r * base + d) 0

@[inline]
partial def exactlyNCore (p : Parsec α) (n : Nat) (acc : Array α) : Parsec $ Array α :=
  if n > 0 then do
    exactlyNCore p (n-1) (acc.push $ ←p)
  else
    pure acc

@[inline]
def exactlyN (p : Parsec α) (n : Nat) : Parsec $ Array α := exactlyNCore p n #[]

def escaped : Parsec ByteArray := do
  skipString "%"
  let c? ← peek?
  if c? = some '%' then
    skip
    return ByteArray.mk #[ 0x25 ]
  let charCode := digitsToNat 16 (← exactlyN (hexDigitToNat <$> hexDigit) 2)
  return ByteArray.mk #[ charCode.toUInt8 ]

def escapedSequence : Parsec String := do
  let mut codes := ByteArray.empty
  for a in (← many1 escaped) do
    codes := codes ++ a
  return String.fromUTF8Unchecked codes

def unescaped : Parsec String := many1Chars textData
def uriChunk : Parsec String := escapedSequence <|> unescaped
def parsedUri : Parsec (Array String) := many1 uriChunk

def decodeUri (uri : String) := do
  match parsedUri uri.mkIterator with
  | Parsec.ParseResult.success _ res => Except.ok (join res)
  | Parsec.ParseResult.error it err  => Except.error s!"offset {it.pos}: {err}"
  where
  join (l : Array String) : String :=
    l.foldl (fun r s => r ++ s) ""

/- https://datatracker.ietf.org/doc/html/rfc3986/#page-12 -/
def rfc3986ReservedChars : List Char := [ ';', ':', '?', '#', '[', ']', '@', '&', '=', '+', '$', ',', '!', '\'', '(', ')', '*', '%' ]

def uriEscapeAsciiChar (c : Char) : String :=
  if (rfc3986ReservedChars.contains c) then
    "%" ++ smallCharToHex c
  else if ((Char.toNat c) < 127) then
    c.toString
  else
    c.toString.toUTF8.foldl (fun s c => s ++ "%" ++ (smallCharToHex (Char.ofNat c.toNat))) ""
  where
  smallCharToHex (c : Char) : String :=
    let n  := Char.toNat c;
    let d2 := n / 16;
    let d1 := n % 16;
    hexDigitRepr d2 ++ hexDigitRepr d1
end UriEscape


def toFileUri (s : String) : String :=
  let uri := s.foldl (fun s c => s ++ UriEscape.uriEscapeAsciiChar c) ""
  if uri.startsWith "/" then
    "file://" ++ uri
  else
    "file:///" ++ uri

def pathToUri (fname : System.FilePath) : String :=
  toFileUri fname.normalize.toString

def unescapeUri (s: String) : Option String := Id.run do
  match (← UriEscape.decodeUri s) with
  | Except.ok res => some res
  | Except.error _ => none

def fileUriToPath (uri : String) : Option System.FilePath :=
  if !uri.startsWith "file:///" then
    none
  else do
    let mut p := uri.drop "file://".length
    if System.Platform.isWindows then
      p := uri.drop "file:///".length
    match unescapeUri p with
    | some s => some ⟨s⟩
    | none => none

end Uri
