/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Lovett
-/

namespace System
namespace Uri
namespace UriEscape

def hexDigitToNat (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Decode %HH escapings in the given string. Note that sometimes a consecutive
sequence of multiple escapings can represet a utf-8 encoded sequence for
a single unicode code point and these will also be decoded correctly. -/
def decodeUri (uri : String) : String := Id.run do
  let mut decoded : ByteArray := ByteArray.empty
  let len := uri.utf8ByteSize
  let mut i := uri.mkIterator
  while i.2.byteIdx < len do
    let c := i.curr
    if c == '%' && i.2.byteIdx + 1 < len then
      let h1 : Char := i.next.curr
      if h1 == '%' then
        -- this is an escaped '%%' which should become a single percent.
        decoded := decoded.push 37 -- %
        i := i.next.next
      else if i.2.byteIdx + 2 < len then
         -- should have %HH where HH are hex digits, if they are not
         -- valid hex digits then just repeat whatever sequence of chars
         -- we found here.
         let h2 := i.next.next.curr
         let hc : Option UInt8 := match hexDigitToNat h1 with
         | none => none
         | some hd1 =>
           match hexDigitToNat h2 with
           | some hd2 => (hd1 * 16 + hd2).toUInt8
           | none => none
         decoded := match hc with
         | some b => decoded.push b
         | none => decoded.push 37 ++ h1.toString.toUTF8 ++ h2.toString.toUTF8
         i := i.nextn 3
      else
        decoded := decoded.push 37 ++ h1.toString.toUTF8
        i := i.next.next

    else
      decoded := decoded.append c.toString.toUTF8
      i := i.next
   return String.fromUTF8Unchecked decoded

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

/-- Convert the given file name to a "file:///encodedpath" Uri
where the encoded path may contain %xx escaping when needed. -/
def toFileUri (s : String) : String := Id.run do
  let mut uri := s
  if System.Platform.isWindows then
    uri := uri.map (fun c => if c == '\\' then '/' else c)
  uri := uri.foldl (fun s c => s ++ UriEscape.uriEscapeAsciiChar c) ""
  if uri.startsWith "/" then
    "file://" ++ uri
  else
    "file:///" ++ uri

/-- Convert the given FilePath to a "file:///encodedpath" Uri
where the encoded path may contain %xx escaping when needed. -/
def pathToUri (fname : System.FilePath) : String := Id.run do
  toFileUri fname.normalize.toString

/-- Replaces all %HH Uri escapings in the given string with their
corresponding unicode code points.  Note that sometimes a consecutive
sequence of multiple escapings can represet a utf-8 encoded sequence for
a single unicode code point and these will also be decoded correctly. -/
def unescapeUri (s: String) : String :=
  UriEscape.decodeUri s

/-- Takes a "file://[hostname]/path" uri and returns the unescaped
path minus the uri scheme prefix and optional hostname. -/
def fromFileUri? (uri : String) : Option String := Id.run do
  if !uri.startsWith "file://" then
    none
  else
    let mut p := (unescapeUri uri).drop "file://".length
    p := p.dropWhile (λ c => c != '/') -- drop the hostname.
    -- on windows the path "/c:/temp" needs to become "c:/temp"
    -- but only when it is a valid drive letter.
    if System.Platform.isWindows &&
      p.length > 3 &&
      "/" == (p.take 1) &&
      ((p.drop 1).take 1).all Char.isAlpha &&
      ":" == ((p.drop 2).take 1)  then
      p := p.drop 1
    some p

def fileUriToPath? (uri : String) : Option System.FilePath :=
  match fromFileUri? uri with
  | some p => some ⟨p⟩
  | none => none

end Uri
end System
