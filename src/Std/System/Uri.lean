/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Lovett
-/

namespace System
namespace Uri
namespace UriEscape

/- https://www.ietf.org/rfc/rfc3986.txt -/
@[inline] def zero : UInt8 := '0'.toNat.toUInt8
@[inline] def nine : UInt8 := '9'.toNat.toUInt8
@[inline] def lettera : UInt8 := 'a'.toNat.toUInt8
@[inline] def letterf : UInt8 := 'f'.toNat.toUInt8
@[inline] def letterA : UInt8 := 'A'.toNat.toUInt8
@[inline] def letterF : UInt8 := 'F'.toNat.toUInt8

/-- Decode %HH escapings in the given string. Note that sometimes a consecutive
sequence of multiple escapings can represet a utf-8 encoded sequence for
a single unicode code point and these will also be decoded correctly. -/
def decodeUri (uri : String) : String := Id.run do
  let mut decoded : ByteArray := ByteArray.empty
  let rawBytes := uri.toUTF8
  let len := rawBytes.size
  let mut i := 0
  let percent := '%'.toNat.toUInt8
  while i < len do
    let c := rawBytes[i]!
    (decoded, i) := if c == percent && i + 1 < len then
      let h1 := rawBytes[i + 1]!
      if let some hd1 := hexDigitToUInt8? h1 then
        if i + 2 < len then
          let h2 := rawBytes[i + 2]!
          if let some hd2 := hexDigitToUInt8? h2 then
            -- decode the hex digits into a byte.
            (decoded.push (hd1 * 16 + hd2), i + 3)
          else
            -- not a valid second hex digit so keep the original bytes
            (((decoded.push c).push h1).push h2, i + 3)
        else
          -- hit end of string, there is no h2.
          ((decoded.push c).push h1, i + 2)
      else
        -- not a valid hex digit so keep the original bytes
        ((decoded.push c).push h1, i + 2)
    else
      (decoded.push c, i + 1)
  return String.fromUTF8Unchecked decoded
where hexDigitToUInt8? (c : UInt8) : Option UInt8 :=
  if zero ≤ c ∧ c ≤ nine then some (c - zero)
  else if lettera ≤ c ∧ c ≤ letterf then some (c - lettera + 10)
  else if letterA ≤ c ∧ c ≤ letterF then some (c - letterA + 10)
  else none

def rfc3986ReservedChars : List Char := [ ';', ':', '?', '#', '[', ']', '@', '&', '=', '+', '$', ',', '!', '\'', '(', ')', '*', '%', ' ' ]

def uriEscapeAsciiChar (c : Char) : String :=
  if rfc3986ReservedChars.contains c || c < ' ' then
    "%" ++ uInt8ToHex c.toNat.toUInt8
  else if (Char.toNat c) < 127 then
    c.toString
  else
    c.toString.toUTF8.foldl (fun s b => s ++ "%" ++ (uInt8ToHex b)) ""
where
  uInt8ToHex (c : UInt8) : String :=
    let d2 := c / 16;
    let d1 := c % 16;
    (hexDigitRepr d2.toNat ++ hexDigitRepr d1.toNat).toUpper
end UriEscape

/-- Replaces special characters in the given Uri with %HH Uri escapings. -/
def escapeUri (uri: String) : String :=
  uri.foldl (fun s c => s ++ UriEscape.uriEscapeAsciiChar c) ""

/-- Replaces all %HH Uri escapings in the given string with their
corresponding unicode code points.  Note that sometimes a consecutive
sequence of multiple escapings can represet a utf-8 encoded sequence for
a single unicode code point and these will also be decoded correctly. -/
def unescapeUri (s: String) : String :=
  UriEscape.decodeUri s

/-- Convert the given FilePath to a "file:///encodedpath" Uri
where the encoded path may contain %xx escaping when needed. -/
def pathToUri (fname : System.FilePath) : String := Id.run do
  let mut uri := fname.normalize.toString
  if System.Platform.isWindows then
    uri := uri.map (fun c => if c == '\\' then '/' else c)
  uri := uri.foldl (fun s c => s ++ UriEscape.uriEscapeAsciiChar c) ""
  let result := if uri.startsWith "/" then "file://" ++ uri else "file:///" ++ uri
  result

/-- Convert the given uri to a FilePath stripping the 'file://' prefix,
ignoring the optional host name and unescaping any %HH escaped chars.
It is also careful to create correct paths on Windows that start with a drive letter. -/
def fileUriToPath? (uri : String) : Option System.FilePath := Id.run do
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

end Uri
end System
