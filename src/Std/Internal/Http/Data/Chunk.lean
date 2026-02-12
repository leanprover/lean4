/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.String
public import Std.Data.HashMap
public import Std.Internal.Http.Internal


public section

/-!
# Chunk

This module defines the `Chunk` type, which represents a chunk of data from a request or response.
-/

namespace Std.Http

open Internal

set_option linter.all true

/--
Checks if a character is a valid HTTP token character per RFC 9110 §5.6.2.
Token characters include alphanumerics and the following: `!#$%&'*+-.^_`|~`
-/
def isTokenCharacter (c : Char) : Bool :=
  c.toNat < 128 && Nat.testBit 0x57ffffffc7fffffe03ff6cfa00000000 c.toNat

/--
Proposition that asserts all characters in a string are valid token characters and that it is
non-empty.
-/
abbrev IsValidExtensionName (s : String) : Prop :=
  s.toList.all isTokenCharacter ∧ ¬s.isEmpty

/--
A validated chunk extension name that ensures all characters conform to HTTP token standards
per RFC 9110 §5.6.2. Extension names appear in chunked transfer encoding as key-value metadata.
-/
structure ExtensionName where
  /--
  The extension name string.
  -/
  value : String

  /--
  The proof that it's a valid extension name.
  -/
  validExtensionName : IsValidExtensionName value := by decide
deriving Repr, DecidableEq, BEq

namespace ExtensionName

instance : Hashable ExtensionName where
  hash x := Hashable.hash x.value

instance : Inhabited ExtensionName where
  default := ⟨"x", by native_decide⟩

/--
Attempts to create an `ExtensionName` from a `String`, returning `none` if the string contains
invalid characters or is empty.
-/
def ofString? (s : String) : Option ExtensionName :=
  if h : IsValidExtensionName s then
    some ⟨s, h⟩
  else
    none

/--
Creates an `ExtensionName` from a string, panicking with an error message if the string contains
invalid characters or is empty.
-/
def ofString! (s : String) : ExtensionName :=
  if h : IsValidExtensionName s then
    ⟨s, h⟩
  else
    panic! ("invalid extension name: " ++ s.quote)

instance : ToString ExtensionName where
  toString name := name.value

end ExtensionName

/--
Represents a chunk of data with optional extensions (key-value pairs).
-/
structure Chunk where

  /--
  The byte data contained in this chunk.
  -/
  data : ByteArray

  /--
  Optional metadata associated with this chunk as key-value pairs. Keys are strings, values are
  optional strings.
  -/
  extensions : Array (ExtensionName × Option String) := #[]
deriving Inhabited

namespace Chunk

/--
Quotes an extension value if it contains non-token characters, otherwise returns it as-is.
-/
def quoteExtensionValue (s : String) : String :=
  if s.any (fun c => !isTokenCharacter c) then s.quote else s

/--
An empty chunk with no data and no extensions.
-/
def empty : Chunk :=
  { data := .empty, extensions := #[] }

/--
Creates a simple chunk without extensions.
-/
def ofByteArray (data : ByteArray) : Chunk :=
  { data := data, extensions := #[] }

/--
Adds an extension to a chunk.
-/
def withExtension (chunk : Chunk) (key : ExtensionName) (value : String) : Chunk :=
  { chunk with extensions := chunk.extensions.push (key, some value) }

/--
Interprets the chunk data as a UTF-8 encoded string.
-/
def toString? (chunk : Chunk) : Option String :=
  String.fromUTF8? chunk.data

instance : Encode .v11 Chunk where
  encode buffer chunk :=
    let chunkLen := chunk.data.size
    let exts := chunk.extensions.foldl (fun acc (name, value)  =>
      acc ++ ";" ++ name.value.toLower ++ (value.elim "" (fun x => "=" ++ quoteExtensionValue x))) ""
    let size := Nat.toDigits 16 chunkLen |>.toArray |>.map Char.toUInt8 |> ByteArray.mk
    buffer.append #[size, exts.toUTF8, "\r\n".toUTF8, chunk.data, "\r\n".toUTF8]

end Chunk

/--
Trailer headers sent after the final chunk in HTTP/1.1 chunked transfer encoding.
Per RFC 9112 §7.1.2, trailers allow the sender to include additional metadata after
the message body, such as message integrity checks or digital signatures.
-/
structure Trailer where
  /--
  The trailer header fields as key-value pairs.
  -/
  headers : HashMap String (Array String) := .emptyWithCapacity
deriving Inhabited

namespace Trailer

/--
Creates an empty trailer with no headers.
-/
def empty : Trailer :=
  { headers := .emptyWithCapacity }

/--
Adds a header field to the trailer.
-/
def header (trailer : Trailer) (key : String) (value : String) : Trailer :=
  let headers := trailer.headers.alter key (fun values => some <| (values.getD #[]).push value)
  { trailer with headers }

instance : Encode .v11 Trailer where
  encode buffer trailer :=
    let terminalChunk := "0\r\n".toUTF8
    let trailerFields := trailer.headers.fold (init := ByteArray.empty) fun acc key values =>
      values.foldl (init := acc) fun acc value =>
        acc ++ (key ++ ": " ++ value ++ "\r\n").toUTF8
    buffer.append #[terminalChunk, trailerFields, "\r\n".toUTF8]

end Trailer
