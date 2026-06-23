/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Internal
public import Std.Http.Data.Headers
public meta import Std.Http.Internal.String

public section

/-!
# Chunk

This module defines the `Chunk` type, which represents a chunk of data from a request or response.

Reference: https://www.rfc-editor.org/rfc/rfc9112.html#section-7.1
-/

namespace Std.Http
open Internal Char

set_option linter.all true

namespace Chunk

/--
A proposition stating that `s` is a valid chunk-extension name: every character in `s` is an
HTTP token character and `s` is non-empty.

Reference: https://httpwg.org/specs/rfc9112.html#chunked.extension
-/
abbrev IsValidExtensionName (s : String) : Prop :=
  isToken s

/--
A validated chunk extension name that ensures all characters conform to HTTP standards
per RFC 9112 §7.1.1. Extension names appear in chunked transfer encoding as key-value metadata.

Reference: https://httpwg.org/specs/rfc9112.html#chunked.extension
-/
structure ExtensionName where
  /--
  The extension name string.
  -/
  value : String

  /--
  The proof that it's a valid extension name.
  -/
  isValidExtensionName : IsValidExtensionName value := by decide
deriving Repr, DecidableEq, BEq

instance : Hashable ExtensionName where
  hash x := Hashable.hash x.value

instance : Inhabited ExtensionName where
  default := ⟨"_", by decide⟩

instance : ToString ExtensionName where
  toString name := name.value

namespace ExtensionName

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
  match ofString? s with
  | some res => res
  | none => panic! ("invalid extension name: " ++ s.quote)

end ExtensionName

/--
A proposition asserting that `s` is a valid extension value, meaning every character passes
`Char.quotedStringChar` (i.e. is `qdtext` or a valid `quoted-pair` payload).

Reference: https://httpwg.org/specs/rfc9112.html#chunked.extension
-/
abbrev IsValidExtensionValue (s : String) : Prop :=
  s.toList.all Char.quotedStringChar

/--
A validated chunk extension value that ensures all characters conform to HTTP standards per RFC 9112 §7.1.1.
Extension values appear in chunked transfer encoding as metadata associated with extension names.

Note: UTF-8 encoding is not supported. The quoting mechanism is strict and only permits escaping
specific values. Additionally, the library does not support obs-text, which means certain UTF-8
characters or values outside of token, qdtext, and the limited set of escapable characters cannot be
encoded.

Reference: https://httpwg.org/specs/rfc9112.html#chunked.extension
-/
structure ExtensionValue where
  /--
  The extension value string.
  -/
  value : String

  /--
  The proof that it's a valid extension value.
  -/
  isValidExtensionValue : IsValidExtensionValue value := by decide
deriving Repr, DecidableEq, BEq

namespace ExtensionValue

instance : Inhabited ExtensionValue where
  default := ⟨"", by decide⟩

instance : ToString ExtensionValue where
  toString v := v.value

/--
Quotes an extension value if it contains non-token characters, otherwise returns it as-is.
-/
def quote (s : ExtensionValue) : String :=
  quoteHttpString s.value s.isValidExtensionValue

/--
Attempts to create an `ExtensionValue` from a `String`, returning `none` if the string contains
characters that cannot be encoded as an HTTP quoted-string.
-/
def ofString? (s : String) : Option ExtensionValue :=
  if h : IsValidExtensionValue s then
    some ⟨s, h⟩
  else
    none

/--
Creates an `ExtensionValue` from a string, panicking with an error message if the string contains
characters that cannot be encoded as an HTTP quoted-string.
-/
def ofString! (s : String) : ExtensionValue :=
  match ofString? s with
  | some res => res
  | none => panic! ("invalid extension value: " ++ s.quote)

end Chunk.ExtensionValue

/--
Represents a chunk of data with optional extensions (key-value pairs).

The interpretation of a chunk depends on the protocol layer consuming it:

- HTTP/1.1: The zero-size wire encoding (`0\r\n\r\n`) is reserved
  exclusively as the `last-chunk` terminator. The HTTP/1.1 writer silently discards
  any empty chunk (including its extensions) rather than emitting a premature
  end-of-body signal. `Encode.encode` on a `Chunk.empty` value does produce
  `"0\r\n\r\n"`, but that path bypasses the writer's framing logic.

- HTTP/2 (not yet implemented): Chunked transfer encoding does not exist; HTTP/2 uses DATA
  frames instead. This type is specific to the HTTP/1.1 wire format.

Reference: https://httpwg.org/specs/rfc9112.html#rfc.section.7.1
-/
structure Chunk where

  /--
  The byte data contained in this chunk.
  -/
  data : ByteArray

  /--
  Optional metadata associated with this chunk as key-value pairs. Keys are validated
  `Chunk.ExtensionName` values, values are optional strings.
  -/
  extensions : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue) := #[]
deriving Inhabited

namespace Chunk

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
def insertExtension (chunk : Chunk) (key : Chunk.ExtensionName) (value : ExtensionValue) : Chunk :=
  { chunk with extensions := chunk.extensions.push (key, some value) }

/--
Interprets the chunk data as a UTF-8 encoded string.
-/
def toString? (chunk : Chunk) : Option String :=
  String.fromUTF8? chunk.data

instance : Encode .v11 Chunk where
  encode buffer chunk :=
    let chunkLen := chunk.data.size
    let exts := chunk.extensions.foldl (fun acc (name, value) =>
      acc ++ ";" ++ name.value ++ (value.elim "" (fun x => "=" ++ x.quote))) ""
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
  headers : Headers
deriving Inhabited

namespace Trailer

/--
Creates an empty trailer with no headers.
-/
def empty : Trailer :=
  { headers := .empty }

/--
Inserts a trailer header field.
-/
@[inline]
def insert (trailer : Trailer) (name : Header.Name) (value : Header.Value) : Trailer :=
  { headers := trailer.headers.insert name value }

/--
Inserts a trailer header field from string name and value, panicking if either is invalid.
-/
@[inline]
def insert! (trailer : Trailer) (name : String) (value : String) : Trailer :=
  { headers := trailer.headers.insert! name value }

/--
Retrieves the first value for the given trailer header name.
Returns `none` if absent.
-/
@[inline]
def get? (trailer : Trailer) (name : Header.Name) : Option Header.Value :=
  trailer.headers.get? name

/--
Retrieves all values for the given trailer header name.
Returns `none` if absent.
-/
@[inline]
def getAll? (trailer : Trailer) (name : Header.Name) : Option (Array Header.Value) :=
  trailer.headers.getAll? name

/--
Checks if a trailer header with the given name exists.
-/
@[inline]
def contains (trailer : Trailer) (name : Header.Name) : Bool :=
  trailer.headers.contains name

/--
Removes a trailer header with the given name.
-/
@[inline]
def erase (trailer : Trailer) (name : Header.Name) : Trailer :=
  { headers := trailer.headers.erase name }

/--
Gets the number of trailer headers.
-/
@[inline]
def size (trailer : Trailer) : Nat :=
  trailer.headers.size

/--
Checks if the trailer has no headers.
-/
@[inline]
def isEmpty (trailer : Trailer) : Bool :=
  trailer.headers.isEmpty

/--
Merges two trailers, accumulating values for duplicate keys from both.
-/
def merge (t1 t2 : Trailer) : Trailer :=
  { headers := t1.headers.merge t2.headers }

/--
Converts the trailer headers to a list of key-value pairs.
-/
def toList (trailer : Trailer) : List (Header.Name × Header.Value) :=
  trailer.headers.toList

/--
Converts the trailer headers to an array of key-value pairs.
-/
def toArray (trailer : Trailer) : Array (Header.Name × Header.Value) :=
  trailer.headers.toArray

/--
Folds over all key-value pairs in the trailer headers.
-/
def fold (trailer : Trailer) (init : α) (f : α → Header.Name → Header.Value → α) : α :=
  trailer.headers.fold init f

instance : Encode .v11 Trailer where
  encode buffer trailer :=
    buffer.write "0\r\n".toUTF8
    |> (Encode.encode .v11 · trailer.headers)
    |>.write  "\r\n".toUTF8

end Trailer
