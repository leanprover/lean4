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
  extensions : Array (String × Option String) := #[]
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
def withExtension (chunk : Chunk) (key : String) (value : String) : Chunk :=
  { chunk with extensions := chunk.extensions.push (key, some value) }

/--
Interprets the chunk data as a UTF-8 encoded string.
-/
def toString? (chunk : Chunk) : Option String :=
  String.fromUTF8? chunk.data

instance : Encode .v11 Chunk where
  encode buffer chunk :=
    let chunkLen := chunk.data.size
    let exts := chunk.extensions.foldl (fun acc (name, value)  => acc ++ ";" ++ name ++ (value.elim "" (fun x => "=" ++ x))) ""
    let size := Nat.toDigits 16 chunkLen |>.toArray |>.map Char.toUInt8 |> ByteArray.mk
    buffer.append #[size, exts.toUTF8, "\r\n".toUTF8, chunk.data, "\r\n".toUTF8]

/--
Returns the total wire format size of the chunk in bytes. This includes the hex-encoded data length
prefix, formatted extensions (`;name=value`), CRLF after the size line, the data itself, and the
trailing CRLF.
-/
def wireFormatSize (chunk : Chunk) : Nat :=
  let hexSize := (Nat.toDigits 16 chunk.data.size).length
  let extensionsSize := chunk.extensions.foldl (fun acc (name, value) => acc + name.length + (value.map (fun v => v.length + 1) |>.getD 0) + 1) 0
  hexSize + extensionsSize + 2 + chunk.data.size + 2

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
    let buffer := buffer.write "0\r\n".toUTF8

    let buffer := trailer.headers.fold (init := buffer) fun acc key values =>
      values.foldl (init := acc) fun acc value =>
        acc.write (key ++ ": " ++ value ++ "\r\n").toUTF8

    buffer.write "\r\n".toUTF8

end Trailer
