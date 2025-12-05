/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.String
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
Returns the total size of the chunk including data and formatted extensions. Extensions are formatted
as: ;name=value;name=value Plus 2 bytes for \r\n at the end.
-/
def size (chunk : Chunk) : Nat :=
  let extensionsSize := chunk.extensions.foldl (fun acc (name, value) => acc + name.length + (value.map (fun v => v.length + 1) |>.getD 0) + 1) 0
  chunk.data.size + extensionsSize + (if extensionsSize > 0 then 2 else 0)

instance : Encode .v11 Chunk where
  encode buffer chunk :=
    let chunkLen := chunk.data.size
    let exts := chunk.extensions.foldl (fun acc (name, value)  => acc ++ ";" ++ name ++ (value.map (fun x => "=" ++ x) |>.getD "")) ""
    let size := Nat.toDigits 16 chunkLen |>.toArray |>.map Char.toUInt8 |> ByteArray.mk
    buffer.append #[size, exts.toUTF8, "\r\n".toUTF8, chunk.data, "\r\n".toUTF8]

end Chunk
