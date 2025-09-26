/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.String
public import Init.Data.ByteArray

public section

namespace Std
namespace Http
namespace Util

set_option linter.all true

/--
A `Buffer` is a type alias for `ByteArray` that provides a convenient interface for working with binary data.
-/
@[expose]
def Buffer := ByteArray

namespace Buffer

/--
Creates a buffer with minimum size of `1024` if not specified.
-/
@[inline]
def empty (capacity := 1024) : Buffer :=
  ByteArray.emptyWithCapacity capacity

/--
Writes a `ByteArray` to the `Buffer`
-/
@[inline]
def write (buffer : Buffer) (data : ByteArray) : Buffer :=
  buffer.append data

/--
Writes a `Char` to the `Buffer`
-/
@[inline]
def writeChar (buffer : Buffer) (data : Char) : Buffer :=
  buffer.push data.toUInt8

/--
Writes a `String` to the `Buffer`
-/
@[inline]
def writeString (buffer : Buffer) (data : String) : Buffer :=
  buffer.append data.toUTF8
