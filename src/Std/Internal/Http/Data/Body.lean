/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Http.Data.Body.Length
public import Std.Internal.Http.Data.Body.ByteStream

public section

/-!
# Body

This module defines the `Body` type, which represents the body of a HTTP request or response.
-/

namespace Std.Http

open Std Internal IO Async

set_option linter.all true

set_option linter.all true

/--
Type that represents the body of a request or response with streams of bytearrays or bytearrays of fixed
size.
-/
inductive Body where
  /--
  Empty body with no content
  -/
  | zero

  /--
  Body containing raw byte data stored in memory
  -/
  | bytes (data : ByteArray)

  /--
  Body containing streaming data from a byte stream channel
  -/
  | stream (channel : Body.ByteStream)
deriving Inhabited

namespace Body

/--
Get content length of a body (if known).
-/
def getContentLength (body : Body) : Length :=
  match body with
  | zero => .fixed 0
  | .bytes data => .fixed data.size
  | .stream _ => .chunked

/--
Close the body and release any associated resources. For streaming bodies, this closes the underlying
channel. For other body types, this is a no-op.
-/
def close (body : Body) : Async Unit :=
  match body with
  | .stream channel => channel.close
  | _ => pure ()

instance : Coe String Body where
  coe := .bytes ∘ String.toUTF8

instance : Coe ByteArray Body where
  coe := .bytes

instance : Coe Body.ByteStream Body where
  coe := .stream

/--
Iterate over the body content in chunks, processing each ByteArray chunk with the given step function.
-/
@[inline]
protected partial def forIn
  {β : Type} (body : Body) (acc : β)
  (step : Chunk → β → Async (ForInStep β)) :
  Async β := do
    match body with
    | .zero => pure acc
    | .bytes data => return (← step (Chunk.mk data #[]) acc).value
    | .stream stream' => ByteStream.forIn stream' acc step

instance : ForIn Async Body Chunk where
  forIn := Body.forIn


/--
Collect all data from the body into a single `ByteArray`. This reads the entire body content into memory,
so use with caution for large bodies as it may consume significant memory.
-/
def collectByteArray (body : Body) : Async ByteArray := do
  let mut result := .empty
  for x in body do result := result ++ x.data
  return result

/--
Collect all data from the body into a single `String`. This reads the entire body content into memory,
so use with caution for large bodies as it may consume significant memory. If it's a valid UTF8 string
then it will return `some` otherwise `none`.
-/
def collectString (body : Body) : Async (Option String) := do
  let mut result := .empty
  for x in body do result := result ++ x.data
  return String.fromUTF8? result
