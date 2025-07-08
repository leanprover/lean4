/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Internal.Http.Data.Headers
import Std.Internal.Http.Data.Version
import Std.Internal.Http.Data.Status
import Std.Sync

namespace Std
namespace Internal
namespace Http
namespace Data

structure ByteStream where
  data : Channel ByteArray
  want : IO.Ref Bool

inductive Body where
  | zero
  | bytes (data : ByteArray)
  | stream (channel : ByteStream)

namespace Body

def getContentType (body : Body) : String :=
  match body with
  | zero => ""
  | .bytes _ => "application/octet-stream"
  | .stream _ => "application/octet-stream"

/-- Get content length for a body (if known) -/
def getContentLength (body : Body) : Option Nat :=
  match body with
  | zero => some 0
  | .bytes data => some data.size
  | .stream _ => none

def withBodyHeaders (body : Body) (headers : Headers) : Headers :=
  let headers' := headers.insert "Content-Type" (body.getContentType)
  match body.getContentLength with
  | some len => headers'.insert "Content-Length" (toString len)
  | none => headers'.insert "Transfer-Encoding" "chunked"
