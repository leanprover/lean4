/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init
import Std.Sync
import Std.Internal.Async
import Std.Internal.Http.Encode
import Std.Internal.Http.Data.Headers
import Std.Internal.Http.Data.Method
import Std.Internal.Http.Data.Version

open Std Internal IO Async

namespace Std
namespace Http
namespace Data

structure ByteStream where
  data : Channel (Option ByteArray)

inductive Body where
  | zero
  | bytes (data : ByteArray)
  | stream (channel : ByteStream)
deriving Inhabited

namespace Body

/--
Get content length for a body (if known)
-/
def getContentLength (body : Body) : Option Nat :=
  match body with
  | zero => some 0
  | .bytes data => some data.size
  | .stream _ => none

partial def ByteStream.recvString? (body : ByteStream) (buffer : ByteArray) : Async ByteArray := do
  match (← body.data.tryRecv) with
  | some (some bs) => recvString? body (buffer ++ bs)
  | some none => pure buffer
  | none => pure buffer

def recvString? (body : Body) : Async String :=
  match body with
  | .bytes body => pure (String.fromUTF8! body)
  | .zero => pure ""
  | .stream body => String.fromUTF8! <$> ByteStream.recvString? body .empty
