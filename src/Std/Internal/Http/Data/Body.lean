/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init
public import Std.Internal.Http.Data.Body.Length
public import Std.Internal.Http.Data.Body.ByteStream

public section

open Std Internal IO Async

namespace Std
namespace Http

/--
Inductive type for HTTP body content
-/
inductive Body where
  | zero
  | bytes (data : ByteArray)
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

def close (body : Body) : Async Unit :=
  match body with
  | .stream channel => channel.close
  | _ => pure ()

instance : Coe String Body where
  coe := .bytes ∘ String.toUTF8

instance : Coe Body.ByteStream Body where
  coe := .stream

instance : Coe Body Body where
  coe := id

@[inline]
protected partial def forIn
  {β : Type} (body : Body) (acc : β)
  (step : ByteArray → β → Async (ForInStep β)) :
  Async β := do
    let rec @[specialize] loop (stream : ByteStream) (acc : β) : Async β := do
      if let some data ← stream.recv then
        match ← step data.toByteArray acc with
        | .done res => pure res
        | .yield res => loop stream res
      else
        return acc

    match body with
    | .zero => pure acc
    | .bytes data =>
      match ← step data acc with
      | .done x => pure x
      | .yield x => pure x
    | .stream strea => loop strea acc

instance : ForIn Async Body ByteArray where
  forIn := Body.forIn
