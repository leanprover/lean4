/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Async
public import Std.Internal.Http.Data.Body.Length
public import Std.Internal.Http.Data.Chunk
public import Std.Internal.Http.Data.Body.Stream
public import Std.Internal.Http.Data.Body.Full
public import Std.Internal.Http.Data.Body.Empty

public section

/-!
# Body.Writer

Writer typeclass for body-like values that can produce chunk streams.
-/

namespace Std.Http.Body
open Std Internal IO Async

set_option linter.all true

/--
Typeclass for values that can be written as HTTP body streams.
-/
class Writer (α : Type) where
  /--
  Sends a body chunk.
  -/
  send : α → Chunk → Bool → Async Unit

  /--
  Closes the writer stream.
  -/
  close : α → Async Unit

  /--
  Returns `true` when the writer stream is closed.
  -/
  isClosed : α → Async Bool

  /--
  Returns `true` when a consumer is waiting for data.
  -/
  hasInterest : α → Async Bool

  /--
  Gets known stream size metadata, if available.
  -/
  getKnownSize : α → Async (Option Body.Length)

  /--
  Sets known stream size metadata.
  -/
  setKnownSize : α → Option Body.Length → Async Unit

  /--
  Selector that resolves when consumer interest appears.
  -/
  interestSelector : α → Selector Bool

namespace Writer

/--
Sends a chunk with `incomplete := false`.
-/
@[inline]
def writeChunk [Writer α] (body : α) (chunk : Chunk) : Async Unit :=
  Writer.send body chunk false

end Writer

/--
Union of writer-capable body variants.
-/
inductive AnyBody where
  /--
  Channel-backed streaming body writer.
  -/
  | outgoing (body : Outgoing)
  /--
  Fixed full-body writer handle.
  -/
  | full (body : Full)
  /--
  Always-empty writer handle.
  -/
  | empty (body : Empty)

instance : Coe Outgoing AnyBody where
  coe := .outgoing

instance : Coe Full AnyBody where
  coe := .full

instance : Coe Empty AnyBody where
  coe := .empty

instance : Coe (Response Empty) (Response AnyBody) where
  coe f := { f with }

instance : Coe (Response Full) (Response AnyBody) where
  coe f := { f with }

instance : Coe (Response Outgoing) (Response AnyBody) where
  coe f := { f with }

instance : Coe (ContextAsync (Response Empty)) (ContextAsync (Response AnyBody)) where
  coe action := do
    let response ← action
    pure (response : Response AnyBody)

instance : Coe (ContextAsync (Response Full)) (ContextAsync (Response AnyBody)) where
  coe action := do
    let response ← action
    pure (response : Response AnyBody)

instance : Coe (ContextAsync (Response Outgoing)) (ContextAsync (Response AnyBody)) where
  coe action := do
    let response ← action
    pure (response : Response AnyBody)

instance : Coe (Async (Response Empty)) (ContextAsync (Response AnyBody)) where
  coe action := do
    let response ← action
    pure (response : Response AnyBody)

instance : Coe (Async (Response Full)) (ContextAsync (Response AnyBody)) where
  coe action := do
    let response ← action
    pure (response : Response AnyBody)

instance : Coe (Async (Response Outgoing)) (ContextAsync (Response AnyBody)) where
  coe action := do
    let response ← action
    pure (response : Response AnyBody)

instance : Writer Outgoing where
  send body chunk incomplete := Outgoing.send body chunk incomplete
  close := Outgoing.close
  isClosed := Outgoing.isClosed
  hasInterest := Outgoing.hasInterest
  getKnownSize := Outgoing.getKnownSize
  setKnownSize := Outgoing.setKnownSize
  interestSelector := Outgoing.interestSelector

instance : Writer Full where
  send body chunk incomplete := Full.send body chunk incomplete
  close := Full.close
  isClosed := Full.isClosed
  hasInterest := Full.hasInterest
  getKnownSize := Full.getKnownSize
  setKnownSize := Full.setKnownSize
  interestSelector := Full.interestSelector

instance : Writer Empty where
  send _ _ _ := throw <| .userError "cannot send"
  close _ := pure ()
  isClosed _ := pure false
  hasInterest _ := pure false
  getKnownSize _ := pure (some (.fixed 0))
  setKnownSize _ _ := pure ()
  interestSelector _ := {
    tryFn := pure (some false)
    registerFn waiter := do
      let lose := pure ()
      let win promise := do
        promise.resolve (.ok false)
      waiter.race lose win
    unregisterFn := pure ()
  }

instance : Writer AnyBody where
  send
    | .outgoing body, chunk, incomplete => Writer.send body chunk incomplete
    | .full body, chunk, incomplete => Writer.send body chunk incomplete
    | .empty body, chunk, incomplete => Writer.send body chunk incomplete
  close
    | .outgoing body => Writer.close body
    | .full body => Writer.close body
    | .empty body => Writer.close body
  isClosed
    | .outgoing body => Writer.isClosed body
    | .full body => Writer.isClosed body
    | .empty body => Writer.isClosed body
  hasInterest
    | .outgoing body => Writer.hasInterest body
    | .full body => Writer.hasInterest body
    | .empty body => Writer.hasInterest body
  getKnownSize
    | .outgoing body => Writer.getKnownSize body
    | .full body => Writer.getKnownSize body
    | .empty body => Writer.getKnownSize body
  setKnownSize
    | .outgoing body, size => Writer.setKnownSize body size
    | .full body, size => Writer.setKnownSize body size
    | .empty body, size => Writer.setKnownSize body size
  interestSelector
    | .outgoing body => Writer.interestSelector body
    | .full body => Writer.interestSelector body
    | .empty body => Writer.interestSelector body

instance : Reader AnyBody where
  recv
    | .outgoing body, count => Reader.recv body count
    | .full body, count => Reader.recv body count
    | .empty body, count => Reader.recv body count
  close
    | .outgoing body => Reader.close body
    | .full body => Reader.close body
    | .empty body => Reader.close body
  isClosed
    | .outgoing body => Reader.isClosed body
    | .full body => Reader.isClosed body
    | .empty body => Reader.isClosed body
  recvSelector
    | .outgoing body => Reader.recvSelector body
    | .full body => Reader.recvSelector body
    | .empty body => Reader.recvSelector body

end Std.Http.Body
