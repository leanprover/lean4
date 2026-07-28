/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Async.Select

public section

/-!
# Element streams

`Read` and `Write` in `Std.IO.Basic` move bytes. `Stream` and `Sink` are their element-generic
counterparts: a `Stream` yields values of some type `β`, a `Sink` accepts them. Channels, broadcast
receivers, and other message-oriented endpoints implement these rather than the byte classes, since
a message has no notion of a partial read or of an end-of-stream marked by zero bytes.

A `Stream` hands back a `Selector` rather than a plain action in `m`, so several streams can be
raced against one another; `Std.StreamMap` is built on that. Since `next` never mentions `m`, the
monad is an `outParam`: a source fixes the monad its `stop` runs in, rather than serving several.
-/

namespace Std.IO

open Std.Async

/--
Typeclass for sources that yield values one at a time.
-/
class Stream (m : outParam (Type → Type)) [Monad m] (α : Type) (β : outParam Type) where

  /--
  A selector that resolves once the next value is available.
  -/
  next : α → Selector β

  /--
  Stop consuming, releasing whatever claim the stream holds on its source.
  -/
  stop : α → m Unit := fun _ => pure ()

/--
Typeclass for destinations that accept values one at a time.
-/
class Sink (m : Type → Type) [Monad m] (α : Type) (β : Type) where

  /--
  Hand one value to the sink.
  -/
  write : α → β → m Unit

  /--
  Hand several values to the sink, in order.
  -/
  writeAll : α → Array β → m Unit := fun sink values => values.forM (write sink)

  /--
  Deliver whatever the sink has buffered.
  -/
  flush : α → m Unit := fun _ => pure ()

end Std.IO
