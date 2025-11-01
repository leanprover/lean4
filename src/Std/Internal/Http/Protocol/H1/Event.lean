/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time
public import Std.Internal.Http.Data
public import Std.Internal.Http.Internal
public import Std.Internal.Http.Protocol.H1.Parser
public import Std.Internal.Http.Protocol.H1.Config
public import Std.Internal.Http.Protocol.H1.Message
public import Std.Internal.Http.Protocol.H1.Error

public section

namespace Std.Http.Protocol.H1

/--
Events that can occur during HTTP message processing.
-/
inductive Event (dir : Direction)
  /--
  Event received when chunk extension data is encountered in chunked encoding.
  -/
  | chunkExt (ext : Array (String × Option String))

  /--
  Event received when the headers end.
  -/
  | endHeaders (head : Message.Head dir)

  /--
  Event received when some data arrives from the received message.
  -/
  | gotData (final : Bool) (data : ByteSlice)

  /--
  Need more data is an event that arrives when the input ended and it requires more
  data to continue
  -/
  | needMoreData (size : Option Nat)

  /--
  Event received when parsing or processing fails with an error message.
  -/
  | failed (err : Error)

  /--
  Event received when connection should be closed.
  -/
  | close

  /--
  Awaiting the next message
  -/
  | next
deriving Inhabited, Repr
