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

/-!
# HTTP/1.1 Events

This module defines the events that can occur during HTTP/1.1 message processing,
including header completion and control/error signals.
-/

namespace Std.Http.Protocol.H1

set_option linter.all true

/--
Events emitted during HTTP message processing.
-/
inductive Event (dir : Direction)
  /--
  Indicates that all headers have been successfully parsed.
  -/
  | endHeaders (head : Message.Head dir)

  /--
  Signals that additional input data is required to continue processing.
  -/
  | needMoreData (size : Option Nat)

  /--
  Indicates a failure during parsing or processing.
  -/
  | failed (err : Error)

  /--
  Requests that the connection be closed.
  -/
  | close

  /--
  The body should be closed.
  -/
  | closeBody

  /--
  Indicates that a response is required.
  -/
  | needAnswer

  /--
  Indicates readiness to process the next message.
  -/
  | next

  /--
  Signals that an `Expect: 100-continue` decision is pending.
  -/
  | «continue»
deriving Inhabited, Repr
