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

public section

namespace Std.Http.Protocol.H1

open Std Internal Parsec ByteArray
open Internal

/--
Connection limits configuration with validation.
-/
structure Config where
  /--
  Maximum number of messages per connection.
  -/
  maxMessages : Nat

  /--
  Maximum number of headers allowed per message.
  -/
  maxHeaders : Nat

  /--
  Maximum size of a single header value.
  -/
  maxHeaderSize : Nat

  /--
  Whether to enable keep-alive connections by default.
  -/
  enableKeepAlive : Bool

  /--
  Size threshold for flushing output buffer.
  -/
  highMark : Nat

  /--
  The server name (for sending responses) or user agent (for sending requests)
  -/
  identityHeader : Option HeaderValue
