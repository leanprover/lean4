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

public section

/-!
# HTTP/1.1 Errors

This module defines the error types for HTTP/1.1 protocol processing,
including parsing errors, timeout errors, and connection errors.
-/

namespace Std.Http.Protocol.H1

set_option linter.all true

/--
Specific HTTP processing errors with detailed information.
-/
inductive Error
  /--
  Malformed request line or status line.
  -/
  | invalidStatusLine

  /--
  Invalid or malformed header.
  -/
  | invalidHeader

  /--
  Request timeout occurred.
  -/
  | timeout

  /--
  Request entity too large.
  -/
  | entityTooLarge

  /--
  Unsupported HTTP method.
  -/
  | unsupportedMethod

  /--
  Unsupported HTTP version.
  -/
  | unsupportedVersion

  /--
  Invalid chunk encoding.
  -/
  | invalidChunk

  /--
  Connection closed.
  -/
  | connectionClosed

  /--
  Bad request or response message.
  -/
  | badMessage

  /--
  Generic error with message.
  -/
  | other (message : String)
deriving Repr, BEq

instance : ToString Error where
  toString
  | .invalidStatusLine => "Invalid status line"
  | .invalidHeader => "Invalid header"
  | .timeout => "Timeout"
  | .entityTooLarge => "Entity too large"
  | .unsupportedMethod => "Unsupported method"
  | .unsupportedVersion => "Unsupported version"
  | .invalidChunk => "Invalid chunk"
  | .connectionClosed => "Connection closed"
  | .badMessage => "Bad message"
  | .other msg => s!"Other error: {msg}"

instance : Repr ByteSlice where
  reprPrec x := reprPrec x.toByteArray.data
