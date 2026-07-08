/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module
prelude
public import Std.Async.TCP.SSL.Basic
public import Std.Async.TCP.SSL.Connection
public import Std.Async.TCP.SSL.Server
public import Std.Async.TCP.SSL.Client

/-!
TLS-over-TCP socket API built on top of `Std.Internal.SSL` (OpenSSL) and `Std.Internal.UV.TCP` (libuv).
Provides `Server`, `Client`, `ServerConn`, and the shared `Connection` type with
send/recv/selector/shutdown operations.

The implementation is split across `SSL.Basic` (types and shared I/O plumbing), `SSL.Connection`
(per-connection send/recv/shutdown), `SSL.Server` (accept), and `SSL.Client` (connect).
-/
