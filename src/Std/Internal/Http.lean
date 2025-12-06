/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Http.Server

public section

/-!
# Http

A "low-level" HTTP 1.1 Server and Client implementation for Lean. It is designed to be used with or without the
`Async` library if you want to implement a custom `Connection`.

# Overview

This module of the standard library defines many concepts related to the HTTP protocol
and its semantics in a sans I/O format.

**sans I/O** means that the core logic of the library doesn’t perform any actual input/output itself,
it just defines how data *should* be processed. This separation allows the protocol implementation
to remain pure and testable, while different transports (like TCP sockets or mocks) can handle
the actual reading and writing of bytes.

The main function of this library is `Std.Http.Server.serve`,
located in the module `Std.Internal.Http.Server`. It starts a simple HTTP/1.1 server that
handles all requests and sends them to a simple handler function. It uses the default `Std.Internal.Async`
library, but it can be customized to use whatever IO library you want, as the protocol implementation
is pure.

If you want to customize how your server handles sockets, you can use `Std.Http.Server.serveConnection`,
which is a simple function to bind a handler to a `Transport`.

# Minimal Example

```lean
import Std.Internal.Http
import Std.Internal.Async

open Std.Internal.IO.Async
open Std Http

def handler (req : Request Body) : Async (Response Body) := do
  let some data ← req.body.collectString
    | return Response.badRequest "expected a utf8 body"

  return Response.ok ("hi, " ++ data)

def mainAsync : Async Unit := do
  let server ← Server.serve (.v4 (.mk (.ofParts 0 0 0 0) 8080)) handler
  server.waitShutdown

def main := mainAsync.block
```

# Main Concepts

## Transport

`Std.Http.Server.Transport` is a type class that defines how communication occurs between a `Connection`
and the outside world. It can be implemented by, for example, a `Mock.Client`, which sends and receives
byte arrays for deterministic HTTP connection testing, or by a `TCP.Socket.Client`, which is the
standard way to communicate over the internet in HTTP/1.1.

## Connection

`Std.Http.Server.Connection` is a structure that holds both a `Transport` and a `Machine`. The machine is
a `Protocol.H1.Machine`, which implements the state machine responsible for parsing HTTP/1.1 requests and responses.
It can change in the future if some other protocols are implemented

If you want to customize how your server handles sockets, you can use `Std.Http.Server.serveConnection`,
a simple function that binds a handler to a `ClientConnection`.

# Minimal Example

```lean
import Std.Internal.Http
import Std.Internal.Async

open Std.Internal.IO.Async
open Std Http

def handler (req : Request Body) : Async (Response Body) := do
  let some data ← req.body.collectString
    | return Response.badRequest "expected a utf8 body"

  return Response.ok ("hi, " ++ data)

def mainAsync : Async Unit := do
  let server ← Server.serve (.v4 (.mk (.ofParts 0 0 0 0) 8080)) handler
  server.waitShutdown

def main := mainAsync.block
```
-/
