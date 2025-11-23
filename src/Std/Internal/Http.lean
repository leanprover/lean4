/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Http.Client
public import Std.Internal.Http.Server
public import Std.Internal.Http.Client

public section

/-!
# Http

A low-level HTTP/1.1 server implementation for Lean. This library provides a pure, sans-I/O
protocol implementation that can be used with the `Async` library or with custom connection
handlers.

## Overview

This module of the standard library defines many concepts related to the HTTP protocol and its semantics
in a sans I/O format.

**sans I/O** means that the core logic of the library doesn't perform any actual input/output itself,
it just defines how data *should* be processed. This separation allows the protocol implementation
to remain pure and testable, while different transports (like TCP sockets or mocks) can handle
the actual reading and writing of bytes.

The main entry point is `Std.Http.Server.serve` (in `Std.Internal.Http.Server`), which starts
an HTTP/1.1 server using the default `Std.Internal.Async` library for Async I/O.

## Minimal Example

```lean
import Std.Internal.Http
import Std.Internal.Async

open Std.Internal.IO.Async
open Std Http

def handler (req : Request Body) : ContextAsync (Response Body) := do
  -- Attempt to collect the request body as a UTF-8 string
  let some data ← req.body.collectString
    | return Response.badRequest
      |>.header! "Content-Type" "text/plain"
      |>.body "Expected a UTF-8 encoded body"

  -- Return a successful response with the collected data
  return Response.ok
    |>.header! "Content-Type" "text/plain"
    |>.body s!"Hello, {data}!"

def mainAsync : Async Unit := do
  -- Bind to localhost:8080
  let address := .v4 (.mk (.ofParts 0 0 0 0) 8080)

  -- Start the server with our handler
  let server ← Server.serve address handler

  -- Block until shutdown (via signal or programmatic shutdown)
  server.waitShutdown

def main := mainAsync.block
```

## Architecture

### Handlers

Handlers have the signature:
```lean
Request Body → ContextAsync (Response Body)
```

`ContextAsync` is a monad that provides:
- Asynchronous I/O capabilities via the `Async` monad
- Cancellation context to monitor connection status and terminate connections when needed

### Transport

`Std.Http.Server.Transport` is a type class that defines how communication occurs between a `Connection`
and the outside world. It can be implemented by, for example, a `Mock.Client`, which sends and receives
byte arrays for deterministic HTTP connection testing, or by a `TCP.Socket.Client`, which is the
standard way to communicate over the internet in HTTP/1.1.

### Connection

`Std.Http.Server.Connection` is a structure that holds both a `Transport` and a `Machine`. The machine is
a `Protocol.H1.Machine`, which implements the state machine responsible for parsing HTTP/1.1 requests and responses.
It can change in the future if some other protocols are implemented.

If you want to customize how your server handles sockets, you can use `Std.Http.Server.serveConnection`,
a simple function that binds a handler to a `ClientConnection`.
-/
