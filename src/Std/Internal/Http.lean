/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Http.Server
public import Std.Internal.Http.Client

public section

/-!
# Http

A "low-level" HTTP 1.1 Server and Client implementation for Lean. It is designed to be used with or without the
`Async` library if you want to implement a custom `Connection`.

# Overview

This module of the standard library defines many concepts related to the HTTP protocol
and its semantics in a SANS-IO format. The main function of this library is `Std.Http.Server.serve`,
located in the module `Std.Internal.Http.Server`. It starts a simple HTTP/1.1 server that
handles all requests and sends them to a simple handler function. It uses the default `Std.Internal.Async`
library, but it can be customized to use whatever IO library you want, as the protocol implementation
is pure.

If you want to customize how your server handles sockets, you can use `Std.Http.Server.serveConnection`,
which is a simple function to bind a handler to a `Transport`.

# Low-Level Protocol Implementation

This library provides a low-level foundation that allows you to implement your own IO layer on top
of it. The core protocol parsing and generation logic is available in `Std.Internal.Http.Protocol`,
which provides pure functions for HTTP message parsing and serialization. This design allows you to
integrate the HTTP protocol handling with any IO system or networking library of your choice, while
reusing the robust protocol implementation.

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
  Server.serve (.v4 (.mk (.ofParts 0 0 0 0) 8080)) handler

def main := mainAsync.block
```

# Main Concepts

## Transport

`Std.Http.Server.Transport` is a type class used for describing a way of communication between a `Connection` and outside
of the `Connection`. It can be a `Mock.Client` that sends and receives byte arrays so it can be used for
deterministic testing a HTTP connection or a `TCP.Socket.Client` that is how usually it communicated with
the internet.

## Connection

`Std.Http.Server.Connection` is a structure that stores both a `Transport` and a `Machine`
the machine right now is only a `Protocol.H1.Machine` that implements a State Machine for parsing request and responses for HTTP/1.1

If you want to customize how your server handles sockets, you can use `Std.Http.Server.serveConnection`,
which is a simple function to bind a handler to a `ClientConnection`.

# Low-Level Protocol Implementation

This library provides a low-level foundation that allows you to implement your own IO layer on top
of it. The core protocol parsing and generation logic is available in `Std.Internal.Http.Protocol`,
which provides pure functions for HTTP message parsing and serialization. This design allows you to
integrate the HTTP protocol handling with any IO system or networking library of your choice, while
reusing the robust protocol implementation.

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
  Server.serve (.v4 (.mk (.ofParts 0 0 0 0) 8080)) handler

def main := mainAsync.block
```
-/

namespace Std.Http
