/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Http.Client
public import Std.Internal.Http.Server

public section

/-!
# HTTP Library

A low-level HTTP/1.1 server implementation for Lean. This library provides a pure,
sans-I/O protocol implementation that can be used with the `Async` library or with
custom connection handlers.

## Overview

This module provides a complete HTTP/1.1 server implementation with support for:

- Request/response handling with streaming bodies
- Keep-alive connections
- Chunked transfer encoding
- Header validation and management
- Configurable timeouts and limits

**Sans I/O Architecture**: The core protocol logic doesn't perform any actual I/O itself -
it just defines how data should be processed. This separation allows the protocol implementation
to remain pure and testable, while different transports (TCP sockets, mock clients) handle
the actual reading and writing of bytes.

## Quick Start

The main entry point is `Server.serve`, which starts an HTTP/1.1 server. Implement the
`Server.Handler` type class to define how the server handles requests, errors, and
`Expect: 100-continue` headers:

```lean
import Std.Internal.Http

open Std Internal IO Async
open Std Http Server

structure MyHandler

instance : Handler MyHandler where
  onRequest _ req := do
    Response.ok |>.text "Hello, World!"

def main : IO Unit := Async.block do
  let addr : Net.SocketAddress := .v4 ⟨.ofParts 127 0 0 1, 8080⟩
  let server ← Server.serve addr MyHandler.mk
  server.waitShutdown
```

## Working with Requests

Incoming requests are represented by `Request Body.Stream`, which bundles together the
request line, parsed headers, and a lazily-consumed body. Headers are available
immediately, while the body can be streamed or collected on demand, allowing handlers
to efficiently process both small and large requests.

### Reading Headers

```lean
def handler (req : Request Body.Stream) : ContextAsync (Response Body.Stream) := do
  -- Access request method and URI
  let method := req.head.method      -- Method.get, Method.post, etc.
  let uri := req.head.uri            -- RequestTarget

  -- Read a specific header
  if let some contentType := req.head.headers.get? (.mk "content-type") then
    IO.println s!"Content-Type: {contentType}"

  Response.ok |>.text "OK"
```

### Reading the Request Body

The request body is exposed as a `Body.Stream`, which can be consumed incrementally or
collected into memory. The `readAll` method reads the entire body, with an optional size
limit to protect against unbounded payloads.

```lean
def handler (req : Request Body.Stream) : ContextAsync (Response Body.Stream) := do
  -- Collect entire body as a String
  let bodyStr : String ← req.body.readAll

  -- Or with a maximum size limit
  let bodyStr : String ← req.body.readAll (maximumSize := some 1024)

  Response.ok |>.text s!"Received: {bodyStr}"
```

## Building Responses

Responses are constructed using a builder API that starts from a status code and adds
headers and a body. Common helpers exist for text, HTML, JSON, and binary responses, while
still allowing full control over status codes and header values.

```lean
-- Text response
Response.ok |>.text "Hello!"

-- HTML response
Response.ok |>.html "<h1>Hello!</h1>"

-- JSON response
Response.ok |>.json "{\"key\": \"value\"}"

-- Binary response
Response.ok |>.bytes someByteArray

-- Custom status
Response.new |>.status .created |>.text "Resource created"

-- With custom headers
Response.ok
  |>.header! "X-Custom-Header" "value"
  |>.header! "Cache-Control" "no-cache"
  |>.text "Response with headers"
```

### Streaming Responses

For large responses or server-sent events, use streaming:

```lean
def handler (req : Request Body.Stream) : ContextAsync (Response Body.Stream) := do
  Response.ok
    |>.header! "Content-Type" "text/plain"
    |>.stream fun stream => do
      for i in [0:10] do
        stream.send { data := s!"chunk {i}\n".toUTF8 }
        Async.sleep 1000
      stream.close
```

## Server Configuration

Configure server behavior with `Config`:

```lean
def config : Config := {
  maxRequests := 10000000,
  lingeringTimeout := 5000,
}

let server ← Server.serve addr MyHandler.mk config
```

## Handler Type Class

Implement `Server.Handler` to define how the server processes events. The class has three
methods, all with default implementations:

- `onRequest` — called for each incoming request; returns a response inside `ContextAsync`
- `onFailure` — called when an error occurs while processing a request
- `onContinue` — called when a request includes an `Expect: 100-continue` header; return
  `true` to accept the body or `false` to reject it

```lean
structure MyHandler where
  greeting : String

instance : Handler MyHandler where
  onRequest self req := do
    Response.ok |>.text self.greeting

  onFailure self err := do
    IO.eprintln s!"Error: {err}"
```

The handler methods operate in the following monads:

- `onRequest` uses `ContextAsync` — an asynchronous monad (`ReaderT CancellationContext Async`) that provides:
  - Full access to `Async` operations (spawning tasks, sleeping, concurrent I/O)
  - A `CancellationContext` tied to the client connection — when the client disconnects, the
    context is cancelled, allowing your handler to detect this and stop work early
- `onFailure` uses `Async`
- `onContinue` uses `Async`
-/
