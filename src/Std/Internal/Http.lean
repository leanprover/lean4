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

The main entry point is `HTTP.Server.serve`, which starts an HTTP/1.1 server:

```lean
import Std.Internal.Http
import Std.Internal.Async

open Std.Internal.IO.Async
open Std Http

def handler (req : Request Body) : ContextAsync (Response Body) := do
  -- Return a simple text response
  return Response.ok
    |>.text "Hello, World!"

def main : IO Unit := do
  let address := .v4 (.mk (.ofParts 127 0 0 1) 8080)
  let server ← (Server.serve address handler).block
  server.waitShutdown.block
```

## Working with Requests

Incoming requests are represented by `Request Body`, which bundles together the
request line, parsed headers, and a lazily-consumed body. Headers are available
immediately, while the body can be streamed or collected on demand, allowing handlers
to efficiently process both small and large requests.

### Reading Headers

```lean
def handler (req : Request Body) : ContextAsync (Response Body) := do
  -- Access request method and URI
  let method := req.head.method      -- Method.get, Method.post, etc.
  let uri := req.head.uri            -- RequestTarget

  -- Read a specific header
  if let some contentType := req.head.headers.get? (.new "content-type") then
    IO.println s!"Content-Type: {contentType.value}"

  return Response.ok |>.text "OK"
```

### Reading Request Body

The request body is exposed as a stream, which can be consumed incrementally or collected into memory.
Helper functions are provided to decode the body as UTF-8 text or raw bytes, with optional size limits
to protect against unbounded payloads.

```lean
def handler (req : Request Body) : ContextAsync (Response Body) := do
  -- Collect entire body as string (with optional size limit)
  let some bodyStr ← req.body.collectString (maxBytes := some 1024)
    | return Response.badRequest |>.text "Invalid UTF-8 or body too large"

  -- Or collect as raw bytes
  let bodyBytes ← req.body.collectByteArray

  return Response.ok |>.text s!"Received: {bodyStr}"
```

## Building Responses

Responses are constructed using an API that starts from a status code and adds headers and a body.
Common helpers exist for text, HTML, and binary responses, while still allowing full control over status
codes and header values.

```lean
-- Text response
Response.ok |>.text "Hello!"

-- HTML response
Response.ok |>.html "<h1>Hello!</h1>"

-- Binary response
Response.ok |>.binary someByteArray

-- Custom status
Response.withStatus .created |>.text "Resource created"

-- With custom headers
Response.ok
  |>.header! "X-Custom-Header" "value"
  |>.header! "Cache-Control" "no-cache"
  |>.text "Response with headers"
```

### Streaming Responses

For large responses or server-sent events, use streaming:

```lean
def handler (req : Request Body) : ContextAsync (Response Body) := do
  Response.ok
    |>.header! "Content-Type" "text/plain"
    |>.stream fun stream => do
      for i in [0:10] do
        stream.writeChunk { data := s!"chunk {i}\n".toUTF8 }
        -- Optionally add delays for SSE-like behavior
      stream.close
```

## Server Configuration

Configure server behavior with `Server.Config`:

```lean
def config : Std.Http.Config := {
  keepAliveTimeout := ⟨30000, by decide⟩,
  lingeringTimeout := 5000,
  maximumRecvSize := 65536,
  defaultPayloadBytes := 8192,
}

let server ← Server.serve address handler config
```

## Architecture

### Request/Response Types

- `Request Body` - HTTP request with headers and body
- `Response Body` - HTTP response with status, headers, and body
- `Body` - Request/response body (empty, bytes, or stream)
- `Headers` - Collection of header name-value pairs

### Handler Signature

```lean
Request Body → ContextAsync (Response Body)
```

`ContextAsync` provides:
- Asynchronous I/O via the `Async` monad
- Cancellation context to monitor connection status

### Transport Layer

`Transport` is a type class abstracting the network layer. Implementations:
- `TCP.Socket.Client` - Standard TCP sockets for production
- `Mock.Client` - In-memory mock for testing

### Low-Level API

For custom connection handling, use `Server.serveConnection`:

```lean
-- Handle a single connection with custom transport
Server.serveConnection client handler config
```
-/
