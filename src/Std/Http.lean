/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Server
public import Std.Http.Client
-- Built with the library for the test suite, but not part of what `import Std.Http` exports.
import Std.Http.Test.Helpers

public section

/-!
# HTTP Library

An HTTP/1.1 server and client for Lean, built on a pure, sans-I/O protocol implementation that can
be used with the `Async` library or with custom connection handlers. The client is described in the
"Client" section below.

## Overview

This module provides a complete HTTP/1.1 server implementation with support for:

- Request/response handling with directional streaming bodies
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
import Std.Http

open Std Async
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

Incoming requests are represented by `Request Body.Stream`, which bundles the request
line, parsed headers, and a lazily-consumed body. Headers are available immediately,
while the body can be streamed or collected on demand, allowing handlers to process both
small and large payloads efficiently.

### Reading Headers

```lean
def handler (req : Request Body.Stream) : ContextAsync (Response Body.Any) := do
  -- Access request method and URI
  let method := req.line.method      -- Method.get, Method.post, etc.
  let uri := req.line.uri            -- RequestTarget

  -- Read a specific header
  if let some contentType := req.line.headers.get? (.mk "content-type") then
    IO.println s!"Content-Type: {contentType}"

  Response.ok |>.text "OK"
```

### URI Query Semantics

`RequestTarget.query` is parsed using form-style key/value conventions (`k=v&...`), and `+` is decoded as a
space in query components. If you need RFC 3986 opaque query handling, use the raw request target string
(`toString req.line.uri`) and parse it with custom logic.

### Reading the Request Body

The request body is exposed as `Body.Stream`, which can be consumed incrementally or
collected into memory. The `readAll` method reads the entire body, with an optional size
limit to protect against unbounded payloads.

```lean
def handler (req : Request Body.Stream) : ContextAsync (Response Body.Any) := do
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

Response builders produce `Async (Response Body.Full)`, which converts to the `Response Body.Any` a
handler returns.

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
def handler (req : Request Body.Stream) : ContextAsync (Response Body.Any) := do
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

## Client

`Client` sends HTTP/1.1 requests over a pool of keep-alive connections per origin, following
redirects and retrying requests that a fresh connection may succeed with. Create one client and share
it: it is safe to use from many tasks at once, and concurrent requests to one origin run on separate
connections, up to `Client.Config.maxConnectionsPerOrigin`.

```lean
import Std.Http
open Std Async Http

def main : IO Unit := Async.block do
  let client ← Client.new

  -- A GET from a URL.
  let response ← client.get "http://example.com/"
  IO.println s!"status {response.line.status.toCode}"
  IO.println (← response.body.readAll (α := String))

  -- A request with a body, sent to the origin its URL names, with failures as typed values.
  let request ← Request.new |>.method .post |>.uri! "http://example.com/items"
    |>.json "{\"name\": \"lean\"}"
  match ← client.tryExecute request with
  | .ok response => discard <| response.body.readAll (α := ByteArray)
  | .error (.connect message) => IO.eprintln s!"could not connect: {message}"
  | .error .timeout => IO.eprintln "timed out"
  | .error e => IO.eprintln s!"request failed: {e}"
```

`get`, `execute`, and `send` throw on failure; `tryGet`, `tryExecute`, and `trySend` return a
`Client.Error`. `send` and `trySend` take the origin separately, for a request built with an
origin-form target.

**Read or close every body.** A response's connection stays with it until its body has been read to
the end or closed. Until then that connection carries no other request; a body that is neither read
nor closed is released only when `requestTimeout` runs out.

**Timeouts** (`Client.Config`): `connectTimeout` bounds DNS resolution and the connect;
`requestTimeout` bounds sending a request and receiving its response head, then each pause in the
body, so a body of any length streams as long as it keeps moving; `readTimeout` bounds the wait for
the next bytes from the peer.

**Redirects** are followed up to `maxRedirects`; a chain that runs out of hops returns its last
redirect response. Credentials and cookies are not carried to another origin.

**Retries**: a request with an idempotent method and a replayable body is sent again, up to
`maxRetries` times on fresh connections, after a connection-level failure; any request is sent again
after a failure that proves it never reached the server.

**Hooks**: a `Client.Middleware` sees every request and response, redirect hops included, together
with the origin each hop goes to (`Client.Middleware.forOrigin` keeps one to a single origin). An
`Authenticator` answers `401` and `407` challenges, a `CookieHandler` stores and supplies cookies, a
`ProxySelector` routes origins through an HTTP proxy, and a `Connector` opens connections.

The default connector speaks plain HTTP over TCP; `https` URLs need a connector that provides TLS.
-/
