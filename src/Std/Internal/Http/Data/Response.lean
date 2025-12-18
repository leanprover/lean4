/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Async
public import Std.Internal.Http.Data.Body
public import Std.Internal.Http.Data.Status
public import Std.Internal.Http.Data.Headers
public import Std.Internal.Http.Data.Version

public section

/-!
# Response

This module provides the `Response` type, which represents an HTTP response. It also defines
builder functions and convenience methods for constructing responses with various content types.
-/

namespace Std.Http

set_option linter.all true

open Std.Internal.IO.Async
open Internal Lean

/--
The main parts of a response.
-/
structure Response.Head where
  /--
  The HTTP status code and reason phrase, indicating the result of the request.
  For example, `.ok` corresponds to `200 OK`.
  -/
  status : Status := .ok

  /--
  The HTTP protocol version used in the response, e.g. `HTTP/1.1`.
  -/
  version : Version := .v11

  /--
  The set of response headers, providing metadata such as `Content-Type`,
  `Content-Length`, and caching directives.
  -/
  headers : Headers := .empty
deriving Inhabited, Repr

/--
HTTP response structure parameterized by body type
-/
structure Response (t : Type) where
  /--
  The information of the status-line of the response
  -/
  head : Response.Head := {}

  /--
  The content of the response.
  -/
  body : t
deriving Inhabited

/--
Builds a HTTP Response.
-/
structure Response.Builder where
  /--
  The information of the status-line of the response
  -/
  head : Head := {}

namespace Response

instance : ToString Head where
  toString r :=
    toString r.version ++ " " ++
    toString r.status.toCode ++ " " ++
    toString r.status ++ "\r\n" ++
    toString r.headers ++ "\r\n\r\n"

/--
Creates a new HTTP Response builder with default head (status: 200 OK, version: HTTP/1.1, empty headers)
-/
def new : Builder := { }

namespace Builder

/--
Creates a new HTTP Response builder with default head (status: 200 OK, version: HTTP/1.1, empty headers)
-/
def empty : Builder := { }

/--
Sets the HTTP status code for the response being built
-/
def status (builder : Builder) (status : Status) : Builder :=
  { builder with head := { builder.head with status := status } }

/--
Sets the HTTP version for the response being built
-/
def version (builder : Builder) (version : Version) : Builder :=
  { builder with head := { builder.head with version := version } }

/--
Sets the headers for the response being built
-/
def headers (builder : Builder) (headers : Headers) : Builder :=
  { builder with head := { builder.head with headers } }

/--
Adds a single header to the response being built
-/
def header (builder : Builder) (key : HeaderName) (value : HeaderValue) : Builder :=
  { builder with head := { builder.head with headers := builder.head.headers.insert key value } }

/--
Adds a single header to the response being built
-/
def header! (builder : Builder) (key : String) (value : String) : Builder :=
  let key := HeaderName.ofString! key
  let value := HeaderValue.ofString! value
  { builder with head := { builder.head with headers := builder.head.headers.insert key value } }

/--
Builds and returns the final HTTP Response with the specified body
-/
def body (builder : Builder) (body : t) : Response t :=
  { head := builder.head, body := body }

/--
Builds and returns the final HTTP Response with a stream builder
-/
def stream (builder : Builder) (body : Body.ByteStream → ContextAsync Unit) : ContextAsync (Response Body) := do
  let stream ← Body.ByteStream.empty
  background (body stream)
  return { head := builder.head, body := stream }

/--
Builds and returns the final HTTP Response.
-/
def build [EmptyCollection t] (builder : Builder) : Response t :=
  { head := builder.head, body := {} }

/--
Builds and returns the final HTTP Response with the specified body as binary data.
-/
def binary (builder : Builder) (bytes : ByteArray) : Response Body :=
  builder
    |>.header (.new "Content-Type") (.new "application/octet-stream")
    |>.body (Body.bytes bytes)

/--
Builds and returns the final HTTP Response with the specified body as plain text.
-/
def text (builder : Builder) (body : String) : Response Body :=
  builder
    |>.header (.new "Content-Type") (.new "text/plain; charset=utf-8")
    |>.body (body.toUTF8 |> Body.bytes)

/--
Builds and returns the final HTTP Response with the specified body as HTML.
-/
def html (builder : Builder) (body : String) : Response Body :=
  builder
    |>.header (.new "Content-Type") (.new "text/html; charset=utf-8")
    |>.body (body.toUTF8 |> Body.bytes)

end Builder

/--
Creates a new HTTP Response builder with with 200 status code
-/
def ok : Builder :=
  .empty |>.status .ok

/--
Creates a new HTTP Response builder with with provided status
-/
def buildWithStatus (status : Status) : Builder :=
  .empty |>.status status

/--
Creates a new HTTP Response builder with with 404 status code
-/
def notFound : Builder :=
  .empty |>.status .notFound

/--
Creates a new HTTP Response builder with with 500 status code
-/
def internalServerError : Builder :=
  .empty |>.status .internalServerError

/--
Creates a new HTTP Response builder with with 400 status code
-/
def badRequest : Builder :=
  .empty |>.status .badRequest

end Response
