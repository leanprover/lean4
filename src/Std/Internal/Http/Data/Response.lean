/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Http.Encode
public import Std.Internal.Http.Data.Body
public import Std.Internal.Http.Data.Status
public import Std.Internal.Http.Data.Headers
public import Std.Internal.Http.Data.Version

public section

namespace Std
namespace Http

set_option linter.all true

open Util
open Lean

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
  The information of the status-line of the request.
  -/
  head : Response.Head := {}

  /--
  The content of the request.
  -/
  body : Option t
deriving Inhabited

/--
Builds a HTTP Response
-/
structure Response.Builder where

  /--
  The information of the status-line of the request.
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
Adds a single header to the response being built
-/
def header (builder : Builder) (key : String) (value : HeaderValue) : Builder :=
  { builder with head := { builder.head with headers := builder.head.headers.insert key value } }

/--
Builds and returns the final HTTP Response with the specified body
-/
def body (builder : Builder) (body : t) : Response t :=
  { head := builder.head, body := some body }

/--
Builds and returns the final HTTP Response.
-/
def build (builder : Builder) : Response t :=
  { head := builder.head, body := none }

/--
Builds and returns the final HTTP Response with the specified body as binary data.
-/
def binary (builder : Builder) (bytes : ByteArray) : Response Body :=
  builder
    |>.header "Content-Type" (.new "application/octet-stream")
    |>.body (Body.bytes bytes)

/--
Builds and returns the final HTTP Response with the specified body as plain text.
-/
def text (builder : Builder) (body : String) : Response Body :=
  builder
    |>.header "Content-Type" (.new "text/plain; charset=utf-8")
    |>.body (body.toUTF8 |> Body.bytes)

/--
Builds and returns the final HTTP Response with the specified body as HTML.
-/
def html (builder : Builder) (body : String) : Response Body :=
  builder
    |>.header "Content-Type" (.new "text/html; charset=utf-8")
    |>.body (body.toUTF8 |> Body.bytes)

end Builder

/--
Creates a new HTTP Response with OK status and the provided string body
-/
def ok (body : t) : Response t :=
  new.body body

/--
Creates a new HTTP Response with the specified status and string body
-/
def buildWithStatus (status : Status) (body : t) : Response t :=
  new
  |>.status status
  |>.body body

/--
Convenience function to create a simple HTTP 404 Not Found response
-/
def notFound [Coe String t] (body : String := "Not Found") : Response t :=
  new
  |>.status .notFound
  |>.body body

/--
Convenience function to create a simple HTTP 500 Internal Server Error response
-/
def internalServerError [Coe String t] (body : String := "Internal Server Error") : Response t :=
  new
  |>.status .internalServerError
  |>.body body

/--
Convenience function to create a simple HTTP 400 Bad Request response
-/
def badRequest [Coe String t] (body : String := "Bad Request") : Response t :=
  new
  |>.status .badRequest
  |>.body body

end Response
