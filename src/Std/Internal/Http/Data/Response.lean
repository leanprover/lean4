/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Async
public import Std.Internal.Http.Data.Status
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
  headers : HashMap String (Array String) := .emptyWithCapacity
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
    r.headers.fold (init := "") (fun acc key values =>
      values.foldl (init := acc) (fun acc value =>
        acc ++ key ++ ": " ++ value ++ "\r\n")) ++
    "\r\n"

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
Sets the headers for the response being built
-/
def headers (builder : Builder) (headers : HashMap String (Array String)) : Builder :=
  { builder with head := { builder.head with headers } }

/--
Adds a single header to the response being built
-/
def header (builder : Builder) (key : String) (value : String) : Builder :=
  let headers := builder.head.headers
  let values := headers.getD key #[]
  { builder with head := { builder.head with headers := headers.insert key (values.push value) } }

/--
Builds and returns the final HTTP Response with the specified body
-/
def body (builder : Builder) (body : t) : Response t :=
  { head := builder.head, body := body }

/--
Builds and returns the final HTTP Response.
-/
def build [EmptyCollection t] (builder : Builder) : Response t :=
  { head := builder.head, body := {} }

end Builder

/--
Creates a new HTTP Response builder with the 200 status code.
-/
def ok : Builder :=
  .empty |>.status .ok

/--
Creates a new HTTP Response builder with the provided status.
-/
def withStatus (status : Status) : Builder :=
  .empty |>.status status

/--
Creates a new HTTP Response builder with the 404 status code.
-/
def notFound : Builder :=
  .empty |>.status .notFound

/--
Creates a new HTTP Response builder with the 500 status code.
-/
def internalServerError : Builder :=
  .empty |>.status .internalServerError

/--
Creates a new HTTP Response builder with the 400 status code.
-/
def badRequest : Builder :=
  .empty |>.status .badRequest

/--
Creates a new HTTP Response builder with the 201 status code.
-/
def created : Builder :=
  .empty |>.status .created

/--
Creates a new HTTP Response builder with the 202 status code.
-/
def accepted : Builder :=
  .empty |>.status .accepted

/--
Creates a new HTTP Response builder with the 401 status code.
-/
def unauthorized : Builder :=
  .empty |>.status .unauthorized

/--
Creates a new HTTP Response builder with the 403 status code.
-/
def forbidden : Builder :=
  .empty |>.status .forbidden

/--
Creates a new HTTP Response builder with the 409 status code.
-/
def conflict : Builder :=
  .empty |>.status .conflict

/--
Creates a new HTTP Response builder with the 503 status code.
-/
def serviceUnavailable : Builder :=
  .empty |>.status .serviceUnavailable

/--
Creates a redirect response with the 302 Found status code (temporary redirect).
-/
def redirect (location : String) : Builder :=
  Builder.empty
  |>.status .found
  |>.header "Location" location

/--
Creates a redirect response with the 301 Moved Permanently status code (permanent redirect).
-/
def redirectPermanent (location : String) : Builder :=
  Builder.empty
  |>.status .movedPermanently
  |>.header "Location" location

/--
Creates a redirect response with a configurable status code.
Use `permanent := true` for 301 Moved Permanently, `permanent := false` for 302 Found.
-/
def redirectWith (location : String) (permanent : Bool) : Builder :=
  Builder.empty
  |>.status (if permanent then .movedPermanently else .found)
  |>.header "Location" location

end Response
