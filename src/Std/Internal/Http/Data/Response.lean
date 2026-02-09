/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Async
public import Std.Internal.Http.Data.Extensions
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

  /--
  Optional dynamic metadata attached to the response.
  -/
  extensions : Extensions := .empty
deriving Inhabited

/--
Builds a HTTP Response.
-/
structure Response.Builder where
  /--
  The information of the status-line of the response
  -/
  head : Head := {}

  /--
  Optional dynamic metadata attached to the response.
  -/
  extensions : Extensions := .empty

namespace Response

instance : ToString Head where
  toString r :=
    toString r.version ++ " " ++
    toString r.status.toCode ++ " " ++
    toString r.status ++ "\r\n"

open Internal in
instance : Encode .v11 Head where
  encode buffer r :=
    let buffer := Encode.encode (v := .v11) buffer r.version
    let buffer := buffer.writeChar ' '
    let buffer := Encode.encode (v := .v11) buffer r.status
    buffer.writeString "\r\n"

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
Inserts a typed extension value into the response being built.
-/
def extension (builder : Builder) [TypeName α] (data : α) : Builder :=
  { builder with extensions := builder.extensions.insert data }

/--
Builds and returns the final HTTP Response with the specified body
-/
def body (builder : Builder) (body : t) : Response t :=
  { head := builder.head, body := body, extensions := builder.extensions }

/--
Builds and returns the final HTTP Response.
-/
def build [EmptyCollection t] (builder : Builder) : Response t :=
  { head := builder.head, body := {}, extensions := builder.extensions }

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

end Response
