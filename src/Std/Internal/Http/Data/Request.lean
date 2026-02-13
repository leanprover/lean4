/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Http.Data.Extensions
public import Std.Internal.Http.Data.Method
public import Std.Internal.Http.Data.Version

public section

/-!
# Request

This module provides the `Request` type, which represents an HTTP request. It also defines ways
to build a `Request` using functions that make it easier.
-/

namespace Std.Http

set_option linter.all true

/--
The main parts of a request containing the HTTP method, version, and request target URI.
-/
structure Request.Head where
  /--
  The HTTP method (GET, POST, PUT, DELETE, etc.) for the request
  -/
  method : Method := .get

  /--
  The HTTP protocol version (HTTP/1.0, HTTP/1.1, HTTP/2.0, etc.)
  -/
  version : Version := .v11

  /--
  The request target/URI indicating the resource being requested
  -/
  uri : String := "*"
deriving Inhabited, Repr

/--
HTTP request structure parameterized by body type
-/
structure Request (t : Type) where
  /--
  The request headers and metadata
  -/
  head : Request.Head

  /--
  The request body content of type t
  -/
  body : t

  /--
  Optional dynamic metadata attached to the request.
  -/
  extensions : Extensions := .empty
deriving Inhabited

/--
Builds an HTTP Request
-/
structure Request.Builder where
  /--
  The head of the request
  -/
  head : Head := {}

  /--
  Optional dynamic metadata attached to the request.
  -/
  extensions : Extensions := .empty

namespace Request

instance : ToString Head where
  toString req :=
    toString req.method ++ " " ++
    toString req.uri ++ " " ++
    toString req.version ++
    "\r\n"

open Internal in
instance : Encode .v11 Head where
  encode buffer req :=
    let buffer := Encode.encode (v := .v11) buffer req.method
    let buffer := buffer.writeChar ' '
    let buffer := buffer.writeString req.uri
    let buffer := buffer.writeChar ' '
    let buffer := Encode.encode (v := .v11) buffer req.version
    buffer.writeString "\r\n"

/--
Creates a new HTTP Request builder with default head (method: GET, version: HTTP/1.1, asterisk URI,
empty URI)
-/
def new : Builder := { }

namespace Builder

/--
Creates a new HTTP Request builder with default head (method: GET, version: HTTP/1.1, asterisk URI,
empty URI)
-/
def empty : Builder := { }

/--
Sets the HTTP method for the request being built
-/
def method (builder : Builder) (method : Method) : Builder :=
  { builder with head := { builder.head with method := method } }

/--
Sets the HTTP version for the request being built
-/
def version (builder : Builder) (version : Version) : Builder :=
  { builder with head := { builder.head with version := version } }

/--
Sets the request target/URI for the request being built
-/
def uri (builder : Builder) (uri : String) : Builder :=
  { builder with head := { builder.head with uri := uri } }

/--
Inserts a typed extension value into the request being built.
-/
def extension (builder : Builder) [TypeName α] (data : α) : Builder :=
  { builder with extensions := builder.extensions.insert data }

/--
Builds and returns the final HTTP Request with the specified body
-/
def body (builder : Builder) (body : t) : Request t :=
  { head := builder.head, body := body, extensions := builder.extensions }

end Builder

/--
Creates a new HTTP GET Request with the specified URI
-/
def get (uri : String) : Builder :=
  new
  |>.method .get
  |>.uri uri

/--
Creates a new HTTP POST Request builder with the specified URI.
-/
def post (uri : String) : Builder :=
  new
  |>.method .post
  |>.uri uri

/--
Creates a new HTTP PUT Request builder with the specified URI.
-/
def put (uri : String) : Builder :=
  new
  |>.method .put
  |>.uri uri

/--
Creates a new HTTP DELETE Request builder with the specified URI
-/
def delete (uri : String) : Builder :=
  new
  |>.method .delete
  |>.uri uri

/--
Creates a new HTTP PATCH Request builder with the specified URI
-/
def patch (uri : String) : Builder :=
  new
  |>.method .patch
  |>.uri uri

/--
Creates a new HTTP HEAD Request builder with the specified URI.
Named `head'` to avoid conflict with the `head` field accessor.
-/
def head' (uri : String) : Builder :=
  new
  |>.method .head
  |>.uri uri

/--
Creates a new HTTP OPTIONS Request builder with the specified URI.
Use `Request.options "*"` for server-wide OPTIONS.
-/
def options (uri : String) : Builder :=
  new
  |>.method .options
  |>.uri uri

/--
Creates a new HTTP CONNECT Request builder with the specified URI.
Typically used with authority-form URIs such as `"example.com:443"` for tunneling.
-/
def connect (uri : String) : Builder :=
  new
  |>.method .connect
  |>.uri uri

/--
Creates a new HTTP TRACE Request builder with the specified URI
-/
def trace (uri : String) : Builder :=
  new
  |>.method .trace
  |>.uri uri

end Std.Http.Request
