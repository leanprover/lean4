/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.ToString
public import Std.Http.Internal

public section

/-!
# Method

This module provides the `Method` type that represents HTTP request methods. It defines all
IANA-registered HTTP methods as distinct constructors, including standard methods (e.g. `GET`,
`POST`, `PUT`, `DELETE`) and extension methods from WebDAV, CalDAV, and other specifications.
Unrecognized method strings produce `none` from `ofString?`.

References:
* https://httpwg.org/specs/rfc9112.html#request.method
* https://httpwg.org/specs/rfc9110.html#method.overview
* https://www.iana.org/assignments/http-methods/http-methods.xhtml
-/

namespace Std.Http

set_option linter.all true

open Internal

/--
A method is a verb that describes the action to be performed.

Covers all methods in the IANA HTTP Method Registry.

* Reference: https://www.iana.org/assignments/http-methods/http-methods.xhtml
-/
inductive Method where
  /--
  Access control list for a resource.
  Source: https://www.rfc-editor.org/rfc/rfc3744#section-8.1
  -/
  | acl

  /--
  Apply a label to a version-controlled resource baseline.
  Source: https://www.rfc-editor.org/rfc/rfc3253#section-12.6
  -/
  | baselineControl

  /--
  Bind a resource to an additional URI path.
  Source: https://www.rfc-editor.org/rfc/rfc5842#section-4
  -/
  | bind

  /--
  Check in a checked-out version-controlled resource.
  Source: https://www.rfc-editor.org/rfc/rfc3253#section-9.4
  -/
  | checkin

  /--
  Check out a version-controlled resource for modification.
  Source: https://www.rfc-editor.org/rfc/rfc3253#section-8.8
  -/
  | checkout

  /--
  Establish a tunnel to a server (often for TLS).
  Source: https://httpwg.org/specs/rfc9110.html#section-9.3.6
  -/
  | connect

  /--
  Copy a resource to a new URI.
  Source: https://www.rfc-editor.org/rfc/rfc4918#section-9.8
  -/
  | copy

  /--
  Remove a resource.
  Source: https://httpwg.org/specs/rfc9110.html#section-9.3.5
  -/
  | delete

  /--
  Retrieve a resource.
  Source: https://httpwg.org/specs/rfc9110.html#section-9.3.1
  -/
  | get

  /--
  Retrieve headers for a resource, without the body.
  Source: https://httpwg.org/specs/rfc9110.html#section-9.3.2
  -/
  | head

  /--
  Apply a label to a version history.
  Source: https://www.rfc-editor.org/rfc/rfc3253#section-8.2
  -/
  | label

  /--
  Create a link relationship between resources.
  Source: https://www.rfc-editor.org/rfc/rfc2068#section-19.6.1.2
  -/
  | link

  /--
  Lock a resource to prevent concurrent modifications.
  Source: https://www.rfc-editor.org/rfc/rfc4918#section-9.10
  -/
  | lock

  /--
  Merge a version-controlled resource.
  Source: https://www.rfc-editor.org/rfc/rfc3253#section-11.2
  -/
  | merge

  /--
  Create a new activity resource.
  Source: https://www.rfc-editor.org/rfc/rfc3253#section-13.5
  -/
  | mkactivity

  /--
  Create a calendar collection.
  Source: https://www.rfc-editor.org/rfc/rfc4791#section-5.3.1
  -/
  | mkcalendar

  /--
  Create a collection resource (WebDAV directory).
  Source: https://www.rfc-editor.org/rfc/rfc4918#section-9.3
  -/
  | mkcol

  /--
  Create a redirect reference resource.
  Source: https://www.rfc-editor.org/rfc/rfc4437#section-6
  -/
  | mkredirectref

  /--
  Create a workspace resource.
  Source: https://www.rfc-editor.org/rfc/rfc3253#section-6.3
  -/
  | mkworkspace

  /--
  Move a resource to a new URI.
  Source: https://www.rfc-editor.org/rfc/rfc4918#section-9.9
  -/
  | move

  /--
  Describe communication options for a resource.
  Source: https://httpwg.org/specs/rfc9110.html#section-9.3.7
  -/
  | options

  /--
  Reorder members of a collection.
  Source: https://www.rfc-editor.org/rfc/rfc3648#section-7
  -/
  | orderpatch

  /--
  Apply partial modifications to a resource.
  Source: https://www.rfc-editor.org/rfc/rfc5789#section-2
  -/
  | patch

  /--
  Submit data to be processed (e.g., form submission).
  Source: https://httpwg.org/specs/rfc9110.html#section-9.3.3
  -/
  | post

  /--
  HTTP/2 connection preface (not used in application code).
  Source: https://www.rfc-editor.org/rfc/rfc9113#section-3.4
  -/
  | pri

  /--
  Retrieve properties of a resource (WebDAV).
  Source: https://www.rfc-editor.org/rfc/rfc4918#section-9.1
  -/
  | propfind

  /--
  Set or remove properties on a resource (WebDAV).
  Source: https://www.rfc-editor.org/rfc/rfc4918#section-9.2
  -/
  | proppatch

  /--
  Replace a resource with new data.
  Source: https://httpwg.org/specs/rfc9110.html#section-9.3.4
  -/
  | put

  /--
  Perform a safe query with a request body.
  Source: https://www.ietf.org/archive/id/draft-ietf-httpbis-safe-method-w-body-14.html#section-2
  -/
  | query

  /--
  Rebind a resource to a new URI path.
  Source: https://www.rfc-editor.org/rfc/rfc5842#section-6
  -/
  | rebind

  /--
  Retrieve a report on a resource.
  Source: https://www.rfc-editor.org/rfc/rfc3253#section-3.6
  -/
  | report

  /--
  Search a resource.
  Source: https://www.rfc-editor.org/rfc/rfc5323#section-2
  -/
  | search

  /--
  Perform a message loop-back test.
  Source: https://httpwg.org/specs/rfc9110.html#section-9.3.8
  -/
  | trace

  /--
  Remove a URI binding from a resource.
  Source: https://www.rfc-editor.org/rfc/rfc5842#section-5
  -/
  | unbind

  /--
  Undo a previous checkout of a version-controlled resource.
  Source: https://www.rfc-editor.org/rfc/rfc3253#section-4.5
  -/
  | uncheckout

  /--
  Remove a link relationship between resources.
  Source: https://www.rfc-editor.org/rfc/rfc2068#section-19.6.1.3
  -/
  | unlink

  /--
  Unlock a resource.
  Source: https://www.rfc-editor.org/rfc/rfc4918#section-9.11
  -/
  | unlock

  /--
  Update a version-controlled resource.
  Source: https://www.rfc-editor.org/rfc/rfc3253#section-7.1
  -/
  | update

  /--
  Update a redirect reference resource.
  Source: https://www.rfc-editor.org/rfc/rfc4437#section-7
  -/
  | updateredirectref

  /--
  Put a resource under version control.
  Source: https://www.rfc-editor.org/rfc/rfc3253#section-3.5
  -/
  | versionControl
deriving Repr, Inhabited, BEq, DecidableEq

namespace Method

/--
Converts a `String` into a `Method`. Returns `none` for unrecognized method strings.
-/
def ofString? : String → Option Method
  | "ACL" => some .acl
  | "BASELINE-CONTROL" => some .baselineControl
  | "BIND" => some .bind
  | "CHECKIN" => some .checkin
  | "CHECKOUT" => some .checkout
  | "CONNECT" => some .connect
  | "COPY" => some .copy
  | "DELETE" => some .delete
  | "GET" => some .get
  | "HEAD" => some .head
  | "LABEL" => some .label
  | "LINK" => some .link
  | "LOCK" => some .lock
  | "MERGE" => some .merge
  | "MKACTIVITY" => some .mkactivity
  | "MKCALENDAR" => some .mkcalendar
  | "MKCOL" => some .mkcol
  | "MKREDIRECTREF" => some .mkredirectref
  | "MKWORKSPACE" => some .mkworkspace
  | "MOVE" => some .move
  | "OPTIONS" => some .options
  | "ORDERPATCH" => some .orderpatch
  | "PATCH" => some .patch
  | "POST" => some .post
  | "PRI" => some .pri
  | "PROPFIND" => some .propfind
  | "PROPPATCH" => some .proppatch
  | "PUT" => some .put
  | "QUERY" => some .query
  | "REBIND" => some .rebind
  | "REPORT" => some .report
  | "SEARCH" => some .search
  | "TRACE" => some .trace
  | "UNBIND" => some .unbind
  | "UNCHECKOUT" => some .uncheckout
  | "UNLINK" => some .unlink
  | "UNLOCK" => some .unlock
  | "UPDATE" => some .update
  | "UPDATEREDIRECTREF" => some .updateredirectref
  | "VERSION-CONTROL" => some .versionControl
  | _ => none

/--
Converts a `String` into a `Method`, panicking if unrecognized.
-/
def ofString! (s : String) : Method :=
  match ofString? s with
  | some m => m
  | none => panic! s!"invalid HTTP method: {s.quote}"

instance : ToString Method where
  toString
    | .acl => "ACL"
    | .baselineControl => "BASELINE-CONTROL"
    | .bind => "BIND"
    | .checkin => "CHECKIN"
    | .checkout => "CHECKOUT"
    | .connect => "CONNECT"
    | .copy => "COPY"
    | .delete => "DELETE"
    | .get => "GET"
    | .head => "HEAD"
    | .label => "LABEL"
    | .link => "LINK"
    | .lock => "LOCK"
    | .merge => "MERGE"
    | .mkactivity => "MKACTIVITY"
    | .mkcalendar => "MKCALENDAR"
    | .mkcol => "MKCOL"
    | .mkredirectref => "MKREDIRECTREF"
    | .mkworkspace => "MKWORKSPACE"
    | .move => "MOVE"
    | .options => "OPTIONS"
    | .orderpatch => "ORDERPATCH"
    | .patch => "PATCH"
    | .post => "POST"
    | .pri => "PRI"
    | .propfind => "PROPFIND"
    | .proppatch => "PROPPATCH"
    | .put => "PUT"
    | .query => "QUERY"
    | .rebind => "REBIND"
    | .report => "REPORT"
    | .search => "SEARCH"
    | .trace => "TRACE"
    | .unbind => "UNBIND"
    | .uncheckout => "UNCHECKOUT"
    | .unlink => "UNLINK"
    | .unlock => "UNLOCK"
    | .update => "UPDATE"
    | .updateredirectref => "UPDATEREDIRECTREF"
    | .versionControl => "VERSION-CONTROL"

instance : Encode .v11 Method where
  encode buffer := buffer.writeString ∘ toString

end Std.Http.Method
