/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.Repr
public import Init.Data.ToString
public import Std.Internal.Http.Internal

public section

/-!
# Method

This module provides the `Method` type, that represents HTTP request methods. It defines the
standard set of HTTP methods (e.g. `GET`, `POST`, `PUT`, `DELETE`).
-/

namespace Std.Http

set_option linter.all true

open Internal

/--
A method is a verb that describes the action to be performed.

* Reference: https://httpwg.org/specs/rfc9110.html#methods
-/
inductive Method where
  /--
  Retrieve a resource.
  -/
  | get

  /--
  Retrieve headers for a resource, without the body.
  -/
  | head

  /--
  Submit data to be processed (e.g., form submission).
  -/
  | post

  /--
  Replace a resource with new data.
  -/
  | put

  /--
  Remove a resource.
  -/
  | delete

  /--
  Establish a tunnel to a server (often for TLS).
  -/
  | connect

  /--
  Describe communication options for a resource.
  -/
  | options

  /--
  Perform a message loop-back test.
  -/
  | trace

  /--
  Apply partial modifications to a resource.
  Source: https://www.rfc-editor.org/rfc/rfc5789.html
  -/
  | patch
deriving Repr, Inhabited, BEq, DecidableEq

namespace Method

/--
Converts a `String` into a `Method`.
-/
def ofString? : String → Option Method
  | "GET" => some .get
  | "HEAD" => some .head
  | "POST" => some .post
  | "PUT" => some .put
  | "DELETE" => some .delete
  | "CONNECT" => some .connect
  | "OPTIONS" => some .options
  | "TRACE" => some .trace
  | "PATCH" => some .patch
  | _ => none

/--
Converts a `String` into a `Method`, panics if invalid.
-/
def ofString! (s : String) : Method :=
  match ofString? s with
  | some m => m
  | none => panic! s!"invalid HTTP method: {s.quote}"

instance : ToString Method where
  toString
    | .get => "GET"
    | .head => "HEAD"
    | .post => "POST"
    | .put => "PUT"
    | .delete => "DELETE"
    | .connect => "CONNECT"
    | .options => "OPTIONS"
    | .trace => "TRACE"
    | .patch => "PATCH"

instance : Encode .v11 Method where
  encode buffer := buffer.writeString ∘ toString

end Std.Http.Method
