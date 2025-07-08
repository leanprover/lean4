/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init.Data

namespace Std
namespace Internal
namespace Http
namespace Data

/-
A method is a verb that describes the action to be performed.

* Reference: https://httpwg.org/specs/rfc9110.html#methods
-/
inductive Method where
  | get
  | head
  | post
  | put
  | delete
  | connect
  | options
  | trace
  | patch
  deriving Repr, Inhabited, BEq

namespace Method

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

def fromString? : String → Option Method
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
Request methods are considered safe if their defined semantics are essentially read-only.

* Reference: https://httpwg.org/specs/rfc9110.html#metho  d.properties
-/
def isSafe : Method → Prop
  | .get | .head | .options | .trace => True
  | _ => False

/--
A request method is considered idempotent if the intended effect on the server of multiple
identical requests with that method is the same as the effect for a single such request.

* Reference: https://httpwg.org/specs/rfc9110.html#idempotent.methods
-/
def isIdempotent : Method → Prop
  | .get | .head | .options | .trace => True
  | .put | .delete => True
  | _ => False

/--
Checks if the given method allows a request body. GET and HEAD methods do not typically allow
request bodies.

* Reference: https://developer.mozilla.org/en-US/docs/Web/HTTP/Methods
-/
def allowsRequestBody : Method → Bool
  | .get | .head => False
  | _ => True

end Method
end Data
end Http
end Internal
end Std
