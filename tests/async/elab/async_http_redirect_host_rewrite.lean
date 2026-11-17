import Std.Http.Protocol.H1

open Std.Http
open Std.Http.Protocol.H1

/-!
Tests how `decideRedirect` rewrites `Host` on a cross-origin hop. The redirected request carries a
single `Host` for the new origin, in the place of the first `Host` it had, even when the original
request carried several (RFC 9112 §3.2 allows one): no `Host` line may keep naming the previous
origin. A request without `Host` gets none, and a same-origin hop leaves the fields as they were.
-/

private def origin : URI.Origin :=
  let base := URI.parse! "http://example.com/a"
  { scheme := base.scheme, host := base.host?.get!, port := base.port }

private def mkReq (fields : List (String × String)) : Request.Head :=
  { method := .get, version := .v11, uri := RequestTarget.originForm! "/a",
    headers := fields.foldl (fun h (n, v) => h.insert! n v) Headers.empty }

/-- The redirected request's fields for a 302 to `location`, or `none` when it is not followed. -/
private def redirectedFields (fields : List (String × String)) (location : String) :
    Option (List (String × String)) :=
  match decideRedirect origin (mkReq fields) true .found
      (Headers.empty.insert! "Location" location) with
  | .follow plan => some (plan.headers.toArray.toList.map fun (n, v) => (n.value, v.value))
  | .done => none

-- Two `Host` lines become one `Host` for the new origin, where the first was.
#guard redirectedFields [("Host", "example.com"), ("Accept", "*/*"), ("Host", "example.com")]
    "http://other.com/x" ==
  some [("host", "other.com"), ("accept", "*/*")]

#guard redirectedFields [("Accept", "*/*"), ("Host", "example.com"), ("X-A", "1"), ("Host", "evil")]
    "http://other.com:8080/x" ==
  some [("accept", "*/*"), ("host", "other.com:8080"), ("x-a", "1")]

-- A single `Host` keeps its place.
#guard redirectedFields [("Host", "example.com"), ("Accept", "*/*")] "http://other.com/x" ==
  some [("host", "other.com"), ("accept", "*/*")]

-- Without `Host`, none is added.
#guard redirectedFields [("Accept", "*/*")] "http://other.com/x" == some [("accept", "*/*")]

-- A same-origin hop leaves `Host` as it was.
#guard redirectedFields [("Host", "example.com"), ("Host", "example.com")] "/x" ==
  some [("host", "example.com"), ("host", "example.com")]
