import Std.Internal.Http.Data.Headers

open Std.Http
open Std.Http.Header

/-! ## Header.Name tests -/

-- Valid header names
#guard (Name.ofString? "content-type").isSome
#guard (Name.ofString? "host").isSome
#guard (Name.ofString? "x-custom-header").isSome
#guard (Name.ofString? "accept").isSome

-- Invalid header names (empty, spaces, control chars)
#guard (Name.ofString? "").isNone
#guard (Name.ofString? "invalid header").isNone
#guard (Name.ofString? "bad\nname").isNone
#guard (Name.ofString? "bad\x00name").isNone
#guard (Name.ofString? "bad(name").isNone
#guard (Name.ofString? "bad)name").isNone
#guard (Name.ofString? "bad,name").isNone
#guard (Name.ofString? "bad;name").isNone
#guard (Name.ofString? "bad[name").isNone
#guard (Name.ofString? "bad]name").isNone
#guard (Name.ofString? "bad{name").isNone
#guard (Name.ofString? "bad}name").isNone
#guard (Name.ofString? "bad\"name").isNone

-- Case normalization
/--
info: "content-type"
-/
#guard_msgs in
#eval (Name.ofString! "Content-Type").value

/--
info: "content-type"
-/
#guard_msgs in
#eval (Name.ofString! "CONTENT-TYPE").value

-- Canonical form
/--
info: "Content-Type"
-/
#guard_msgs in
#eval toString (Name.ofString! "content-type")

/--
info: "X-Custom-Header"
-/
#guard_msgs in
#eval toString (Name.ofString! "x-custom-header")

/--
info: "Host"
-/
#guard_msgs in
#eval toString (Name.ofString! "host")

-- Name.is case-insensitive comparison
#guard (Name.ofString! "content-type").is "Content-Type"
#guard (Name.ofString! "content-type").is "CONTENT-TYPE"
#guard (Name.ofString! "content-type").is "content-type"
#guard !(Name.ofString! "content-type").is "host"

-- Predefined names
#guard Name.contentType.value == "content-type"
#guard Name.contentLength.value == "content-length"
#guard Name.host.value == "host"
#guard Name.authorization.value == "authorization"
#guard Name.userAgent.value == "user-agent"
#guard Name.accept.value == "accept"
#guard Name.connection.value == "connection"
#guard Name.transferEncoding.value == "transfer-encoding"
#guard Name.server.value == "server"

-- Name equality
#guard Name.ofString! "content-type" == Name.ofString! "Content-Type"
#guard Name.ofString! "HOST" == Name.ofString! "host"
#guard !(Name.ofString! "content-type" == Name.ofString! "host")

/-! ## Header.Value tests -/

-- Valid header values (printable ASCII, tab, space)
#guard (Value.ofString? "text/html").isSome
#guard (Value.ofString? "application/json; charset=utf-8").isSome
#guard (Value.ofString? "").isSome
#guard (Value.ofString? "value with spaces").isSome
#guard (Value.ofString? "value\twith\ttabs").isSome

-- Invalid header values (control characters except tab)
#guard (Value.ofString? "bad\x00value").isNone
#guard (Value.ofString? "bad\nvalue").isNone
#guard (Value.ofString? "bad\rvalue").isNone

-- Value.is case-insensitive comparison
#guard (Value.ofString! "text/html").is "TEXT/HTML"
#guard (Value.ofString! "text/html").is "text/html"
#guard !(Value.ofString! "text/html").is "application/json"

-- Value toString
/--
info: "text/html"
-/
#guard_msgs in
#eval toString (Value.ofString! "text/html")

/-! ## Headers collection tests -/

-- Empty headers
#guard Headers.empty.isEmpty
#guard Headers.empty.size == 0

-- Add and retrieve
#guard (Headers.empty.insert! "content-type" "text/html").size == 1
#guard !(Headers.empty.insert! "content-type" "text/html").isEmpty
#guard (Headers.empty.insert! "content-type" "text/html").contains (Name.ofString! "content-type")

-- get? retrieves the value
/--
info: "text/html"
-/
#guard_msgs in
#eval do
  let h := Headers.empty.insert! "content-type" "text/html"
  return (h.get? (Name.ofString! "content-type")).get!.value

-- get? returns none for missing headers
#guard (Headers.empty.get? (Name.ofString! "content-type")).isNone

-- Multiple headers
#guard
  let h := Headers.empty
    |>.insert! "content-type" "text/html"
    |>.insert! "host" "example.com"
    |>.insert! "accept" "application/json"
  h.size == 3

#guard
  let h := Headers.empty.insert! "host" "example.com"
  h.contains (Name.ofString! "host") && !h.contains (Name.ofString! "accept")

#guard
  let h := Headers.empty
    |>.insert! "content-type" "text/html"
    |>.insert! "host" "example.com"
  let h' := h.erase (Name.ofString! "content-type")
  !h'.contains (Name.ofString! "content-type") && h'.contains (Name.ofString! "host")

#guard
  let h := Headers.empty
    |>.insert! "content-type" "text/html"
    |>.insert! "host" "example.com"
  (h.erase (Name.ofString! "content-type")).size == 1

-- hasEntry
#guard
  let h := Headers.empty.insert! "content-type" "text/html"
  h.hasEntry (Name.ofString! "content-type") (Value.ofString! "text/html")

#guard
  let h := Headers.empty.insert! "content-type" "text/html"
  !h.hasEntry (Name.ofString! "content-type") (Value.ofString! "application/json")

-- update existing
/--
info: "TEXT/HTML"
-/
#guard_msgs in
#eval do
  let h := Headers.empty.insert! "content-type" "text/html"
  let h' := h.update (Name.ofString! "content-type") (fun
    | some v => Value.ofString! v.value.toUpper
    | none => Value.ofString! "default")
  return (h'.get? (Name.ofString! "content-type")).get!.value

-- update missing (inserts)
/--
info: "default-value"
-/
#guard_msgs in
#eval do
  let h := Headers.empty
  let h' := h.update (Name.ofString! "x-new") (fun
    | some v => v
    | none => Value.ofString! "default-value")
  return (h'.get? (Name.ofString! "x-new")).get!.value

-- ofList
#guard
  let h := Headers.ofList [
    (Name.ofString! "host", Value.ofString! "example.com"),
    (Name.ofString! "accept", Value.ofString! "*/*")
  ]
  h.size == 2 && h.contains (Name.ofString! "host")

-- merge
#guard
  let h1 := Headers.empty.insert! "content-type" "text/html"
  let h2 := Headers.empty.insert! "host" "example.com"
  let merged := h1.merge h2
  merged.contains (Name.ofString! "content-type") && merged.contains (Name.ofString! "host")

-- filter
#guard
  let h := Headers.empty
    |>.insert! "content-type" "text/html"
    |>.insert! "host" "example.com"
    |>.insert! "accept" "application/json"
  let filtered := h.filter (fun name _ => name.is "host")
  filtered.size == 1 && filtered.contains (Name.ofString! "host")

-- fold
/--
info: 3
-/
#guard_msgs in
#eval do
  let h := Headers.empty
    |>.insert! "a" "1"
    |>.insert! "b" "2"
    |>.insert! "c" "3"
  return h.fold 0 (fun acc _ _ => acc + 1)

-- getD with default
/--
info: "fallback"
-/
#guard_msgs in
#eval do
  let h := Headers.empty
  return (h.getD (Name.ofString! "missing") (Value.ofString! "fallback")).value

-- mapValues
/--
info: "TEXT/HTML"
-/
#guard_msgs in
#eval do
  let h := Headers.empty.insert! "content-type" "text/html"
  let h' := h.mapValues (fun _ v => Value.ofString! v.value.toUpper)
  return (h'.get? (Name.ofString! "content-type")).get!.value

/-! ## Header typeclass tests -/

-- ContentLength parse
#guard
  match Header.ContentLength.parse (Value.ofString! "42") with
  | some cl => cl.length == 42
  | none => false

#guard
  match Header.ContentLength.parse (Value.ofString! "0") with
  | some cl => cl.length == 0
  | none => false

#guard (Header.ContentLength.parse =<< (Value.ofString! "abc")).isNone
#guard (Header.ContentLength.parse =<< (Value.ofString? "")).isNone

/--
info: ("content-length", "42")
-/
#guard_msgs in
#eval do
  let (name, value) := Header.ContentLength.serialize ⟨42⟩
  return (name.value, value.value)

#guard
  match Header.TransferEncoding.parse (Value.ofString! "chunked") with
  | some te => te.isChunked
  | none => false

#guard
  match Header.TransferEncoding.parse (Value.ofString! "gzip, chunked") with
  | some te => te.isChunked && te.codings.size == 2
  | none => false

#guard
  match Header.TransferEncoding.parse (Value.ofString! "gzip") with
  | some te => !te.isChunked
  | none => false

#guard (Header.TransferEncoding.parse =<< (Value.ofString? "chunked, gzip")).isNone
#guard (Header.TransferEncoding.parse =<< (Value.ofString? "chunked, chunked")).isNone
#guard (Header.TransferEncoding.parse =<< (Value.ofString? "")).isNone
#guard (Header.TransferEncoding.parse =<< (Value.ofString? ",")).isNone
#guard (Header.TransferEncoding.parse =<< (Value.ofString? " , , ")).isNone

/--
info: ("transfer-encoding", "gzip,chunked")
-/
#guard_msgs in
#eval do
  let te : Header.TransferEncoding := ⟨#["gzip", "chunked"], by native_decide⟩
  let (name, value) := Header.TransferEncoding.serialize te
  return (name.value, value.value)
