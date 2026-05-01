import Std.Http.Data.Chunk
import Std.Http.Data.Request
import Std.Http.Data.Response

open Std.Http
open Std.Http.Internal

private def encodeStr [Encode .v11 t] (v : t) : String :=
  String.fromUTF8! (Encode.encode (v := .v11) ChunkedBuffer.empty v).toByteArray

/-! ## Version encoding -/

/--
info: "HTTP/1.1"
-/
#guard_msgs in
#eval encodeStr Version.v11

/--
info: "HTTP/2.0"
-/
#guard_msgs in
#eval encodeStr Version.v20

/--
info: "HTTP/3.0"
-/
#guard_msgs in
#eval encodeStr Version.v30

/-! ## Method encoding -/

/--
info: "GET"
-/
#guard_msgs in
#eval encodeStr Method.get

/--
info: "HEAD"
-/
#guard_msgs in
#eval encodeStr Method.head

/--
info: "POST"
-/
#guard_msgs in
#eval encodeStr Method.post

/--
info: "PUT"
-/
#guard_msgs in
#eval encodeStr Method.put

/--
info: "DELETE"
-/
#guard_msgs in
#eval encodeStr Method.delete

/--
info: "CONNECT"
-/
#guard_msgs in
#eval encodeStr Method.connect

/--
info: "OPTIONS"
-/
#guard_msgs in
#eval encodeStr Method.options

/--
info: "TRACE"
-/
#guard_msgs in
#eval encodeStr Method.trace

/--
info: "PATCH"
-/
#guard_msgs in
#eval encodeStr Method.patch

/-! ## Status encoding -/

/--
info: "200 OK"
-/
#guard_msgs in
#eval encodeStr Status.ok

/--
info: "201 Created"
-/
#guard_msgs in
#eval encodeStr Status.created

/--
info: "404 Not Found"
-/
#guard_msgs in
#eval encodeStr Status.notFound

/--
info: "500 Internal Server Error"
-/
#guard_msgs in
#eval encodeStr Status.internalServerError

/--
info: "999 Unknown"
-/
#guard_msgs in
#eval encodeStr (Status.other ⟨999, "Unknown", by decide, by decide, by decide⟩)

/-! ## Request.line encoding -/

/--
info: ""
-/
#guard_msgs in
#eval encodeStr Headers.empty

/--
info: "Content-Type: text/html\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Headers.empty.insert! "content-type" "text/html")

/--
info: "X-Custom-Header: value\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Headers.empty.insert! "x-custom-header" "value")


/--
info: "GET /path HTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr ({ method := .get, version := .v11, uri := .parse! "/path" } : Request.Head)

/--
info: "POST /submit HTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr ({ method := .post, version := .v11, uri := .parse! "/submit" } : Request.Head)

/--
info: "PUT /resource HTTP/2.0\x0d\nContent-Type: application/json\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr ({
    method := .put
    version := .v20
    uri := .parse! "/resource"
    headers := Headers.empty.insert! "content-type" "application/json"
  } : Request.Head)

/-! ## Response.line encoding -/

/--
info: "HTTP/1.1 200 OK\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr ({ status := .ok, version := .v11 } : Response.Head)

/--
info: "HTTP/1.1 404 Not Found\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr ({ status := .notFound, version := .v11 } : Response.Head)

/--
info: "HTTP/2.0 500 Internal Server Error\x0d\nContent-Type: text/plain\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr ({
    status := .internalServerError
    version := .v20
    headers := Headers.empty.insert! "content-type" "text/plain"
  } : Response.Head)

/-! ## Chunk encoding -/

/--
info: "5\x0d\nhello\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Chunk.ofByteArray "hello".toUTF8)

/--
info: "0\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr Chunk.empty

/--
info: "3;lang=en\x0d\nabc\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Chunk.ofByteArray "abc".toUTF8 |>.insertExtension (Chunk.ExtensionName.mk "lang") (.ofString! "en"))

/--
info: "3;lang=\"en \\\" u\";type=text\x0d\nabc\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Chunk.ofByteArray "abc".toUTF8 |>.insertExtension (Chunk.ExtensionName.mk "lang") (.ofString! "en \" u") |>.insertExtension (Chunk.ExtensionName.mk "type") (.ofString! "text"))

/--
info: "a\x0d\n0123456789\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Chunk.ofByteArray "0123456789".toUTF8)

/-! ## Request builder -/

/--
info: "GET /index.html HTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Request.get (.parse! "/index.html") |>.body ()).line

/--
info: "POST /api/data HTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Request.post (.parse! "/api/data") |>.body ()).line

/--
info: "PUT /resource HTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Request.put (.parse! "/resource") |>.body ()).line

/--
info: "DELETE /item HTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Request.delete (.parse! "/item") |>.body ()).line

/--
info: "PATCH /update HTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Request.patch (.parse! "/update") |>.body ()).line

/--
info: "HEAD /check HTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Request.head (.parse! "/check") |>.body ()).line

/--
info: "OPTIONS * HTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Request.options (.parse! "*") |>.body ()).line

/--
info: "CONNECT proxy:8080 HTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Request.connect (.parse! "proxy:8080") |>.body ()).line

/--
info: "TRACE /debug HTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Request.trace (.parse! "/debug") |>.body ()).line

/--
info: "POST /v2 HTTP/2.0\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Request.new |>.method .post |>.uri (.parse! "/v2") |>.version .v20 |>.body ()).line

/-! ## Response builder -/

/--
info: "HTTP/1.1 200 OK\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Response.ok |>.body ()).line

/--
info: "HTTP/1.1 404 Not Found\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Response.notFound |>.body ()).line

/--
info: "HTTP/1.1 500 Internal Server Error\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Response.internalServerError |>.body ()).line

/--
info: "HTTP/1.1 400 Bad Request\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Response.badRequest |>.body ()).line

/--
info: "HTTP/1.1 201 Created\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Response.created |>.body ()).line

/--
info: "HTTP/1.1 202 Accepted\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Response.accepted |>.body ()).line

/--
info: "HTTP/1.1 401 Unauthorized\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Response.unauthorized |>.body ()).line

/--
info: "HTTP/1.1 403 Forbidden\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Response.forbidden |>.body ()).line

/--
info: "HTTP/1.1 409 Conflict\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Response.conflict |>.body ()).line

/--
info: "HTTP/1.1 503 Service Unavailable\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Response.serviceUnavailable |>.body ()).line

/--
info: "HTTP/1.1 418 I'm a teapot\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Response.withStatus .imATeapot |>.body ()).line

/-! ## Edge cases: Status encoding -/

-- Status.other 104: minimum valid non-known code (100–103 are all named)
/--
info: "999 Unknown"
-/
#guard_msgs in
#eval encodeStr (Status.other ⟨999, "Unknown", by decide, by decide, by decide⟩)

-- Status.other 209: non-named code between two known blocks
/--
info: "888 Unknown"
-/
#guard_msgs in
#eval encodeStr (Status.other ⟨888, "Unknown", by decide, by decide, by decide⟩)

-- Status.other 999: maximum valid code
/--
info: "999 Unknown"
-/
#guard_msgs in
#eval encodeStr (Status.other ⟨999, "Unknown", by decide, by decide, by decide⟩)

-- Non-standard status code in the middle
/--
info: "299 Unknown"
-/
#guard_msgs in
#eval encodeStr (Status.other ⟨299, "Unknown", by decide, by decide, by decide⟩)

/-! ## Edge cases: Chunk size hex encoding -/

-- Size 16 → hex "10" (first two-digit hex)
/--
info: "10\x0d\n0123456789abcdef\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Chunk.ofByteArray "0123456789abcdef".toUTF8)

-- Size 255 → hex "ff": verify prefix
/--
info: true
-/
#guard_msgs in
#eval do
  let data := ByteArray.mk (Array.replicate 255 (0x41 : UInt8))
  return encodeStr (Chunk.ofByteArray data) |>.startsWith "ff\r\n"

-- Size 256 → hex "100" (first three-digit hex): verify prefix
/--
info: true
-/
#guard_msgs in
#eval do
  let data := ByteArray.mk (Array.replicate 256 (0x41 : UInt8))
  return encodeStr (Chunk.ofByteArray data) |>.startsWith "100\r\n"

-- Size 15 → hex "f" (largest single hex digit)
/--
info: "f\x0d\n0123456789abcde\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Chunk.ofByteArray "0123456789abcde".toUTF8)

-- Chunk.ofByteArray with empty data encodes as the last-chunk terminator.
/--
info: "0\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Chunk.ofByteArray ByteArray.empty)

/-! ## Edge cases: Chunk extensions -/

-- Extension with no value (None case) via direct struct construction
/--
info: "3;marker\x0d\nabc\x0d\n"
-/
#guard_msgs in
#eval encodeStr ({ data := "abc".toUTF8, extensions := #[(Chunk.ExtensionName.mk "marker", none)] } : Chunk)

-- Extension with empty string value (not quoted since "".any returns false)
/--
info: "3;key=\"\"\x0d\nabc\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Chunk.ofByteArray "abc".toUTF8 |>.insertExtension (Chunk.ExtensionName.mk "key") (.ofString! ""))

-- Extension value that is all token chars (no quoting needed)
/--
info: "3;key=abc123\x0d\nabc\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Chunk.ofByteArray "abc".toUTF8 |>.insertExtension (Chunk.ExtensionName.mk "key") (.ofString! "abc123"))

-- Extension value with space (must be quoted)
/--
info: "3;key=\"hello world\"\x0d\nabc\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Chunk.ofByteArray "abc".toUTF8 |>.insertExtension (Chunk.ExtensionName.mk "key") (.ofString! "hello world"))

-- Extension value with backslash (must be escaped)
/--
info: "3;key=\"a\\\\b\"\x0d\nabc\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Chunk.ofByteArray "abc".toUTF8 |>.insertExtension (Chunk.ExtensionName.mk "key") (.ofString! "a\\b"))

-- Multiple extensions with no value and with value
/--
info: "3;a;b=1\x0d\nabc\x0d\n"
-/
#guard_msgs in
#eval encodeStr ({ data := "abc".toUTF8, extensions := #[(Chunk.ExtensionName.mk "a", none), (Chunk.ExtensionName.mk "b", some (.ofString! "1"))] } : Chunk)

/-! ## Trailer encoding -/

-- Empty trailer: terminal chunk + CRLF
/--
info: "0\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr Trailer.empty

-- Trailer with a single header
/--
info: "0\x0d\nChecksum: abc123\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Trailer.empty.insert! "checksum" "abc123")

-- Trailer with a single header
/--
info: "0\x0d\nChecksum: abc 123\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Trailer.empty.insert! "checksum" "abc 123")


-- Trailer with multiple headers
/--
info: "0\x0d\nChecksum: abc123\x0d\nExpires: Thu, 01 Dec 2025 16:00:00 GMT\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Trailer.empty.insert! "checksum" "abc123" |>.insert! "expires" "Thu, 01 Dec 2025 16:00:00 GMT")

/-! ## Edge cases: Trailer validation -/

-- Empty header name is rejected
/--
info: true
-/
#guard_msgs in
#eval (Header.Name.ofString? "" |>.isNone : Bool)

-- Header name with spaces is rejected
/--
info: true
-/
#guard_msgs in
#eval (Header.Name.ofString? "bad name" |>.isNone : Bool)

-- Header name with colon is rejected
/--
info: true
-/
#guard_msgs in
#eval (Header.Name.ofString? "bad:name" |>.isNone : Bool)

-- Header name with newline is rejected
/--
info: true
-/
#guard_msgs in
#eval (Header.Name.ofString? "bad\nname" |>.isNone : Bool)

-- Header value with newline is rejected
/--
info: true
-/
#guard_msgs in
#eval (Header.Value.ofString? "bad\nvalue" |>.isNone : Bool)

-- Header value with null byte is rejected
/--
info: true
-/
#guard_msgs in
#eval (Header.Value.ofString? "bad\x00value" |>.isNone : Bool)

-- Header value with carriage return is rejected
/--
info: true
-/
#guard_msgs in
#eval (Header.Value.ofString? "bad\rvalue" |>.isNone : Bool)

-- Valid header name succeeds
/--
info: true
-/
#guard_msgs in
#eval (Header.Name.ofString? "content-type" |>.isSome : Bool)

-- Valid header value with tab succeeds (tab is allowed per RFC)
/--
info: true
-/
#guard_msgs in
#eval (Header.Value.ofString? "value\twith-tab" |>.isSome : Bool)

-- Empty header value is valid
/--
info: true
-/
#guard_msgs in
#eval (Header.Value.ofString? "" |>.isSome : Bool)

-- Header value with DEL character (0x7F) is rejected
/--
info: true
-/
#guard_msgs in
#eval (Header.Value.ofString? (String.ofList [Char.ofNat 0x7F]) |>.isNone : Bool)

/-! ## Edge cases: Request URI encoding -/

-- URI with query parameters
/--
info: "GET /search?q=hello&lang=en HTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr ({ method := .get, version := .v11, uri := .parse! "/search?q=hello&lang=en" } : Request.Head)

-- URI with percent-encoded characters
/--
info: "GET /path%20with%20spaces HTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr ({ method := .get, version := .v11, uri :=.parse!  "/path%20with%20spaces" } : Request.Head)

/-! ## Edge cases: Response with unusual statuses -/

/--
info: "HTTP/1.1 100 Continue\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr ({ status := .«continue», version := .v11 } : Response.Head)

/--
info: "HTTP/1.1 204 No Content\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr ({ status := .noContent, version := .v11 } : Response.Head)

/--
info: "HTTP/1.1 301 Moved Permanently\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr ({ status := .movedPermanently, version := .v11 } : Response.Head)

/--
info: "HTTP/3.0 200 OK\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr ({ status := .ok, version := .v30 } : Response.Head)
