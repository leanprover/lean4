import Std.Internal.Http.Data.Chunk
import Std.Internal.Http.Data.Request
import Std.Internal.Http.Data.Response

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
info: "999 999"
-/
#guard_msgs in
#eval encodeStr (Status.other 999)

/-! ## Request.Head encoding -/

/--
info: "GET /path HTTP/1.1\x0d\n"
-/
#guard_msgs in
#eval encodeStr ({ method := .get, version := .v11, uri := "/path" } : Request.Head)

/--
info: "POST /submit HTTP/1.1\x0d\n"
-/
#guard_msgs in
#eval encodeStr ({ method := .post, version := .v11, uri := "/submit" } : Request.Head)

/--
info: "PUT /resource HTTP/2.0\x0d\n"
-/
#guard_msgs in
#eval encodeStr ({
    method := .put
    version := .v20
    uri := "/resource"
  } : Request.Head)

/-! ## Response.Head encoding -/

/--
info: "HTTP/1.1 200 OK\x0d\n"
-/
#guard_msgs in
#eval encodeStr ({ status := .ok, version := .v11 } : Response.Head)

/--
info: "HTTP/1.1 404 Not Found\x0d\n"
-/
#guard_msgs in
#eval encodeStr ({ status := .notFound, version := .v11 } : Response.Head)

/--
info: "HTTP/2.0 500 Internal Server Error\x0d\n"
-/
#guard_msgs in
#eval encodeStr ({
    status := .internalServerError
    version := .v20
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
#eval encodeStr (Chunk.ofByteArray "abc".toUTF8 |>.withExtension (.mk "lang") "en")

/--
info: "3;lang=\"en \\\" u\";type=text\x0d\nabc\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Chunk.ofByteArray "abc".toUTF8 |>.withExtension (.mk "lang") "en \" u" |>.withExtension (.mk "type") "text")

/--
info: "a\x0d\n0123456789\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Chunk.ofByteArray "0123456789".toUTF8)

/-! ## Trailer encoding -/

/--
info: "0\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr Trailer.empty

/--
info: "0\x0d\nChecksum: abc123\x0d\n\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Trailer.empty.header "Checksum" "abc123")

/-! ## Request builder -/

/--
info: "GET /index.html HTTP/1.1\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Request.get "/index.html" |>.body ()).head

/--
info: "POST /api/data HTTP/1.1\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Request.post "/api/data" |>.body ()).head

/--
info: "PUT /resource HTTP/1.1\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Request.put "/resource" |>.body ()).head

/--
info: "DELETE /item HTTP/1.1\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Request.delete "/item" |>.body ()).head

/--
info: "PATCH /update HTTP/1.1\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Request.patch "/update" |>.body ()).head

/--
info: "HEAD /check HTTP/1.1\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Request.head' "/check" |>.body ()).head

/--
info: "OPTIONS * HTTP/1.1\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Request.options "*" |>.body ()).head

/--
info: "CONNECT proxy:8080 HTTP/1.1\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Request.connect "proxy:8080" |>.body ()).head

/--
info: "TRACE /debug HTTP/1.1\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Request.trace "/debug" |>.body ()).head

/--
info: "POST /v2 HTTP/2.0\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Request.new |>.method .post |>.uri "/v2" |>.version .v20 |>.body ()).head

/-! ## Response builder -/

/--
info: "HTTP/1.1 200 OK\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Response.ok |>.body ()).head

/--
info: "HTTP/1.1 404 Not Found\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Response.notFound |>.body ()).head

/--
info: "HTTP/1.1 500 Internal Server Error\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Response.internalServerError |>.body ()).head

/--
info: "HTTP/1.1 400 Bad Request\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Response.badRequest |>.body ()).head

/--
info: "HTTP/1.1 201 Created\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Response.created |>.body ()).head

/--
info: "HTTP/1.1 202 Accepted\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Response.accepted |>.body ()).head

/--
info: "HTTP/1.1 401 Unauthorized\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Response.unauthorized |>.body ()).head

/--
info: "HTTP/1.1 403 Forbidden\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Response.forbidden |>.body ()).head

/--
info: "HTTP/1.1 409 Conflict\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Response.conflict |>.body ()).head

/--
info: "HTTP/1.1 503 Service Unavailable\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Response.serviceUnavailable |>.body ()).head

/--
info: "HTTP/1.1 418 I'm a teapot\x0d\n"
-/
#guard_msgs in
#eval encodeStr (Response.withStatus .imATeapot |>.body ()).head
