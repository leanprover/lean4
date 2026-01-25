import Std.Internal.Http.Data.Request
import Std.Internal.Http.Data.Response

open Std.Http
open Std.Http.Internal

private def encodeStr [Encode .v11 t] (v : t) : String :=
  String.fromUTF8! (Encode.encode (v := .v11) ChunkedBuffer.empty v).toByteArray

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
