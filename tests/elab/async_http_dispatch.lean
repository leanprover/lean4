import Std.Http.Test.Helpers

open Std.Async
open Std Http Internal Test

-- Basic method dispatch and streaming responses

#eval runGroup "Basic dispatch" do
  check "GET with Content-Length header → 200"
    (raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 7\x0d\nConnection: close\x0d\n\x0d\nsurvive")
    (handler := fun req => do
      if req.line.method == .get && req.line.headers.hasEntry (.mk "content-length") (.ofString! "7")
      then Response.ok |>.text "ok"
      else Response.badRequest |>.text "bad")
    (expect := fun r => assertStatus r "HTTP/1.1 200" *> assertContains r "ok")

  check "GET → 200 with body"
    (raw := mkGetClose "/api/users")
    (handler := fun req => do
      if req.line.method == .get then Response.ok |>.text "users list"
      else Response.notFound |>.text "")
    (expect := fun r => assertStatus r "HTTP/1.1 200" *> assertContains r "users list")

  check "POST with JSON body → 201 Created"
    (raw := mkPost "/api/users" "{\"name\":\"Alice\"}" "Content-Type: application/json\x0d\nConnection: close\x0d\n")
    (handler := fun req => do
      if req.line.headers.hasEntry (.mk "content-type") (.ofString! "application/json")
      then Response.new |>.status .created |>.text "Created"
      else Response.badRequest |>.text "")
    (expect := fun r => assertStatus r "HTTP/1.1 201" *> assertContains r "Created")

  check "DELETE → 204 No Content"
    (raw := "DELETE /api/users/123 HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := fun req => do
      if req.line.method == .delete then Response.new |>.status .noContent |>.text ""
      else Response.notFound |>.text "")
    (expect := fun r => assertStatus r "HTTP/1.1 204")

  check "HEAD → headers present, body absent"
    (raw := "HEAD /api/users HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := fun req => do
      if req.line.method == .head then Response.ok |>.text ""
      else Response.notFound |>.text "")
    (expect := fun r => assertStatus r "HTTP/1.1 200" *> assertAbsent r "\x0d\n\x0d\nX")

  check "OPTIONS with Allow header"
    (raw := "OPTIONS * HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := fun req => do
      if req.line.method == .options
      then Response.ok |>.header! "Allow" "GET, POST, DELETE, OPTIONS" |>.text ""
      else Response.badRequest |>.text "")
    (expect := fun r => assertStatus r "HTTP/1.1 200" *> assertContains r "Allow: GET")

  check "multiple request headers preserved"
    (raw := "GET /api/data HTTP/1.1\x0d\nHost: api.example.com\x0d\nAccept: application/json\x0d\nAuthorization: Bearer tok\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := fun req => do
      if req.line.headers.hasEntry (.mk "authorization") (.ofString! "Bearer tok") &&
         req.line.headers.hasEntry (.mk "accept") (.ofString! "application/json")
      then Response.ok |>.text "authenticated"
      else Response.new |>.status .unauthorized |>.text "unauthorized")
    (expect := fun r => assertStatus r "HTTP/1.1 200" *> assertContains r "authenticated")

  check "query parameters preserved in URI"
    (raw := mkGetClose "/api/search?q=test&limit=10")
    (handler := fun req => do
      if toString req.line.uri == "/api/search?q=test&limit=10"
      then Response.ok |>.text "results"
      else Response.notFound |>.text "")
    (expect := fun r => assertStatus r "HTTP/1.1 200" *> assertContains r "results")

  check "POST with empty body (CL: 0) → 202 Accepted"
    (raw := "POST /api/trigger HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := fun req => do
      if req.line.headers.hasEntry (.mk "content-length") (.ofString! "0")
      then Response.new |>.status .accepted |>.text "triggered"
      else Response.badRequest |>.text "")
    (expect := fun r => assertStatus r "HTTP/1.1 202" *> assertContains r "triggered")

  check "URI with percent-encoded characters"
    (raw := mkGetClose "/api/users/%C3%A9")
    (handler := fun req => do
      if toString req.line.uri == "/api/users/%C3%A9"
      then Response.ok |>.text "found"
      else Response.notFound |>.text "")
    (expect := fun r => assertStatus r "HTTP/1.1 200" *> assertContains r "found")

  check "custom response headers preserved"
    (raw := mkGetClose "/api/data")
    (handler := fun _ =>
      Response.ok
        |>.header! "Cache-Control" "no-cache"
        |>.header! "X-Custom-Header" "custom-value"
        |>.text "data")
    (expect := fun r =>
      assertStatus r "HTTP/1.1 200" *>
      assertContains r "Cache-Control: no-cache" *>
      assertContains r "X-Custom-Header: custom-value")

  check "custom status code (418 I'm a teapot)"
    (raw := mkGetClose "/api/teapot")
    (handler := fun _ => Response.new |>.status .imATeapot |>.text "I'm a teapot")
    (expect := fun r => assertStatus r "HTTP/1.1 418" *> assertContains r "I'm a teapot")

  check "large response body (1000 bytes)"
    (raw := mkGetClose "/api/large")
    (handler := fun _ => Response.ok |>.text (String.ofList (List.replicate 1000 'X')))
    (expect := fun r => assertStatus r "HTTP/1.1 200" *> assertContains r "Content-Length: 1000")

-- Streaming responses

#eval runGroup "Streaming responses" do
  check "streaming with explicit Content-Length"
    (raw := mkGetClose "/stream")
    (handler := fun _ => do
      let stream ← Body.mkStream
      background do
        for i in [0:3] do
          let sleep ← Sleep.mk 5
          sleep.wait
          stream.send <| Chunk.ofByteArray s!"chunk{i}\n".toUTF8
        stream.close
      return Response.ok
        |>.header (.mk "content-length") (.mk "21")
        |>.body stream)
    (expect := fun r =>
      assertStatus r "HTTP/1.1 200" *>
      assertContains r "Content-Length: 21" *>
      assertContains r "chunk0")

  check "streaming with setKnownSize"
    (raw := mkGetClose "/stream-sized")
    (handler := fun _ => do
      let stream ← Body.mkStream
      stream.setKnownSize (some (.fixed 15))
      background do
        for i in [0:3] do
          stream.send <| Chunk.ofByteArray s!"data{i}".toUTF8
        stream.close
      return Response.ok |>.body stream)
    (expect := fun r =>
      assertStatus r "HTTP/1.1 200" *>
      assertContains r "Content-Length: 15" *>
      assertContains r "data0")

  check "streaming chunked encoding (unknown size)"
    (raw := mkGetClose "/stream-chunked")
    (handler := fun _ => do
      let stream ← Body.mkStream
      background do
        stream.send <| Chunk.ofByteArray "hello".toUTF8
        stream.send <| Chunk.ofByteArray "world".toUTF8
        stream.close
      return Response.ok |>.body stream)
    (expect := fun r =>
      assertStatus r "HTTP/1.1 200" *>
      assertContains r "Transfer-Encoding: chunked" *>
      assertContains r "hello" *>
      assertContains r "world")

  check "chunked request + streaming response"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\ndata1\x0d\n5\x0d\ndata2\x0d\n0\x0d\n\x0d\n")
    (handler := fun req => do
      let stream ← Body.mkStream
      let te := req.line.headers.get? (.mk "transfer-encoding")
      if te.isSome then
        background do
          stream.send <| Chunk.ofByteArray "response0".toUTF8
          stream.send <| Chunk.ofByteArray "response1".toUTF8
          stream.close
        return Response.ok
          |>.header (.mk "content-length") (.mk "18")
          |>.body stream
      else
        stream.close
        return Response.badRequest |>.body stream)
    (expect := fun r =>
      assertStatus r "HTTP/1.1 200" *>
      assertContains r "response0" *>
      assertContains r "response1")

  check "fixed-length overflow: output stops at announced length"
    (raw := mkGetClose "/overflow")
    (handler := fun _ => do
      let stream ← Body.mkStream
      background do
        stream.send <| Chunk.ofByteArray "abcdef".toUTF8
        stream.close
      return Response.ok
        |>.header (.mk "content-length") (.mk "3")
        |>.body stream)
    (expect := fun r =>
      assertStatus r "HTTP/1.1 200" *>
      assertContains r "Content-Length: 3")
