import Std.Http.Test.Helpers

open Std.Async
open Std Http Internal Test

-- RFC 9112 §6: Transfer-Encoding and Content-Length framing

#eval runGroup "RFC 9112 §6: chunked body baseline" do
  check "CL body accepted and echoed"
    (raw := mkPost "/echo" "hello" "Connection: close\x0d\n")
    (handler := echoHandler)
    (expect := fun r => assertStatus r "HTTP/1.1 200" *> assertContains r "hello")

  check "chunked body accepted and echoed"
    (raw := mkChunked "/" (chunk "hello" ++ chunkEnd) "Connection: close\x0d\n")
    (handler := echoHandler)
    (expect := fun r => assertStatus r "HTTP/1.1 200" *> assertContains r "hello")

  check "chunk-size uppercase and leading zeros accepted"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n000A\x0d\n0123456789\x0d\n0\x0d\n\x0d\n")
    (handler := echoHandler)
    (expect := fun r => assertStatus r "HTTP/1.1 200" *> assertContains r "0123456789")

  check "chunk extensions with token and quoted value accepted"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;ext=val;quoted=\"ok\"\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := echoHandler)
    (expect := fun r => assertStatus r "HTTP/1.1 200" *> assertContains r "hello")

#eval runGroup "RFC 9112 §6: chunked parse errors" do
  check "invalid chunk-size token → 400"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\nG\x0d\nabc\x0d\n0\x0d\n\x0d\n")
    (handler := echoHandler)
    (expect := (assertExact · r400))

  checkClose "chunk terminator must be CRLF → 400"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nxxx__1a\x0d\n")
    (handler := echoHandler)
    (expect := (assertExact · r400))

  checkClose "missing terminal 0-chunk at EOF → 400"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n")
    (handler := echoHandler)
    (expect := (assertExact · r400))

  check "chunk-size trailing whitespace → 400"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5 \x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := echoHandler)
    (expect := (assertExact · r400))

#eval runGroup "RFC 9112 §6.1: Transfer-Encoding validation (Critical)" do
  -- TE + CL → request smuggling prevention
  check "TE + Content-Length → 400"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := (assertExact · r400))

  -- chunked must be the last coding
  check "TE: chunked not last (chunked, gzip) → 400"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked, gzip\x0d\nConnection: close\x0d\n\x0d\nbody")
    (handler := okHandler)
    (expect := (assertExact · r400))

  check "TE: duplicate chunked → 400"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked, chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := (assertExact · r400))

  check "TE: gzip alone (no chunked framing) → 400"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: gzip\x0d\nConnection: close\x0d\n\x0d\nbody")
    (handler := okHandler)
    (expect := (assertExact · r400))

  check "TE: deflate alone → 400"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: deflate\x0d\nConnection: close\x0d\n\x0d\nbody")
    (handler := okHandler)
    (expect := (assertExact · r400))

  check "TE: identity alone → 400"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: identity\x0d\nConnection: close\x0d\n\x0d\nbody")
    (handler := okHandler)
    (expect := (assertExact · r400))

  check "TE: malformed token list (leading comma) → 400"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: ,chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := (assertExact · r400))

  check "TE: duplicate header lines with unsupported coding → 400"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nTransfer-Encoding: gzip\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := echoHandler)
    (expect := (assertExact · r400))

  -- NUL and control chars in TE value
  check "NUL byte in TE value → 400"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunk\x00ed\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := (assertExact · r400))

  check "control char (0x01) in TE value → 400"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunk\x01ed\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := (assertExact · r400))

#eval runGroup "RFC 9112 §6.1: Transfer-Encoding accepted cases" do
  check "gzip, chunked accepted — chunked is last"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: gzip, chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := echoHandler)
    (expect := fun r => assertStatus r "HTTP/1.1 200" *> assertContains r "hello")

  check "br, chunked accepted"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: br, chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := echoHandler)
    (expect := fun r => assertStatus r "HTTP/1.1 200" *> assertContains r "hello")

  check "mixed-case Chunked accepted (codings are lowercased)"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: Chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := echoHandler)
    (expect := fun r => assertStatus r "HTTP/1.1 200" *> assertContains r "hello")

  check "TE trailing OWS accepted"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked \x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := echoHandler)
    (expect := fun r => assertStatus r "HTTP/1.1 200")

  check "gzip+chunked chain is visible to handler in TE header"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: gzip, chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := fun req => do
      let te := match req.line.headers.getAll? Header.Name.transferEncoding with
        | some vs => String.intercalate "|" (vs.map (·.value) |>.toList)
        | none => "<none>"
      Response.ok |>.text te)
    (expect := fun r => assertStatus r "HTTP/1.1 200" *> assertContains r "gzip, chunked")

-- RFC 9112 §6.3: Content-Length

#eval runGroup "RFC 9112 §6.3: Content-Length" do
  check "Content-Length with leading zeros accepted"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 005\x0d\nConnection: close\x0d\n\x0d\nhello")
    (handler := echoHandler)
    (expect := fun r => assertStatus r "HTTP/1.1 200" *> assertContains r "hello")

  check "very large Content-Length → 413"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 99999999999999999999\x0d\nConnection: close\x0d\n\x0d\nhello")
    (handler := echoHandler)
    (expect := fun r => assertStatus r "HTTP/1.1 413")

  check "duplicate Content-Length same value → 400"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello")
    (handler := echoHandler)
    (expect := (assertExact · r400))

  check "duplicate Content-Length different values → 400"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 3\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nabc")
    (handler := echoHandler)
    (expect := (assertExact · r400))

  check "non-numeric Content-Length → 400"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: abc\x0d\nConnection: close\x0d\n\x0d\nbody")
    (handler := okHandler)
    (expect := (assertExact · r400))

  check "negative Content-Length → 400"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: -1\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := (assertExact · r400))

  check "extra bytes beyond CL become next pipelined request"
    (raw :=
      "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\n\x0d\nhello" ++
      "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := fun req => do
      let body : String ← req.body.readAll
      Response.ok |>.text s!"{toString req.line.uri}:{body}")
    (expect := fun r =>
      assertResponseCount r 2 *>
      assertContains r "/:hello" *>
      assertContains r "/second:" *>
      assertAbsent r "/second:hello")

-- Chunk extension limits

#eval runGroup "Chunk extension name length (default limit = 256)" do
  check "ext name at 256 bytes → accepted"
    (raw :=
      let name := String.ofList (List.replicate 256 'a')
      s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;{name}\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := echoHandler)
    (expect := fun r => assertStatus r "HTTP/1.1 200")

  check "ext name at 257 bytes → 400"
    (raw :=
      let name := String.ofList (List.replicate 257 'a')
      s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;{name}\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := echoHandler)
    (expect := (assertExact · r400))

#eval runGroup "Chunk extension value length (default limit = 256)" do
  check "ext token value at 256 bytes → accepted"
    (raw :=
      let v := String.ofList (List.replicate 256 'v')
      s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;ext={v}\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := echoHandler)
    (expect := fun r => assertStatus r "HTTP/1.1 200")

  check "ext token value at 257 bytes → 400"
    (raw :=
      let v := String.ofList (List.replicate 257 'v')
      s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;ext={v}\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := echoHandler)
    (expect := (assertExact · r400))

  check "ext quoted value at 256 bytes → accepted"
    (raw :=
      let v := String.ofList (List.replicate 256 'v')
      s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;ext=\"{v}\"\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := echoHandler)
    (expect := fun r => assertStatus r "HTTP/1.1 200")

  check "ext quoted value at 257 bytes → 400"
    (raw :=
      let v := String.ofList (List.replicate 257 'v')
      s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;ext=\"{v}\"\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := echoHandler)
    (expect := (assertExact · r400))

#eval runGroup "Chunk extension count (default limit = 16)" do
  check "16 extensions → accepted"
    (raw :=
      let exts := (List.range 16).foldl (fun acc i => acc ++ s!";e{i}") ""
      s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5{exts}\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := echoHandler)
    (expect := fun r => assertStatus r "HTTP/1.1 200")

  check "17 extensions → 400"
    (raw :=
      let exts := (List.range 17).foldl (fun acc i => acc ++ s!";e{i}") ""
      s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5{exts}\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := echoHandler)
    (expect := (assertExact · r400))

#eval runGroup "Chunk extension count (custom limit)" do
  let cfg := { defaultConfig with maxChunkExtensions := 1 }

  check "1 extension with limit=1 → accepted"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;ext1\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := echoHandler)
    (config := cfg)
    (expect := fun r => assertStatus r "HTTP/1.1 200")

  check "2 extensions with limit=1 → 400"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;ext1;ext2\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := echoHandler)
    (config := cfg)
    (expect := (assertExact · r400))

  check "0 extensions with limit=1 → accepted"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := echoHandler)
    (config := cfg)
    (expect := fun r => assertStatus r "HTTP/1.1 200")

#eval runGroup "Chunk extension misc" do
  check "name-only extension (no value) → accepted"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;novalue\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := echoHandler)
    (expect := fun r => assertStatus r "HTTP/1.1 200" *> assertContains r "hello")

  check "extension on terminal zero-chunk → accepted"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0;final-ext=done\x0d\n\x0d\n")
    (handler := echoHandler)
    (expect := fun r => assertStatus r "HTTP/1.1 200")

  check "extension with quoted-string value → accepted"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;ext=\"hello world\"\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := echoHandler)
    (expect := fun r => assertStatus r "HTTP/1.1 200")

  check "non-token character in ext name → 400"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;bad@name\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := echoHandler)
    (expect := (assertExact · r400))

  check "multiple name=value extensions → accepted"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;a=1;b=2;c=3\x0d\nhello\x0d\n0\x0d\n\x0d\n")
    (handler := echoHandler)
    (expect := fun r => assertStatus r "HTTP/1.1 200")

-- RFC 9112 §7.1: zero-size chunk encoding

#eval runGroup "RFC 9112 §7.1: empty outgoing chunks must not be encoded as last-chunk" do
  -- A zero-size chunk IS the last-chunk terminator; the encoder must skip empty non-final chunks
  -- so that subsequent data remains visible to the client.
  check "empty chunk with extensions before real data — real data still received"
    (raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := fun _ => do
      let ext := (Chunk.ExtensionName.ofString! "test", some (Chunk.ExtensionValue.ofString! "val"))
      Response.ok |>.stream fun s => do
        s.send { data := .empty, extensions := #[ext] }
        s.send (Chunk.ofByteArray "after\n".toUTF8))
    (expect := fun r => assertStatus r "HTTP/1.1 200" *> assertContains r "after")

  check "multiple empty chunks before real data — real data still received"
    (raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := fun _ => do
      Response.ok |>.stream fun s => do
        s.send Chunk.empty
        s.send Chunk.empty
        s.send (Chunk.ofByteArray "data\n".toUTF8))
    (expect := fun r => assertContains r "data")

#eval runGroup "RFC 9110 §8.6: Content-Length strict decimal" do
  check "underscore in Content-Length → 400"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 1_0\x0d\nConnection: close\x0d\n\x0d\n0123456789")
    (handler := echoHandler)
    (expect := fun r => assertExact r r400)

  check "valid Content-Length → 200"
    (raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello")
    (handler := echoHandler)
    (expect := fun r => assertStatus r "HTTP/1.1 200")
