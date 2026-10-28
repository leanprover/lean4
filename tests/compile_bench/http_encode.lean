import Std.Http

open Std Http Internal Time

/-!
Benchmarks the HTTP/1.1 serializers that run for every message written to the wire.

- `response_head`: status lines of common statuses plus typical response headers.
- `request_head`: request lines with origin-form targets plus typical client headers.
- `chunk`: chunked transfer-encoding frames, with and without extensions.
- `date_header`: formatting the `Date` header value the server adds to every response.
-/

def responseHeaders : Headers :=
  Headers.empty
    |>.insert .contentType (.mk "application/json; charset=utf-8")
    |>.insert .contentLength (.mk "1024")
    |>.insert .server (.mk "LeanHTTP/1.1")
    |>.insert .date (.mk "Tue, 27 Oct 2026 12:00:00 GMT")
    |>.insert (.mk "cache-control") (.mk "private, max-age=0, must-revalidate")
    |>.insert (.mk "etag") (.mk "\"5f3a9c2e-400\"")
    |>.insert (.mk "vary") (.mk "Accept-Encoding, Origin")
    |>.insert .setCookie (.mk "session=6f1e3c2a9b8d4e7f; Path=/; HttpOnly; Secure; SameSite=Lax")

def statuses : Array Status :=
  #[.ok, .created, .noContent, .movedPermanently, .notModified, .notFound, .tooManyRequests,
    .internalServerError]

def requestHeaders : Headers :=
  Headers.empty
    |>.insert .host (.mk "api.example.com")
    |>.insert .userAgent (.mk "lean-bench/1.0")
    |>.insert .accept (.mk "application/json")
    |>.insert (.mk "accept-encoding") (.mk "gzip, deflate, br")
    |>.insert .authorization (.mk "Bearer eyJhbGciOiJIUzI1NiJ9.eyJzdWIiOiIxMjM0NSJ9.c2lnbmF0dXJl")
    |>.insert .contentLength (.mk "0")

/-- The server sends the encoded pieces without joining them, so neither does the checksum. -/
def checksum (buffer : ChunkedBuffer) : Nat :=
  buffer.size + buffer.data.size

@[noinline]
def benchResponseHead (start : ChunkedBuffer) (version : Version) (statuses : Array Status)
    (headers : Headers) (iters : Nat) : IO Nat := do
  let mut total := 0
  for _ in *...iters do
    for status in statuses do
      let head : Response.Head := { status, version, headers }
      total := total + checksum (Encode.encode (v := .v11) start head)
  return total

@[noinline]
def benchRequestHead (start : ChunkedBuffer) (method : Method) (version : Version)
    (targets : Array RequestTarget) (headers : Headers) (iters : Nat) : IO Nat := do
  let mut total := 0
  for _ in *...iters do
    for uri in targets do
      let head : Request.Head := { method, version, uri, headers }
      total := total + checksum (Encode.encode (v := .v11) start head)
  return total

@[noinline]
def benchChunk (chunks : Array Chunk) (iters : Nat) : IO Nat := do
  let mut total := 0
  for _ in *...iters do
    total := total + checksum (chunks.foldl (Encode.encode (v := .v11)) ChunkedBuffer.empty)
  return total

@[noinline]
def benchDate (iters : Nat) : IO Nat := do
  let mut total := 0
  for i in *...iters do
    let timestamp := Timestamp.ofSecondsSinceUnixEpoch (.ofNat (1798372800 + i * 7919))
    total := total + (DateTime.ofTimestamp timestamp TimeZone.ZoneRules.UTC).toHTTPDateString.length
  return total

def run (name : String) (act : IO Nat) (check : Nat → Bool) : IO Unit := do
  let t1 ← IO.monoNanosNow
  let result ← act
  let t2 ← IO.monoNanosNow
  unless check result do
    throw <| .userError s!"{name}: unexpected result {result}"
  IO.println s!"measurement: {name} {(t2 - t1).toFloat / 1000000000.0} s"

def main (args : List String) : IO Unit := do
  let iters := args[0]!.toNat!

  let targets := #[
    "/", "/api/v1/items?page=2&per_page=50", "/search?q=lean+theorem+prover&lang=en",
    "/files/a%20b/c%2Fd.txt"
  ].map RequestTarget.parse!

  let small : Chunk := { data := "data: {\"tick\":42}\n\n".toUTF8 }
  let large : Chunk := { data := ByteArray.mk (Array.replicate 4096 'x'.toUInt8) }
  let withExt : Chunk := {
    data := "hello".toUTF8
    extensions := #[(.ofString! "sig", some (.ofString! "abc123")), (.ofString! "last", none)]
  }
  let chunks := #[small, large, small, withExt, small, large, small, small]

  -- Every iteration encodes the same values, so one untimed iteration gives the expected total.
  -- The start buffer, version and method are arguments so that encoding them is not precomputed.
  let encodeResponses := benchResponseHead .empty .v11 statuses responseHeaders
  let response ← encodeResponses 1
  run "response_head" (encodeResponses iters) (· == iters * response)
  let encodeRequests := benchRequestHead .empty .get .v11 targets requestHeaders
  let request ← encodeRequests 1
  run "request_head" (encodeRequests iters) (· == iters * request)
  let chunk ← benchChunk chunks 1
  run "chunk" (benchChunk chunks (4 * iters)) (· == 4 * iters * chunk)
  -- `toHTTPDateString` is fixed-width: `Tue, 27 Oct 2026 12:00:00 GMT`.
  run "date_header" (benchDate iters) (· == iters * 29)
