import Std.Http

open Std Http Protocol.H1
open Std.Internal.Parsec

/-!
Benchmarks HTTP/1.1 header-section parsing (`parseSingleHeader`, as used by the server and client
state machines) up to the blank line, without typing the parsed names and values (see
`http_header_ofstring.lean` for that step).

- `browser_request`: the ten headers of a typical browser page request.
- `api_response`: the headers of a typical API server response.
- `padded`: short headers with optional whitespace around their values.
-/

def browserRequest : String :=
  "Host: www.example.com\r\n" ++
  "User-Agent: Mozilla/5.0 (X11; Linux aarch64; rv:131.0) Gecko/20100101 Firefox/131.0\r\n" ++
  "Accept: text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8\r\n" ++
  "Accept-Language: en-US,en;q=0.5\r\n" ++
  "Accept-Encoding: gzip, deflate, br, zstd\r\n" ++
  "Referer: https://www.example.com/articles/2026/10/http-benchmarks\r\n" ++
  "Connection: keep-alive\r\n" ++
  "Cookie: session=6f1e3c2a9b8d4e7f; theme=dark; _ga=GA1.2.1234567890.1700000000\r\n" ++
  "Upgrade-Insecure-Requests: 1\r\n" ++
  "Sec-Fetch-Dest: document\r\n\r\n"

def apiResponse : String :=
  "Date: Tue, 27 Oct 2026 12:00:00 GMT\r\n" ++
  "Server: nginx/1.27.2\r\n" ++
  "Content-Type: application/json; charset=utf-8\r\n" ++
  "Content-Length: 1024\r\n" ++
  "Cache-Control: private, max-age=0, must-revalidate\r\n" ++
  "ETag: \"5f3a9c2e-400\"\r\n" ++
  "Vary: Accept-Encoding, Origin\r\n" ++
  "Set-Cookie: session=6f1e3c2a9b8d4e7f; Path=/; HttpOnly; Secure; SameSite=Lax\r\n" ++
  "Strict-Transport-Security: max-age=63072000; includeSubDomains\r\n" ++
  "X-Request-Id: 0c6f1b52-8d3e-4b7a-9f21-3c4d5e6f7a8b\r\n\r\n"

def padded : String :=
  "A:1\r\nB: 2\r\nC:\t3 \r\nD:   4\t\r\nE: five six\r\nF:\r\nG: 7\r\nH:  8  \r\n\r\n"

/-- Parses header lines up to the blank line and returns how many were parsed. -/
partial def parseSection (config : Protocol.H1.Config) (it : ByteArray.Iterator) (count : Nat) : Option Nat :=
  match parseSingleHeader config it with
  | .success it (some _) => parseSection config it (count + 1)
  | .success _ none => some count
  | .error _ _ => none

@[noinline]
def bench (config : Protocol.H1.Config) (block : ByteArray) (iters : Nat) : IO Nat := do
  let mut headers := 0
  for _ in *...iters do
    if let some count := parseSection config block.iter 0 then
      headers := headers + count
  return headers

def run (name : String) (iters : Nat) (block : String) (expected : Nat) : IO Unit := do
  let t1 ← IO.monoNanosNow
  let headers ← bench {} block.toUTF8 iters
  let t2 ← IO.monoNanosNow
  unless headers == iters * expected do
    throw <| .userError s!"{name}: expected {iters * expected} parsed headers, got {headers}"
  IO.println s!"measurement: {name} {(t2 - t1).toFloat / 1000000000.0} s"

def main (args : List String) : IO Unit := do
  let iters := args[0]!.toNat!
  run "browser_request" iters browserRequest 10
  run "api_response" iters apiResponse 10
  run "padded" iters padded 8
