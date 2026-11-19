import Std.Http

open Std Http

/-!
Benchmarks the `Headers` multimap and the per-message decisions the HTTP/1.1 state machine derives
from it.

- `build`: inserting the ten typed headers of a browser request, as the parser does.
- `lookup`: the framing and connection lookups made for every message, mostly of absent keys.
- `normalize`: the erase-and-insert sequence the writer applies to every response head.
- `framing`: `Message.Head.getSize` and `Message.Head.shouldKeepAlive` on typical request heads.
-/

def browserHeaders : Array (String × String) := #[
  ("Host", "www.example.com"),
  ("User-Agent", "Mozilla/5.0 (X11; Linux aarch64; rv:131.0) Gecko/20100101 Firefox/131.0"),
  ("Accept", "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8"),
  ("Accept-Language", "en-US,en;q=0.5"),
  ("Accept-Encoding", "gzip, deflate, br, zstd"),
  ("Referer", "https://www.example.com/articles/2026/10/http-benchmarks"),
  ("Connection", "keep-alive"),
  ("Cookie", "session=6f1e3c2a9b8d4e7f; theme=dark; _ga=GA1.2.1234567890.1700000000"),
  ("Upgrade-Insecure-Requests", "1"),
  ("Sec-Fetch-Dest", "document")
]

def typed (pairs : Array (String × String)) : Array (Header.Name × Header.Value) :=
  pairs.map fun (name, value) => (Header.Name.ofString! name, Header.Value.ofString! value)

def ofPairs (pairs : Array (String × String)) : Headers :=
  (typed pairs).foldl (fun headers (name, value) => headers.insert name value) .empty

@[noinline]
def benchBuild (pairs : Array (Header.Name × Header.Value)) (iters : Nat) : IO Nat := do
  let mut total := 0
  for _ in *...iters do
    let headers := pairs.foldl (fun headers (name, value) => headers.insert name value) Headers.empty
    total := total + headers.size
  return total

@[noinline]
def benchLookup (all : Array Headers) (iters : Nat) : IO Nat := do
  let mut hits := 0
  for _ in *...iters do
    for headers in all do
      -- Using the values keeps their retrieval from being dropped as dead code.
      if let some values := headers.getAll? .contentLength then hits := hits + values.size
      if let some values := headers.getAll? .transferEncoding then hits := hits + values.size
      if let some values := headers.getAll? .connection then hits := hits + values.size
      if let some values := headers.getAll? .expect then hits := hits + values.size
      if headers.contains .server then hits := hits + 1
      if headers.contains .date then hits := hits + 1
      if let some host := headers.get? .host then hits := hits + host.value.utf8ByteSize
  return hits

@[noinline]
def benchNormalize (all : Array Headers) (iters : Nat) : IO Nat := do
  let mut total := 0
  for i in *...iters do
    for headers in all do
      let headers := headers
        |>.erase .connection
        |>.erase .contentLength
        |>.erase .transferEncoding
        |>.insert .contentLength (.ofString! (toString (i % 4096)))
        |>.insert .connection (.mk "close")
      total := total + headers.size
  return total

@[noinline]
def benchFraming (heads : Array Request.Head) (iters : Nat) : IO Nat := do
  let mut total := 0
  for _ in *...iters do
    for head in heads do
      if let some (.fixed n) := Protocol.H1.Message.Head.getSize (dir := .receiving) head true then
        total := total + n + 1
      if Protocol.H1.Message.Head.shouldKeepAlive (dir := .receiving) head then
        total := total + 1
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

  let browser := ofPairs browserHeaders
  let response := ofPairs #[
    ("Content-Type", "text/html; charset=utf-8"),
    ("Cache-Control", "private, max-age=0"),
    ("ETag", "\"5f3a9c2e-400\""),
    ("Connection", "keep-alive"),
    ("Content-Length", "1024")
  ]
  let post := ofPairs #[
    ("Host", "api.example.com"),
    ("Content-Type", "application/json"),
    ("Content-Length", "1024")
  ]
  let chunked := ofPairs #[
    ("Host", "api.example.com"),
    ("Transfer-Encoding", "chunked"),
    ("Connection", "close")
  ]
  let headers := #[browser, response, post, chunked]

  let heads : Array Request.Head := #[
    { method := .get, version := .v11, headers := browser },
    { method := .post, version := .v11, headers := post },
    { method := .post, version := .v11, headers := chunked },
    { method := .get, version := .v10, headers := ofPairs #[("Connection", "keep-alive")] }
  ]

  run "build" (benchBuild (typed browserHeaders) (10 * iters)) (· == 10 * iters * browserHeaders.size)
  -- Per pass: one value each for `connection` (browser); `content-length`, `connection` (response);
  -- `content-length` (post); `transfer-encoding`, `connection` (chunked); plus three 15-byte hosts.
  run "lookup" (benchLookup headers (10 * iters)) (· == 10 * iters * (6 + 3 * 15))
  -- Sizes after normalizing: 11 (browser), 5 (response), 4 (post), 3 (chunked).
  run "normalize" (benchNormalize headers iters) (· == iters * 23)
  -- Sizes `0 + 1`, `1024 + 1`, none, `0 + 1`; all keep alive except the `Connection: close` one.
  run "framing" (benchFraming heads iters) (· == iters * (1 + 1025 + 1 + 3))
