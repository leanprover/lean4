import Std.Http

open Std Http

/-!
Benchmarks the validating constructors that type every header and request target the HTTP/1.1
server parses (#15887):

- `name_of_string`: `Header.Name.ofString?` on the names of a typical browser page request.
- `value_of_string`: `Header.Value.ofString?` on the values of the same request.
- `request_target_parse`: `RequestTarget.parse?` on typical origin-form targets.
-/

/-- The ten headers of a typical browser page request. -/
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

def targets : Array String := #[
  "/",
  "/index.html",
  "/articles/2026/10/http-benchmarks?utm_source=feed&utm_medium=rss",
  "/api/v1/users/12345/orders?page=2&per_page=50&sort=-created_at",
  "/static/css/main.3f9a1c.css",
  "/search?q=lean+theorem+prover&lang=en",
  "/files/a%20b/c%2Fd.txt?x=%41%42"
]

@[noinline]
def benchNames (iters : Nat) : IO Nat := do
  let mut ok := 0
  for _ in *...iters do
    for (name, _) in browserHeaders do
      if (Header.Name.ofString? name).isSome then ok := ok + 1
  return ok

@[noinline]
def benchValues (iters : Nat) : IO Nat := do
  let mut ok := 0
  for _ in *...iters do
    for (_, value) in browserHeaders do
      if (Header.Value.ofString? value).isSome then ok := ok + 1
  return ok

@[noinline]
def benchTargets (iters : Nat) : IO Nat := do
  let mut ok := 0
  for _ in *...iters do
    for target in targets do
      if (RequestTarget.parse? target).isSome then ok := ok + 1
  return ok

def run (name : String) (expected : Nat) (act : IO Nat) : IO Unit := do
  let t1 ← IO.monoNanosNow
  let ok ← act
  let t2 ← IO.monoNanosNow
  unless ok == expected do
    throw <| .userError s!"{name}: expected {expected} successful parses, got {ok}"
  IO.println s!"measurement: {name} {(t2 - t1).toFloat / 1000000000.0} s"

def main (args : List String) : IO Unit := do
  let iters := args[0]!.toNat!
  run "name_of_string" (iters * browserHeaders.size) (benchNames iters)
  run "value_of_string" (iters * browserHeaders.size) (benchValues iters)
  run "request_target_parse" (iters * targets.size) (benchTargets iters)
