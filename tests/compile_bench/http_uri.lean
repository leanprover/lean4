import Std.Http

open Std Http

/-!
Benchmarks the URI operations that handlers and clients run per request.

- `absolute_parse`: `URI.parse?` on absolute URIs with userinfo, ports, IP hosts, queries and fragments.
- `query_get`: decoded query parameter lookups (`URI.Query.get`), including absent keys.
- `path_decode`: percent-decoding of path segments (`URI.Path.toDecodedSegments`).
- `query_build`: building a query from unencoded strings and rendering it (`URI.Query.insert`).
- `target_to_string`: rendering request targets back to text, as when encoding a request head.
-/

def absoluteUris : Array String := #[
  "http://www.example.com/",
  "https://www.example.com/articles/2026/10/http-benchmarks?utm_source=feed&utm_medium=rss#comments",
  "http://user:secret@api.example.com:8080/v1/items?page=2&per_page=50",
  "https://192.168.1.20:8443/admin/login?next=%2Fdashboard",
  "http://[2001:db8::1]:8080/status",
  "https://cdn.example.com/static/css/main.3f9a1c.css"
]

def targets : Array String := #[
  "/search?q=lean+theorem+prover&lang=en&page=3",
  "/api/v1/users/12345/orders?page=2&per_page=50&sort=-created_at&filter%5Bstatus%5D=shipped",
  "/files/a%20b/c%2Fd/%E2%9C%93.txt?download=1&name=r%C3%A9sum%C3%A9.pdf",
  "/articles/2026/10/http-benchmarks?utm_source=feed&utm_medium=rss&utm_campaign=launch"
]

def keys : Array String := #["page", "q", "name", "utm_campaign", "missing"]

@[noinline]
def benchAbsolute (uris : Array String) (iters : Nat) : IO Nat := do
  let mut ok := 0
  for _ in *...iters do
    for uri in uris do
      if (URI.parse? uri).isSome then ok := ok + 1
  return ok

@[noinline]
def benchQueryGet (parsed : Array RequestTarget) (keys : Array String) (iters : Nat) : IO Nat := do
  let mut found := 0
  for _ in *...iters do
    for target in parsed do
      let query := target.query
      for key in keys do
        if let some value := query.get key then
          found := found + value.length
  return found

@[noinline]
def benchPathDecode (parsed : Array RequestTarget) (iters : Nat) : IO Nat := do
  let mut total := 0
  for _ in *...iters do
    for target in parsed do
      for segment in target.path.toDecodedSegments do
        total := total + segment.length
  return total

/-- Parameters to percent-encode, plus a `page` parameter that changes every iteration. -/
def params : Array (String × String) := #[
  ("q", "lean theorem prover"),
  ("lang", "en"),
  ("redirect", "/dashboard?tab=settings&view=all"),
  ("name", "résumé.pdf")
]

@[noinline]
def benchQueryBuild (params : Array (String × String)) (iters : Nat) : IO Nat := do
  let mut total := 0
  for i in *...iters do
    let query := params.foldl (fun query (key, value) => query.insert key value) URI.Query.empty
    total := total + (toString (query.insert "page" (toString (i % 100)))).length
  return total

@[noinline]
def benchToString (parsed : Array RequestTarget) (iters : Nat) : IO Nat := do
  let mut total := 0
  for _ in *...iters do
    for target in parsed do
      total := total + (toString target).length
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
  let parsed := targets.filterMap RequestTarget.parse?
  unless parsed.size == targets.size do
    throw <| .userError "failed to parse the request targets"

  run "absolute_parse" (benchAbsolute absoluteUris iters) (· == iters * absoluteUris.size)
  -- Decoded lengths of `page=3`, `q=lean+theorem+prover`, `page=2`, `name=résumé.pdf` and
  -- `utm_campaign=launch`; `missing` is absent everywhere.
  run "query_get" (benchQueryGet parsed keys (4 * iters)) (· == 4 * iters * (1 + 19 + 1 + 10 + 6))
  -- Every iteration decodes and renders the same targets, so one untimed iteration gives the total.
  let decoded ← benchPathDecode parsed 1
  run "path_decode" (benchPathDecode parsed (4 * iters)) (· == 4 * iters * decoded)
  let built ← benchQueryBuild params 1
  run "query_build" (benchQueryBuild params (4 * iters)) (· ≥ 4 * iters * built)
  let rendered ← benchToString parsed 1
  run "target_to_string" (benchToString parsed (4 * iters)) (· == 4 * iters * rendered)
