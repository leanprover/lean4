import Std.Http

open Std Http Protocol.H1

/-!
Benchmarks HTTP/1.1 request-line parsing (`parseRequestLineRawVersion`, as used by the server state
machine): method dispatch, request-target parsing and version parsing.

- `common`: the methods and targets of everyday traffic.
- `rare_methods`: methods that the method parser tries late.
- `proxy_form`: proxy-style absolute-form targets with authority, port and query, and a `CONNECT`
  authority-form target.
-/

def common : Array String := #[
  "GET / HTTP/1.1\r\n",
  "GET /index.html HTTP/1.1\r\n",
  "GET /articles/2026/10/http-benchmarks?utm_source=feed&utm_medium=rss HTTP/1.1\r\n",
  "POST /api/v1/users/12345/orders HTTP/1.1\r\n",
  "GET /static/css/main.3f9a1c.css HTTP/1.1\r\n",
  "PUT /api/v1/items/987?if-match=abc HTTP/1.1\r\n",
  "DELETE /api/v1/sessions/6f1e3c2a HTTP/1.1\r\n",
  "HEAD /health HTTP/1.0\r\n"
]

def rareMethods : Array String := #[
  "PATCH /api/v1/items/987 HTTP/1.1\r\n",
  "OPTIONS * HTTP/1.1\r\n",
  "PROPFIND /dav/calendars/user/ HTTP/1.1\r\n",
  "UNLOCK /dav/files/report.odt HTTP/1.1\r\n",
  "UPDATE /dav/files/report.odt HTTP/1.1\r\n",
  "VERSION-CONTROL /dav/files/report.odt HTTP/1.1\r\n"
]

def proxyForm : Array String := #[
  "GET http://www.example.com/ HTTP/1.1\r\n",
  "GET http://www.example.com:8080/articles/2026/10/http-benchmarks?utm_source=feed HTTP/1.1\r\n",
  "GET https://user@api.example.com/v1/items?page=2&per_page=50 HTTP/1.1\r\n",
  "CONNECT www.example.com:443 HTTP/1.1\r\n"
]

@[noinline]
def bench (config : Protocol.H1.Config) (lines : Array ByteArray) (iters : Nat) : IO Nat := do
  let mut ok := 0
  for _ in *...iters do
    for line in lines do
      if let .ok _ := (parseRequestLineRawVersion config).run line then
        ok := ok + 1
  return ok

def run (name : String) (iters : Nat) (lines : Array String) : IO Unit := do
  let lines := lines.map String.toUTF8
  let t1 ← IO.monoNanosNow
  let ok ← bench {} lines iters
  let t2 ← IO.monoNanosNow
  unless ok == iters * lines.size do
    throw <| .userError s!"{name}: expected {iters * lines.size} parsed lines, got {ok}"
  IO.println s!"measurement: {name} {(t2 - t1).toFloat / 1000000000.0} s"

def main (args : List String) : IO Unit := do
  let iters := args[0]!.toNat!
  run "common" iters common
  run "rare_methods" iters rareMethods
  run "proxy_form" iters proxyForm
