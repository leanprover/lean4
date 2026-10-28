import Std.Http

open Std Async
open Std Http Internal Test

/-!
Benchmarks `Std.Http.Server.serve` under concurrent keep-alive load over loopback TCP (#13469).
Unlike `http_server_tcp.lean`, which pipelines every request down one connection, each client here
sends one request and waits for its response before sending the next, so every request pays the
connection loop's polling, timer, channel and task wake-up costs.

- `clients_<k>`: `k` lock-step clients share the same total number of requests.
-/

def request : ByteArray :=
  "GET /bench HTTP/1.1\r\nHost: example.com\r\n\r\n".toUTF8

/-- `okHandler` responses carry `Content-Length: 2`, so they end in the blank line and `ok`. -/
def responseEnd : ByteArray := "\r\n\r\nok".toUTF8

def endsWithResponse (buf : ByteArray) : Bool :=
  buf.size ≥ responseEnd.size &&
  (buf.extract (buf.size - responseEnd.size) buf.size).data == responseEnd.data

def client (addr : Net.SocketAddress) (requests : Nat) : Async Nat := do
  let socket ← TCP.Socket.Client.mk
  socket.connect addr
  socket.noDelay
  let mut responses := 0
  for _ in *...requests do
    socket.send request
    let mut buf := ByteArray.empty
    while !endsWithResponse buf do
      match ← socket.recv? 65536 with
      | none => throw <| .userError "server closed the connection"
      | some chunk => buf := buf ++ chunk
    responses := responses + 1
  socket.shutdown
  return responses

def run (clients total : Nat) : IO Unit := do
  let perClient := total / clients
  let (count, time) ← Async.block do
    let addr : Net.SocketAddress := .v4 ⟨.ofParts 127 0 0 1, 0⟩
    let server ← Server.serve addr okHandler { maxRequests := perClient + 1 }
    let some addr := server.localAddr
      | throw <| .userError "server has no local address"

    let t1 ← IO.monoNanosNow
    let mut tasks := #[]
    for _ in *...clients do
      tasks := tasks.push (← async (client addr perClient))
    let mut count := 0
    for task in tasks do
      count := count + (← await task)
    let t2 ← IO.monoNanosNow

    server.shutdownAndWait
    return (count, (t2 - t1).toFloat / 1000000000.0)

  unless count == clients * perClient do
    throw <| .userError s!"clients_{clients}: expected {clients * perClient} responses, got {count}"
  IO.println s!"measurement: clients_{clients} {time} s"

def main (args : List String) : IO Unit := do
  let total := args[0]!.toNat!
  for clients in [1, 4, 16, 64] do
    run clients total
