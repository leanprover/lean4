import Std.Async

/-!
A `TCP.Socket.Server.acceptSelector` that loses a `Selectable.one` must not drop a connection it
already accepted: every client that connects is eventually returned by some select.

The selector races a 1 ms sleep while clients keep connecting, so whether a round hits the window
between the accept and the lost race is timing-dependent; the test cannot fail when the fix is in
place, but may pass without it.
-/

open Std Async Net

def lo : SocketAddress := .v4 ⟨.ofParts 127 0 0 1, 0⟩

def clients : Nat := 200

#eval show IO Unit from do
  let accepted ← (do
    let server ← TCP.Socket.Server.mk
    server.bind lo
    server.listen 256
    let addr ← server.getSockName
    let connector ← (do
      let mut sockets := #[]
      for _ in [0:clients] do
        let c ← TCP.Socket.Client.mk
        c.connect addr
        sockets := sockets.push c
      return sockets : Async (Array TCP.Socket.Client)).asTask
    let mut accepted := #[]
    let mut idle := 0
    -- Gives up after 2 s without an accept once the clients are connected.
    while accepted.size < clients && idle < 2000 do
      match ← Selectable.one #[
          .case server.acceptSelector (fun c => pure (some c)),
          .case (← Selector.sleep 1) (fun _ => pure none)] with
      | some c =>
        accepted := accepted.push c
        idle := 0
      | none =>
        if ← IO.hasFinished connector then
          idle := idle + 1
    discard <| await connector
    return accepted.size : Async Nat).block
  unless accepted == clients do
    throw <| IO.userError s!"only {accepted} of {clients} connections were returned"
