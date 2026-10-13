import Std.Async

/-!
Socket arguments that the operating system does not accept are rejected rather than silently wrapped
or left pending: out-of-range keep-alive delays are rejected, a receive with a buffer size of 0 fails
as an invalid argument, and accepting on a socket that is bound but not listening fails.
-/

open Std Async Net

def lo : SocketAddress := .v4 ⟨.ofParts 127 0 0 1, 0⟩

def expectFailure (what : String) (x : IO Unit) : IO Unit := do
  if (← x.toBaseIO) matches .ok _ then
    throw <| IO.userError s!"{what} succeeded"

def expectInvalidArgument (what : String) (x : Async Unit) : IO Unit := do
  match ← x.block.toBaseIO with
  | .error (.invalidArgument ..) => pure ()
  | .error e => throw <| IO.userError s!"{what}: unexpected error {e}"
  | .ok _ => throw <| IO.userError s!"{what}: succeeded"

#eval show IO Unit from do
  let server ← TCP.Socket.Server.mk
  server.bind lo
  -- 2^32 + 1 s, which wraps to 1 s.
  expectFailure "server keep-alive delay of 2^32 + 1 s" <|
    server.keepAlive true ⟨2 ^ 32 + 1⟩ (by decide)
  let client ← TCP.Socket.Client.mk
  client.bind lo
  expectFailure "client keep-alive delay of 2^32 + 1 s" <|
    client.keepAlive true ⟨2 ^ 32 + 1⟩

-- Separate sockets: on a socket with a pending `accept`, `tryAccept` fails for another reason.
#eval show IO Unit from do
  let socket ← Internal.UV.TCP.Socket.new
  socket.bind lo
  expectFailure "accept on a socket that is not listening" (discard socket.accept)

#eval show IO Unit from do
  let socket ← Internal.UV.TCP.Socket.new
  socket.bind lo
  expectFailure "tryAccept on a socket that is not listening" (discard socket.tryAccept)

#eval expectInvalidArgument "TCP recv? 0" do
  let server ← TCP.Socket.Server.mk
  server.bind lo
  server.listen 16
  let client ← TCP.Socket.Client.mk
  client.connect (← server.getSockName)
  let peer ← server.accept
  peer.send "hello".toUTF8
  discard <| client.recv? 0

#eval expectInvalidArgument "UDP recv 0" do
  let socket ← UDP.Socket.mk
  socket.bind lo
  let sender ← UDP.Socket.mk
  sender.send "hello".toUTF8 (some (← socket.getSockName))
  discard <| socket.recv 0
