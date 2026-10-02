import Std.Async
import Std.Internal.UV
import Std.Net.Addr

/-!
Tests that receiving a datagram larger than the supplied buffer reports an error instead of
silently handing back the truncated prefix. libuv flags the discarded remainder with
`UV_UDP_PARTIAL`, which used to be ignored.
-/

open Std.Async.UDP
open Std.Async
open Std.Net

def truncatedDatagram (mkAddr : UInt16 → SocketAddress) (serverPort clientPort : UInt16) :
    IO Unit := do
  let server ← UDP.Socket.mk
  server.bind (mkAddr serverPort)

  let client ← UDP.Socket.mk
  client.bind (mkAddr clientPort)
  client.connect (mkAddr serverPort)

  let sent ← (client.send (ByteArray.mk (Array.replicate 4096 (0 : UInt8)))).toIO
  sent.block

  let received ← (server.recv 128).toIO

  match ← received.block.toBaseIO with
  | .ok (bytes, _) =>
    throw <| IO.userError s!"expected a truncated datagram to fail, got {bytes.size} bytes"
  | .error e =>
    let msg := toString e
    unless (msg.splitOn "message too long").length == 2 do
      throw <| IO.userError s!"expected a message-size error, got '{msg}'"

#eval truncatedDatagram (SocketAddress.v4 ∘ SocketAddressV4.mk (.ofParts 127 0 0 1)) 9101 9102

#eval truncatedDatagram (SocketAddress.v6 ∘ SocketAddressV6.mk (.ofParts 0 0 0 0 0 0 0 1)) 9103 9104
