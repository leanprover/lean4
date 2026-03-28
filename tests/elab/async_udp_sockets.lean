import Std.Internal.Async
import Std.Internal.UV
import Std.Net.Addr

open Std.Internal.IO.Async.UDP
open Std.Internal.IO.Async
open Std.Net

def assertBEq [BEq α] [ToString α] (actual expected : α) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError <|
      s!"expected '{expected}', got '{actual}'"

/-- Joe is another client. -/
def runJoe (addr : UInt16 → SocketAddress) (first second : UInt16) : Async Unit := do
  let client ← UDP.Socket.mk

  client.bind (addr second)
  client.connect (addr first)

  client.send (String.toUTF8 "hello robert!")


def acceptClose (addr : UInt16 → SocketAddress) (first second : UInt16) : IO Unit := do

  let server ← UDP.Socket.mk
  server.bind (addr first)

  let res ← (runJoe addr first second).toIO
  res.block

  let res ← server.recv 1024 |>.toBaseIO
  let (msg, addr) ← res.block

  if let some addr := addr then
    assertBEq addr.port second

  assertBEq (String.fromUTF8! msg) "hello robert!"

#eval acceptClose (SocketAddress.v4 ∘ SocketAddressV4.mk (.ofParts 127 0 0 1))  9001 9002

#eval acceptClose (SocketAddress.v6 ∘ SocketAddressV6.mk (.ofParts 0 0 0 0 0 0 0 1))  9003 9004
