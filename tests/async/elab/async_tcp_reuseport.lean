import Std.Async
import Std.Net.Addr

/-!
Tests `TCP.Socket.Server.bindReusePort`: on Linux several servers share one address, while a plain
`bind` cannot join them; elsewhere the call either succeeds or fails with `unsupportedOperation`.
-/

open Std.Async
open Std.Net

def assertBEq [BEq α] [ToString α] (actual expected : α) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError <|
      s!"expected '{expected}', got '{actual}'"

def reusePortShared : IO Unit := do
  let addr := SocketAddressV4.mk (.ofParts 127 0 0 1) 8091

  let first ← TCP.Socket.Server.mk
  first.bindReusePort addr
  first.listen 128

  let second ← TCP.Socket.Server.mk
  second.bindReusePort addr
  second.listen 128

  assertBEq (← first.getSockName).port 8091
  assertBEq (← second.getSockName).port 8091

  let plain ← TCP.Socket.Server.mk
  let joined ← try plain.bind addr; pure true catch _ => pure false
  assertBEq joined false

  let client ← TCP.Socket.Client.mk
  (← (client.connect addr).toBaseIO).block
  assertBEq (← client.getPeerName).port 8091

def reusePortUnsupported : IO Unit := do
  let addr := SocketAddressV4.mk (.ofParts 127 0 0 1) 8092
  let server ← TCP.Socket.Server.mk
  try
    server.bindReusePort addr
  catch
    | .unsupportedOperation .. => pure ()
    | e => throw e

#eval if System.Platform.isLinux then reusePortShared else reusePortUnsupported
