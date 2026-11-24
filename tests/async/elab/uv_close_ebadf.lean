import Std.Async

open Std Async Internal.UV Net

/-!
Closing a TCP socket fails its pending operations with `EBADF`, like every later operation on it,
and not with the canceled error, which is reserved for operations cut short because the program is
finishing. The read, the accept and the shutdown are failed by `close` itself; the write, which
waits on a peer that does not read, by libuv's callback. On Windows the OS may take the whole write
and complete it, and the shutdown with it, before the `close`; they may then succeed there.
-/

def await (p : IO.Promise (Except IO.Error α)) : IO (Except IO.Error α) := do
  return (← IO.wait p.result?).getD (.error (.userError "dropped"))

def report (what : String) (r : Except IO.Error α) : IO Unit := do
  let outcome := match r with
    | .ok _ => "succeeded"
    | .error (.invalidArgument ..) => "invalid argument"
    | .error e => if e.isCanceled then "canceled" else toString e
  IO.println s!"{what}: {outcome}"

/-- For an operation that may complete before the `close` on Windows: `EBADF`, or success there. -/
def reportRacingClose (what : String) (r : Except IO.Error α) : IO Unit :=
  match r with
  | .error (.invalidArgument ..) => IO.println s!"{what}: succeeded or invalid argument"
  | .ok _ => if System.Platform.isWindows then IO.println s!"{what}: succeeded or invalid argument"
    else report what r
  | _ => report what r

def listener : IO TCP.Socket := do
  let server ← TCP.Socket.new
  server.bind <| SocketAddressV4.mk (.ofParts 127 0 0 1) 0
  server.listen 1
  return server

/--
info: recv: invalid argument
send: succeeded or invalid argument
shutdown: succeeded or invalid argument
accept: invalid argument
-/
#guard_msgs in
#eval show IO Unit from do
  let server ← listener
  let accepted ← server.accept
  let client ← TCP.Socket.new
  discard <| AsyncTask.ofPromise (← client.connect (← server.getSockName)) |>.block
  let peer ← AsyncTask.ofPromise accepted |>.block
  let recv ← client.recv? 1024
  -- The peer never reads, so most of this stays in flight, and the shutdown waits behind it.
  let send ← client.send #[ByteArray.mk (Array.replicate (64 * 1024 * 1024) 0)]
  let shutdown ← client.shutdown
  client.close
  report "recv" (← await recv)
  reportRacingClose "send" (← await send)
  reportRacingClose "shutdown" (← await shutdown)
  peer.close

  let idle ← listener
  let accept ← idle.accept
  idle.close
  report "accept" ((← await accept).map fun _ => ())
  server.close
