import Std.Async

open Std Async Internal.UV Net

/-!
Closing a TCP socket fails its pending operations with `EBADF`, like every later operation on it,
and not with the canceled error, which is reserved for operations cut short because the program is
finishing. The read and the accept are failed by `close` itself; the write and the shutdown, which
wait on a peer that does not read, by libuv's callbacks. On Windows the OS may take the whole write
and complete it, and the shutdown with it, before the `close`; they must then succeed, and never
fail with the canceled error.
-/

def await (p : IO.Promise (Except IO.Error α)) : IO (Except IO.Error α) := do
  return (← IO.wait p.result?).getD (.error (.userError "dropped"))

def report (what : String) (r : Except IO.Error α) : IO Unit := do
  let outcome := match r with
    | .ok _ => "succeeded"
    | .error e@(.invalidArgument ..) => if e.isCanceled then "canceled" else "invalid argument"
    | .error e => if e.isCanceled then "canceled" else toString e
  IO.println s!"{what}: {outcome}"

/-- For an operation that may complete before the `close`: success or `EBADF`, never canceled. -/
def reportRacingClose (what : String) (r : Except IO.Error α) : IO Unit :=
  match r with
  | .ok _ | .error (.invalidArgument ..) => IO.println s!"{what}: succeeded or invalid argument"
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
