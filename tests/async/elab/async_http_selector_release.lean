import Std.Http
import Std.Http.Test.Helpers

open Std Async Http Internal Test

/-!
Tests that the selectors an HTTP server polls let go of a waiter once another selector wins
`Selectable.one`, so polling a source that never fires, such as `Server.waitShutdownSelector`, in a
loop does not keep one waiter, and the result of its round, alive per poll.
-/

/-- Wins from a pool task, so the other selectors of the round have registered by then. -/
def readyAfterRegister : Selector Unit where
  tryFn := pure none
  registerFn w := discard <| BaseIO.asTask (w.race (pure ()) (·.resolve (.ok ())))
  unregisterFn := pure ()

/--
Hands `sel` a waiter whose promise only `sel` holds, and records the task of that promise, which
finishes once `sel` drops the waiter.
-/
def tracked (sel : Selector α) (held : IO.Ref (Array (Task (Option (Except IO.Error α))))) :
    Selector α where
  tryFn := sel.tryFn
  registerFn w := do
    let p ← IO.Promise.new
    held.modify (·.push p.result?)
    BaseIO.chainTask (sync := true) p.result? fun
      | some r => w.promise.resolve r
      | none => pure ()
    sel.registerFn (w.withPromise p)
  unregisterFn := sel.unregisterFn

/-- How many of `tasks` have not finished. -/
def countPending (tasks : Array (Task α)) : BaseIO Nat :=
  tasks.foldlM (fun n t => return if ← IO.hasFinished t then n else n + 1) 0

/-- Polls `sel` against `readyAfterRegister` and fails if a waiter of a lost round stays held. -/
def releasesWaiters (name : String) (sel : Async (Selector α)) (rounds : Nat := 20) :
    Async Unit := do
  let held ← IO.mkRef #[]
  for _ in [0:rounds] do
    Selectable.one #[
      .case (tracked (← sel) held) (fun _ => pure ()),
      .case readyAfterRegister pure]
  let tasks ← held.get
  if tasks.isEmpty then
    throw <| IO.userError s!"{name}: never registered"
  -- A selector may drop its waiter from a pool task, so allow it some time.
  let mut waited := 0
  while waited < 3000 && (← countPending tasks) > 0 do
    IO.sleep 10
    waited := waited + 10
  let pending ← countPending tasks
  unless pending == 0 do
    throw <| IO.userError s!"{name}: {pending} of {tasks.size} lost waiters are still held"

#eval Async.block do
  let addr := Net.SocketAddressV4.mk (.ofParts 127 0 0 1) 0
  let server ← Server.serve addr okHandler defaultConfig
  releasesWaiters "waitShutdownSelector" (pure server.waitShutdownSelector)
  server.shutdownAndWait

#eval Async.block do
  let ctx ← CancellationContext.new
  let child ← ctx.fork
  releasesWaiters "doneSelector" (pure child.doneSelector)
  ctx.cancel .cancel

#eval Async.block do
  let ch : Std.Channel Unit ← Std.Channel.new
  releasesWaiters "Channel.recvSelector" (pure ch.recvSelector)

#eval Async.block do
  let stream ← Body.mkStream
  releasesWaiters "Body.Stream.recvSelector" (pure stream.recvSelector)
  releasesWaiters "Body.Stream.interestSelector" (pure stream.interestSelector)
  stream.close

#eval Async.block do
  releasesWaiters "Selector.sleep" (Selector.sleep 3600000)

#eval Async.block do
  let server ← TCP.Socket.Server.mk
  server.bind (Net.SocketAddressV4.mk (.ofParts 127 0 0 1) 0)
  server.listen 1
  let client ← TCP.Socket.Client.mk
  let accepted ← async server.accept
  client.connect (← server.getSockName)
  let conn ← await accepted
  releasesWaiters "recvSelector" (pure (conn.recvSelector 4096))
  client.close
  conn.close
  server.close
