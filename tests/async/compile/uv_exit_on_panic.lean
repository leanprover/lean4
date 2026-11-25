import Std.Internal.UV

open Std.Internal.UV

@[extern "lean_internal_set_exit_on_panic"]
opaque setExitOnPanic (exit : Bool) : BaseIO Unit

/-!
A panic that ends the program must not wait for queued thread-pool requests (here `uv_random`),
which libuv's exit destructor would run one by one before joining its workers (#16701). The child
runs with one pool thread, queues `n` requests of 4 MiB, and then either panics under exit-on-panic
(`panic`) or hits an internal panic (`internal`, an array capacity that overflows); with 64 requests
it must exit with code 1 about as fast as with one.
-/

def child (n : Nat) (mode : String) : IO Unit := do
  let mut held := #[]
  for _ in [0:n] do
    held := held.push (← System.random (4 * 1024 * 1024))
  if mode == "panic" then
    setExitOnPanic true
    let x : Nat := panic! "boom"
    IO.println s!"not exited after panic {x}"
  else
    let a : Array Nat := Array.mkEmpty (2 ^ 61)
    IO.println s!"not exited after internal panic {a.size}"
  -- Keeps the requests' promises alive until the exit.
  IO.println s!"{held.size} requests"

def run (n : Nat) (mode : String) : IO Nat := do
  let start ← IO.monoMsNow
  let out ← IO.Process.output {
    cmd := (← IO.appPath).toString
    args := #["child", toString n, mode]
    env := #[("UV_THREADPOOL_SIZE", some "1")] }
  if out.exitCode != 1 || !out.stdout.isEmpty then
    throw <| .userError s!"{mode} child with {n} requests exited with {out.exitCode}: {out.stdout}"
  return (← IO.monoMsNow) - start

def main (args : List String) : IO Unit := do
  if let ["child", n, mode] := args then
    return (← child n.toNat! mode)
  for mode in ["panic", "internal"] do
    -- The fastest of three runs, so that one slow start does not decide.
    let mut few := 1000000
    let mut many := 1000000
    for _ in [0:3] do
      few := min few (← run 1 mode)
      many := min many (← run 64 mode)
    if many > few + 400 then
      IO.println s!"{mode} waited for the queued requests: {many} ms against {few} ms"
      return
  IO.println "ok"
