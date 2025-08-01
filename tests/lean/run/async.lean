import Std.Internal.Async
import Std.Internal.UV
import Std.Net.Addr

open Std.Internal.IO.Async.UDP
open Std.Internal.IO.Async
open Std.Net

def t : IO (Async Nat) := do
  IO.println "a"
  return do
    IO.println "b"
    return 2

-- Usage example of the ForIn instance

def loop : Async Nat := do
  let mut res := 0

  while res < 10 do
    res := res + 1

  discard t

  pure res

/--
info: 10
-/
#guard_msgs in
#eval IO.println =<< ETask.block =<< loop.asTask

def loopExcept : Async Nat := do
  let mut res := 0

  while res < 10 do
    throw (.userError "some error")

  discard t

  pure res

/--
error: some error
-/
#guard_msgs in
#eval IO.println =<< ETask.block =<< loopExcept.asTask
