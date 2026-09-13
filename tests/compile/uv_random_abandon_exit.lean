import Std.Internal.UV

/-!
Unawaited `System.random` requests large enough to still be running in threadpool workers when
`finalize_libuv` gives up on its 100 ms drain, so teardown abandons them while the workers are still
writing: the `ByteArray` each one writes into has to stay alive with the abandoned request, and the
loop has to be left unclosed. On hardware fast enough to finish them inside the drain, this
exercises the ordinary completion path instead.
-/

open Std.Internal.UV

def main : IO Unit := do
  for _ in [0:4] do
    discard <| System.random (64 * 1024 * 1024)
  IO.println "exiting"
