import Std.Http

open Std Async
open Std Http

/-!
Benchmarks building a `Body.Full` text response and draining it, as the connection loop does for
`Response.ok |>.text`.
-/

@[noinline]
def benchFullResponse (n : Nat) : IO Nat := Async.block do
  let mut total := 0
  for i in *...n do
    let response ← Response.ok |>.text s!"hello, world {i % 10}"
    if let some (.fixed size) ← Body.getKnownSize response.body then
      total := total + size
    while true do
      match ← response.body.recv with
      | some chunk => total := total + chunk.data.size
      | none => break
  return total

def main (args : List String) : IO Unit := do
  let n := args[0]!.toNat!
  let t1 ← IO.monoNanosNow
  let total ← benchFullResponse n
  let t2 ← IO.monoNanosNow
  unless total == 2 * n * 14 do
    throw <| .userError s!"full_response: expected {2 * n * 14} bytes, got {total}"
  IO.println s!"measurement: full_response {(t2 - t1).toFloat / 1000000000.0} s"
