import Std.Internal.UV

/-!
Regression guard: a program that performs a DNS lookup must exit cleanly.
-/

open Std.Internal.UV

def main : IO Unit := do
  let promise ← DNS.getAddrInfo "example.com" "80" 0
  match promise.result?.get with
  | some _ => IO.println "lookup completed"
  | none => IO.println "lookup dropped"
