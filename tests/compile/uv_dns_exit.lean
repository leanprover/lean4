import Std.Internal.UV

/-!
Regression guard: a program that performs a DNS lookup must exit cleanly.

Since the libuv finalization work in #14202, a `getAddrInfo` whose lookup reaches the system
resolver makes the process abort during exit — after `main` has already produced correct output.
The abort is a libmalloc `POINTER_BEING_FREED_WAS_NOT_ALLOCATED` raised inside
`_pthread_tsd_cleanup`, i.e. delayed heap corruption surfacing in a thread-local destructor.

This lives in `tests/compile` rather than `tests/elab` on purpose: the failure only appears when a
compiled binary (or `--run`) exits, not when `#eval` runs during elaboration, which is why
`tests/elab/async_dns.lean` passes. The assertion is the process exit status, so a resolution
failure exercises the same path as a successful lookup and the test does not require network access.
-/

open Std.Internal.UV

def main : IO Unit := do
  let promise ← DNS.getAddrInfo "example.com" "80" 0
  match promise.result?.get with
  | some _ => IO.println "lookup completed"
  | none => IO.println "lookup dropped"
