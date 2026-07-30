import Std.Internal.UV

/-!
Regression guard: a program that performs a DNS lookup must exit cleanly.

While developing the libuv finalization work in #14202, a `getAddrInfo` whose lookup reached the
system resolver made the process abort during exit — after `main` had already produced correct
output — with a libmalloc `POINTER_BEING_FREED_WAS_NOT_ALLOCATED` raised inside
`_pthread_tsd_cleanup`. The cause was mimalloc 3.4.1 parking its thread heap in macOS pthread TSD
slots 126/127, which are not actually free, so `_pthread_tsd_cleanup` passed a mimalloc-internal
pointer to another key's destructor (mimalloc issue #1333, fixed in 3.4.3). Joining the libuv loop
thread is what made that thread run `_pthread_exit` for the first time and exposed it.

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
