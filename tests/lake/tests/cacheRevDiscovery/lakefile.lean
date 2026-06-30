import Lake
open Lake DSL

/-!
Harness for testing `RevDiscovery.discover` — the revision walk behind
`lake cache get`. The `discoverWalk` script runs the walk over the current Git
repo with a *stub* `lookup` (no network/storage), so `test.sh` can assert the
`nearest` vs `head` policies on a controlled commit history.
-/

package test

/--
Probes `RevDiscovery.discover` with a stub `lookup` that "hits" only the revision
given as the first argument. Prints `nearest=<r> head=<r>`, where `<r>` is `HIT`
if discovery returned the target and `MISS` otherwise. An optional second argument
bounds the walk (the `--max-revs` equivalent).
-/
script discoverWalk args do
  match args with
  | [] =>
    IO.eprintln "usage: discoverWalk <targetRev> [maxRevs]"
    return 1
  | targetRev :: rest =>
    let maxRevs? := rest.head?.bind String.toNat?
    let repo := GitRepo.mk (← IO.currentDir)
    let scope := CacheServiceScope.ofString "test"
    let lookup : GitRev → LoggerIO (Option GitRev) := fun rev =>
      pure <| if rev == targetRev then some rev else none
    let probe (policy : RevDiscovery) : ScriptM String := do
      let res? ← (policy.discover repo maxRevs? .error "test" scope lookup).run?'
      return if res?.isSome then "HIT" else "MISS"
    let n ← probe .nearest
    let h ← probe .head
    IO.println s!"nearest={n} head={h}"
    return 0
