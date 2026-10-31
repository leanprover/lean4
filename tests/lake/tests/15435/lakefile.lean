module
import Lake

/-! # Facet keys (#15435)

Exercise package-elided, package-named and module facet dependencies, and check that Lake fetches a
facet named in `plugins` or `moreLinkLibs` before the fetch function that names it returns, unless
it is a package's own facet or the job of its target has not finished.
-/
open Lake DSL

package test

lean_lib Lib

lean_exe a where
  root := `A

lean_lib NeedsElided where
  needs := #[`@/a:exe]

lean_lib NeedsNamed where
  needs := #[`@test/a:exe]

lean_lib NeedsModule where
  needs := #[`+Lib:c.o.noexport]

lean_lib Plugged where
  plugins := #[`@/Lib:shared]

lean_lib Linked where
  moreLinkLibs := #[`@/Lib:shared]

lean_lib Delayed where
  plugins := #[`@/delayed:shared]

lean_lib Gated where
  plugins := #[`@/Lib:gated]

/--
Fails unless the build store has a job for `Lib:shared`.

The test builds the targets below with one worker (`LEAN_NUM_THREADS=1`). The build's top-level
fetch runs in a pool task and holds that worker, and nothing after the fetch of the key waits on a
task, so a fetch left to a job continuation cannot have run yet.
-/
def checkStored : FetchM (Job Unit) := do
  let some lib ← findLeanLib? `Lib | error "library `Lib` not found"
  let key := lib.shared.key
  let stored ← FetchM.ofFn fun _ _ _ store _ log => do
    return .ok ((← store.get).contains key) log
  unless stored do
    error s!"`{key}` was not fetched before the fetch function that names it returned"
  return .nil

target pluginsFetched : Unit := do
  let some mod ← findModule? `Plugged | error "module `Plugged` not found"
  discard mod.presetup.fetch
  checkStored

target linkLibsFetched : Unit := do
  let some mod ← findModule? `Linked | error "module `Linked` not found"
  discard mod.dynlib.fetch
  checkStored

/-- A promise that `fetchThenRelease` resolves after it fetches the `presetup` of a module. -/
target releasePromise : IO.Promise Unit := do
  return .pure (← IO.Promise.new)

/-- `Lib`, from a job that finishes only once `releasePromise` is resolved. -/
target delayed : LeanLib := do
  let promise ← (← releasePromise.fetch).await
  let some lib ← findLeanLib? `Lib | error "library `Lib` not found"
  return .ofTask <| promise.result?.map fun _ => .ok lib {}

/-- Waits for `releasePromise`, and then fetches the library's shared library. -/
library_facet gated lib : Dynlib := do
  let promise ← (← releasePromise.fetch).await
  discard <| IO.wait promise.result?
  lib.shared.fetch

/--
Fetches the `presetup` of the module `name`, and then resolves the promise that its plugin waits
for. This terminates only if the fetch returns without waiting for the plugin.
-/
def fetchThenRelease (name : Lean.Name) : FetchM (Job Unit) := do
  let promise ← (← releasePromise.fetch).await
  let some mod ← findModule? name | error s!"module `{name}` not found"
  let job ← mod.presetup.fetch
  promise.resolve ()
  return job.map fun _ => ()

target delayedFetched : Unit := fetchThenRelease `Delayed

target gatedFetched : Unit := fetchThenRelease `Gated
