import Lake
open Lake DSL

package test

@[default_target] lean_lib Fail1
@[default_target] lean_lib Fail2

-- SlowChain: two-module library where B imports A.
-- SlowChain.A takes ~3 seconds to compile (via #eval IO.sleep).
-- SlowChain.B should NOT be compiled when the build is cancelled while A is in-flight;
-- mapM checks the cancellation token before firing the dependent task (see test.sh).
@[default_target] lean_lib SlowChain where
  globs := #[.submodules `SlowChain]

-- slowA: sleeps 3 seconds then writes a marker file.
-- This target runs independently of the failing ones and will be in-flight
-- when cancellation is triggered by the Fail1/Fail2 errors.
@[default_target]
target slowA pkg : Unit := Job.async do
  IO.sleep 3000
  IO.FS.writeFile (pkg.dir / "slowA.produced.out") ""

-- slowBWork: writes a marker file. NOT a default target -- only reachable
-- via slowB's dependency chain. If bindM sees cancellation is active,
-- it returns Job.cancelled and this body never runs.
target slowBWork pkg : Unit := Job.async do
  IO.FS.writeFile (pkg.dir / "slowB.produced.out") ""

-- slowB: after slowA completes, fetches slowBWork.
-- By the time slowA finishes (3s), cancellation is already active (set within
-- ~200ms when Fail1/Fail2 are detected). bindM sees the token and returns
-- Job.cancelled, so slowBWork's body never executes.
@[default_target]
target slowB : Unit := do
  let jobA ← slowA.fetch
  jobA.bindM fun _ => JobM.runFetchM slowBWork.fetch
