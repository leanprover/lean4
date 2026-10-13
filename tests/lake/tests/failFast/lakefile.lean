import Lake
open Lake DSL

/-!
Fixture for `--fail-fast`: `Fail` fails quickly while the slow targets are in
flight. Under `--fail-fast`, `slowA` completes only once the cancellation token
is set, so everything downstream of it starts strictly after cancellation is
active: `slowA` must still complete (in-flight work is drained), but its
dependents (`slowB`'s `bindM`, `slowC`'s `mapM`, and `Slow`'s compile) must not
run. Without `--fail-fast` there is no token, `slowA` completes immediately, and
every other target must build despite `Fail`'s failure.

Synchronization is through the build graph alone: dependents of `slowA` order
themselves against it by depending on it, never by waiting out of band.
-/

package test

@[default_target] lean_lib Fail

-- Under `--fail-fast`, waits (bounded, in case cancellation never comes) for
-- the token, so every dependent below starts with cancellation already active.
-- Dedicated priority so the wait does not hold a task-pool worker.
@[default_target]
target slowA pkg : Unit := Job.async (prio := .dedicated) do
  if let some tk := (← getBuildContext).cancelTk? then
    for _ in [0:100] do
      if ← tk.isSet then break
      IO.sleep 100
  IO.FS.writeFile (pkg.dir / "slowA.produced.out") ""

@[default_target]
target slowB pkg : Unit := do
  let jobA ← slowA.fetch
  jobA.bindM fun _ => do
    IO.FS.writeFile (pkg.dir / "slowB.produced.out") ""
    pure (Job.pure ())

@[default_target]
target slowC pkg : Unit := do
  let jobA ← slowA.fetch
  jobA.mapM fun _ =>
    IO.FS.writeFile (pkg.dir / "slowC.produced.out") ""

-- `needs` gates the module builds on `slowA`, covering cancellation of the
-- module pipeline itself rather than just of bare target continuations.
@[default_target] lean_lib Slow where
  needs := #[slowA]
