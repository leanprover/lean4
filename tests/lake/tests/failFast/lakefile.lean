import Lake
open Lake DSL

/-!
Fixture for `--fail-fast`: `Fail` fails quickly while the slow targets are in
flight. Under `--fail-fast`, `slowA` completes only once the cancellation token
is set, so the continuations under test (`slowB`'s `bindM`, `SlowChain.B`'s
compile via `mapM`) start strictly after cancellation is active: `slowA` must
still complete (in-flight work is drained), but the continuations must not run.
Without `--fail-fast` there is no token, `slowA` completes immediately, and
every other target must build despite `Fail`'s failure.
-/

package test

@[default_target] lean_lib Fail

@[default_target] lean_lib SlowChain where
  globs := #[.submodules `SlowChain]

-- Under `--fail-fast`, waits (bounded, in case cancellation never comes) for
-- the token before writing the marker that `SlowChain/A.lean` also
-- synchronizes on. Dedicated priority so the wait does not hold a task-pool
-- worker.
@[default_target]
target slowA pkg : Unit := Job.async (prio := .dedicated) do
  if let some tk := (← getBuildContext).cancelling? then
    for _ in [0:600] do
      if ← tk.isSet then break
      IO.sleep 100
  IO.FS.writeFile (pkg.dir / "slowA.produced.out") ""

@[default_target]
target slowB pkg : Unit := do
  let jobA ← slowA.fetch
  jobA.bindM fun _ => do
    IO.FS.writeFile (pkg.dir / "slowB.produced.out") ""
    pure (Job.pure ())
