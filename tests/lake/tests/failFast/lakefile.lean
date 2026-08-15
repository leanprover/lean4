import Lake
open Lake DSL

/-!
Fixture for `--fail-fast`: `Fail` fails quickly while the slow targets are in
flight. `slowA` completes only once the cancellation token is set, so the
continuations under test (`slowB`'s `bindM`, `SlowChain.B`'s compile via
`mapM`) start strictly after cancellation is active: `slowA` must still
complete (in-flight work is drained), but the continuations must not run.
-/

package test

@[default_target] lean_lib Fail

@[default_target] lean_lib SlowChain where
  globs := #[.submodules `SlowChain]

-- Waits for cancellation (bounded, in case it never comes), then writes the
-- marker `SlowChain/A.lean` also synchronizes on.
@[default_target]
target slowA pkg : Unit := Job.async do
  let some tk := (← getBuildContext).cancelling?
    | error "cancellation token missing (build not run with --fail-fast)"
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
