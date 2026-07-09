/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

prelude
public import Lake.Util.Log
public import Lake.Util.Proc
import Init.Data.String.Search
import Init.System.IO
import Lean.Data.Json

/-! # Wrapped-execution hook for Lake's `proc` invocations

When `$LAKE_WRAPPED_EXEC` is set to a path, Lake routes selected subprocess
invocations through that path (the "wrapper") instead of invoking them
directly via `rawProc`.

Lake writes a JSON manifest carrying the exact `argv`, `env`, `cwd`, the set
of input files that must be available before the invocation runs, and the
set of output files Lake expects to find on disk after it completes. The
wrapper decides what to do with that — it can exec the named command itself
in any environment it likes, look up a cached result, hand off to a worker
pool, etc. From Lake's perspective the wrapper is indistinguishable from
the original binary: same stdout/stderr/exit-code shape.

The manifest carries only what the build system uniquely knows and a
wrapper cannot deduce: the spawn recipe (`cmd`/`args`/`env`/`cwd`) and the
declared input/output file sets. Everything a wrapper can derive itself
(toolchain location from `cmd`, workspace layout from its own deployment
configuration) is deliberately left out.

Design constraints:

* No orchestration logic in Lake. The wrapper is opaque; Lake doesn't know
  whether it sandboxes, caches, dispatches, traces, or just exec's the
  command in-process.
* Call sites derive `inputs` and `outputs` from the structures Lake
  already maintains for incremental builds and the artifact cache
  (`fetchTransImportArts` for the lean module input closure, the argv
  construction itself for outputs), keeping the manifest consistent with
  what the build actually reads and writes.
* Lake stays the executor: cache, hashes, trace sidecars, incremental
  rebuilds all continue to work because Lake invokes the wrapper the same
  way it would invoke the original binary, and outputs must reappear at
  the paths the manifest names by the time the wrapper returns.
-/

open System
open Lean (Json toJson)

namespace Lake.WrappedExec

/-- Version of the manifest JSON format (the `schema_version` field). -/
public def schemaVersion : Nat := 1

/--
The per-job metadata a wrappable call site declares alongside the spawn
arguments: a free-form job label plus the declared input/output file sets.
Call sites construct this incrementally (e.g. the module build fetches the
import closure, then `compileLeanModule` extends `inputs` with the files it
itself writes/reads and fills `outputs`).
-/
public structure JobIO where
  /-- Free-form label identifying the job (used in logs and the manifest). -/
  jobId   : String
  /-- Files that must exist on disk before the command runs. -/
  inputs  : Array FilePath := #[]
  /-- Files Lake expects on disk after the command exits successfully.
  Paths embedded in the command's argv appear here byte-identically
  (sandbox wrappers compute their redirect table as `outputs ∩ args`). -/
  outputs : Array FilePath := #[]
  deriving Inhabited

public structure Manifest extends JobIO where
  cmd  : String
  args : Array String
  env  : Array (String × String)
  cwd  : Option FilePath := none
  deriving Inhabited

public def manifestToJson (m : Manifest) : Json :=
  let envObj : Json := Json.mkObj (m.env.toList.map fun (k, v) => (k, toJson v))
  Json.mkObj [
    ("schema_version", toJson schemaVersion),
    ("job_id",         toJson m.jobId),
    ("cmd",            toJson m.cmd),
    ("args",           toJson m.args),
    ("env",            envObj),
    ("cwd",            toJson (m.cwd.map FilePath.toString)),
    ("inputs",         toJson (m.inputs.map FilePath.toString)),
    ("outputs",        toJson (m.outputs.map FilePath.toString))
  ]

private def writeManifestTemp (m : Manifest) : IO FilePath := do
  let tmpDir ← (← IO.getEnv "TMPDIR").getDM (pure "/tmp")
  let dir := FilePath.mk tmpDir
  IO.FS.createDirAll dir
  let pid ← IO.Process.getPID
  let now ← IO.monoNanosNow
  let safe := m.jobId.foldl (init := "") fun acc c =>
    if c.isAlphanum then acc.push c else acc.push '_'
  let path := dir / s!"lake-wrapped-{pid}-{now}-{safe}.json"
  IO.FS.writeFile path (manifestToJson m).pretty
  return path

/-- Invoke the wrapper binary with `manifest`. Returns the wrapper's
`IO.Process.Output` (stdout/stderr/exitCode), shaped identically to what
`rawProc` would return for a direct invocation. -/
public def runViaWrapper (wrapperPath : String) (m : Manifest) (quiet := false) : LogIO IO.Process.Output := do
  let manifestPath ← writeManifestTemp m
  unless quiet do
    logVerbose s!"wrapped-exec: wrapper={wrapperPath} manifest={manifestPath} job={m.jobId}"
  withLogErrorPos do
  let outcome ← (IO.Process.output {
    cmd := wrapperPath,
    args := #[manifestPath.toString]
  } |>.toBaseIO)
  -- Clean up the manifest on both success and failure to avoid leaking
  -- a temp file when the wrapper itself can't be spawned.
  try IO.FS.removeFile manifestPath catch _ => pure ()
  match outcome with
  | .ok out => return out
  | .error err =>
    error s!"failed to execute wrapper '{wrapperPath}': {err}"

/--
Dispatch a `rawProc` invocation either directly or via `$LAKE_WRAPPED_EXEC`.
The invocation is routed through the wrapper when the env var is set AND the
call site declares its I/O via `job? := some _`.

`job? := none` means "this call site doesn't have enough metadata to be
wrapped"; we run the command directly even if `$LAKE_WRAPPED_EXEC` is set.
This lets the wrapped-exec path be extended to new call sites one at a time
without breaking others.
-/
public def runRawProcOrWrapped
  (args : IO.Process.SpawnArgs) (job? : Option JobIO) (quiet := false)
: LogIO IO.Process.Output := do
  match (← IO.getEnv "LAKE_WRAPPED_EXEC"), job? with
  | some wrapperPath, some job =>
    -- `args.env` is `Array (String × Option String)`; collapsing it into
    -- the manifest's string-to-string `env` object drops `none` entries
    -- (explicit unsets) and cannot express duplicate keys. Hooked call
    -- sites must therefore pass only plain key-value env entries; a call
    -- site that needs unsets requires an ordered array-of-pairs encoding
    -- and a `schema_version` bump.
    let envPairs : Array (String × String) := args.env.filterMap fun (k, v?) =>
      v?.map (k, ·)
    let m : Manifest := {
      toJobIO := job
      cmd := args.cmd, args := args.args, env := envPairs, cwd := args.cwd
    }
    runViaWrapper wrapperPath m (quiet := quiet)
  | _, _ =>
    rawProc args (quiet := quiet)

/-- `Lake.proc`, dispatched through `runRawProcOrWrapped`: identical logging
and failure behavior, with the invocation routed through
`$LAKE_WRAPPED_EXEC` when configured and `job? := some _`. -/
public def procOrWrapped
  (args : IO.Process.SpawnArgs) (job? : Option JobIO) (quiet := false)
: LogIO Unit := do
  withLogErrorPos do
  let out ← runRawProcOrWrapped args job?
  if out.exitCode = 0 then
    logOutput out (if quiet then logVerbose else logInfo)
  else
    logOutput out logInfo
    error s!"external command '{args.cmd}' exited with code {out.exitCode}"

end Lake.WrappedExec
