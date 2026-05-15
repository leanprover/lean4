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
invocations through that path (the "wrapper") instead of running them locally.

Lake writes a JSON manifest carrying the exact `argv`, `env`, `cwd`, the set of
input files that must be available before the invocation runs, and the set of
output files Lake expects to find on disk after it completes. The wrapper is
responsible for arranging for the command to be executed somewhere it can
satisfy those input/output declarations. From Lake's perspective the wrapper
is indistinguishable from the original binary — same stdout/stderr/exit-code
shape.

Concrete consumers include sandbox executors (use the input/output lists to
construct an isolated filesystem view), distributed-build orchestrators (ship
work to a worker pool), and content-addressable build farms. Lake is silent
about which is downstream.

Design constraints:

* No orchestration logic in Lake. The wrapper is opaque; Lake doesn't know
  whether it runs the command locally under a sandbox, dispatches to a
  worker pool, looks up a pre-built result in a cache, or anything else.
* Inputs are enumerated explicitly, not discovered. Callers (e.g. the lean
  module compile path) compute the full input closure they need ahead of
  time.
* Lake stays the executor: cache, hashes, trace sidecars, incremental
  rebuilds all continue to work because Lake invokes the wrapper the same
  way it would invoke the original binary, and the wrapper re-materializes
  outputs at the head-node paths Lake expects to read from later.
-/

open System
open Lean (Json toJson)

namespace Lake.WrappedExec

public structure Manifest where
  cmd       : String
  args      : Array String
  env       : Array (String × String)
  cwd       : Option FilePath := none
  inputs    : Array FilePath
  outputs   : Array FilePath
  workspace : FilePath
  lakeHome  : FilePath
  toolchain : FilePath
  toolchainRoot : FilePath
  jobId     : String
  deriving Inhabited

public def manifestToJson (m : Manifest) : Json :=
  let envObj : Json := Json.mkObj (m.env.toList.map fun (k, v) => (k, toJson v))
  Json.mkObj [
    ("job_id",         toJson m.jobId),
    ("cmd",            toJson m.cmd),
    ("args",           toJson m.args),
    ("env",            envObj),
    ("cwd",            toJson (m.cwd.map FilePath.toString)),
    ("inputs",         toJson (m.inputs.map FilePath.toString)),
    ("outputs",        toJson (m.outputs.map FilePath.toString)),
    ("workspace",      toJson m.workspace.toString),
    ("lake_home",      toJson m.lakeHome.toString),
    ("toolchain",      toJson m.toolchain.toString),
    ("toolchain_root", toJson m.toolchainRoot.toString)
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
`rawProc` would return for a local invocation. -/
public def runViaWrapper (wrapperPath : String) (m : Manifest) : LogIO IO.Process.Output := do
  let manifestPath ← writeManifestTemp m
  logVerbose s!"wrapped-exec: wrapper={wrapperPath} manifest={manifestPath} job={m.jobId}"
  withLogErrorPos do
  match (← IO.Process.output {
    cmd := wrapperPath,
    args := #[manifestPath.toString]
  } |>.toBaseIO) with
  | .ok out =>
    try IO.FS.removeFile manifestPath catch _ => pure ()
    return out
  | .error err =>
    error s!"failed to execute wrapper '{wrapperPath}': {err}"

/--
Dispatch a `rawProc` invocation either locally or via `$LAKE_WRAPPED_EXEC`.
When the env var is set AND `lakeRoots := some _`, the wrapper receives a
manifest with `inputs`/`outputs`/`workspace` metadata. Otherwise this falls
through to plain `rawProc`.

`lakeRoots := none` means "this call site doesn't have enough metadata to be
wrapped"; we fall through to local even if `$LAKE_WRAPPED_EXEC` is set. This
lets us extend the wrapped-exec path to new call sites one at a time without
breaking others.
-/
public def runRawProcOrWrapped
  (args : IO.Process.SpawnArgs)
  (inputs outputs : Array FilePath)
  (lakeRoots : Option (FilePath × FilePath × FilePath × FilePath))
  (jobId : String) (quiet := false)
: LogIO IO.Process.Output := do
  match (← IO.getEnv "LAKE_WRAPPED_EXEC"), lakeRoots with
  | some wrapperPath, some (workspace, lakeHome, toolchain, toolchainRoot) =>
    let envPairs : Array (String × String) := args.env.filterMap fun (k, v?) =>
      v?.map (k, ·)
    let m : Manifest := {
      cmd := args.cmd, args := args.args, env := envPairs, cwd := args.cwd
      inputs, outputs
      workspace, lakeHome, toolchain, toolchainRoot
      jobId
    }
    runViaWrapper wrapperPath m
  | _, _ =>
    rawProc args (quiet := quiet)

end Lake.WrappedExec
