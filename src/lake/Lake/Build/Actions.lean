/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone, Siddharth Bhat
-/
module

prelude
public import Lake.Util.Log
public import Lake.Build.WrappedExec
import Lake.Util.Proc
import Lake.Util.FilePath
import Lake.Util.IO
import Lake.Util.Url
import Init.Data.String.Search
import Init.Data.String.TakeDrop
import Init.System.Platform
import Lean.CoreM
import Lean.Compiler.Options

/-! # Common Build Actions
Low level actions to build common Lean artifacts via the Lean toolchain.
-/

open System
open Lean hiding SearchPath

namespace Lake

/--
The `lean` invocation for a module, as computed by `mkLeanModuleArgs`.

`outputs` lists the output files `args` names, with path strings
byte-identical to the corresponding argv tokens. Wrappers rely on this
congruence (e.g. a sandbox wrapper computes its redirect table as
`outputs ∩ args`).
-/
public structure LeanModuleInvocation where
  args : Array String
  /-- Output files embedded in `args` (see above). -/
  outputs : Array FilePath
  /-- When `true`, `-c` is omitted from `args`; the C output is produced by
  the separate `compileLeanIR` action instead. -/
  postponeCompile : Bool

/--
Compute the argv for invoking `lean` on a module given its resolved `ModuleSetup`, output
artifacts, and any extra `leanArgs`, together with the output files the argv names. Pure:
performs no IO and does not create the setup file.

Exposed for tooling that needs to reproduce Lake's exact `lean` invocation without running it
(e.g. static build-graph extraction).
-/
public def mkLeanModuleArgs
  (leanFile : FilePath) (setup : ModuleSetup) (setupFile : FilePath)
  (arts : ModuleArtifacts) (leanArgs : Array String := #[])
: LeanModuleInvocation := Id.run do
  let mut args := leanArgs.push leanFile.toString
  let mut outputs := #[]
  if let some oleanFile := arts.olean? then
    args := args ++ #["-o", oleanFile.toString]
    outputs := outputs.push oleanFile
  if let some ileanFile := arts.ilean? then
    args := args ++ #["-i", ileanFile.toString]
    outputs := outputs.push ileanFile
  let opts := setup.options.toOptions
  let postponeCompile := setup.isModule && Compiler.compiler.postponeCompile.get opts
  if !postponeCompile then
    if let some cFile := arts.c? then
      args := args ++ #["-c", cFile.toString]
      outputs := outputs.push cFile
  if let some bcFile := arts.bc? then
    args := args ++ #["-b", bcFile.toString]
    outputs := outputs.push bcFile
  args := args ++ #["--setup", setupFile.toString]
  args := args.push "--json"
  return {args, outputs, postponeCompile}

/-- Run the separate code generation process, optionally through a wrapper. -/
public def compileLeanIR
  (setupFile irFile cFile : FilePath)
  (leanPath : SearchPath := [])
  (leanir : FilePath := "leanir")
  (wrap? : Option WrappedExec.JobIO := none)
: LogIO Unit := do
  createParentDirs irFile
  createParentDirs cFile
  let job? := wrap?.map fun job => { job with
    inputs := job.inputs.push setupFile
    outputs := #[irFile, irFile.addExtension "sig", cFile]
  }
  WrappedExec.procOrWrapped {
    cmd := leanir.toString
    args := #[setupFile.toString, irFile.toString, cFile.toString]
    env := #[("LEAN_PATH", leanPath.toString)]
  } job?

/-- Invoke Lean with optional declared-I/O metadata for `$LAKE_WRAPPED_EXEC`.
The caller supplies import artifacts; this action adds the source, setup file,
dynamic libraries, plugins, and the outputs of elaboration. Deferred code generation
runs separately through `compileLeanIR`. -/
public def compileLeanModule
  (leanFile relLeanFile : FilePath)
  (setup : ModuleSetup) (setupFile : FilePath)
  (arts : ModuleArtifacts)
  (leanArgs : Array String := #[])
  (leanPath : SearchPath := [])
  (lean : FilePath := "lean")
  (wrap? : Option WrappedExec.JobIO := none)
: LogIO Unit := do
  if let some oleanFile := arts.olean? then createParentDirs oleanFile
  if let some ileanFile := arts.ilean? then createParentDirs ileanFile
  let {args, outputs, postponeCompile} := mkLeanModuleArgs leanFile setup setupFile arts leanArgs
  if !postponeCompile then
    if let some cFile := arts.c? then createParentDirs cFile
  if let some bcFile := arts.bc? then createParentDirs bcFile
  createParentDirs setupFile
  IO.FS.writeFile setupFile (toJson setup).pretty
  withLogErrorPos do
  let job? := wrap?.map fun job => { job with
    -- The setup file, dynlibs, and plugins are declared inputs too.
    -- Lake writes the setup file before dispatch. Wrappers must not return
    -- a translated copy as an output. Undeclared metaprogram reads are not tracked.
    inputs := #[leanFile, setupFile] ++ job.inputs
              ++ setup.dynlibs ++ setup.plugins.map (·.path)
    -- In module mode `lean` derives companion outputs (`.olean.server`,
    -- `.olean.private`, `.ir.sig`, `.ir`) from the `-o` path; they never appear in
    -- argv, so declare them from `arts`. With `postponeCompile` the `.ir.sig`,
    -- `.ir`, and `.c` are produced by the separate `leanir` job instead.
    outputs := outputs ++ #[arts.oleanServer?, arts.oleanPrivate?].filterMap id
      ++ (if postponeCompile then #[] else #[arts.irSig?, arts.ir?].filterMap id)
  }
  let out ← Lake.WrappedExec.runRawProcOrWrapped
    { args, cmd := lean.toString,
      env := #[("LEAN_PATH", leanPath.toString)] }
    job?
  let outLogPos ← getLogPos
  unless out.stdout.isEmpty do
    let txt ← out.stdout.split '\n' |>.foldM (init := "") fun (txt : String) ln => do
      let ln := ln.copy
      if let .ok (msg : SerialMessage) := Json.parse ln >>= fromJson? then
        unless txt.isEmpty do
          logInfo s!"stdout:\n{txt}"
        let msg := {msg with fileName := mkRelPathString relLeanFile}
        logSerialMessage msg
        return txt
      else if txt.isEmpty && ln.isEmpty then
        return txt
      else
        return txt ++ ln ++ "\n"
    unless txt.isEmpty do
      logInfo s!"stdout:\n{txt}"
  unless out.stderr.isEmpty do
    logInfo s!"stderr:\n{out.stderr.trimAscii}"
  -- Elide the generic "Lean exited with code 1" when Lean already
  -- reported errors (the usual compiler-failure case). Keep it for other
  -- nonzero codes, for code 1 without diagnostics, and for the anomalous
  -- case where Lean logs errors but exits successfully.
  -- See https://github.com/leanprover/lean4/issues/10825
  let hasErrors := (← getLog).takeFrom outLogPos |>.any (·.level matches .error)
  if out.exitCode = 1 && hasErrors then
    failure
  else if out.exitCode ≠ 0 || hasErrors then
    error s!"Lean exited with code {out.exitCode}"

public def compileO
  (oFile srcFile : FilePath)
  (moreArgs : Array String := #[]) (compiler : FilePath := "cc")
: LogIO Unit := do
  createParentDirs oFile
  proc {
    cmd := compiler.toString
    args := #["-c", "-o", oFile.toString, srcFile.toString] ++ moreArgs
  }

public def mkArgs (basePath : FilePath) (args : Array String) : LogIO (Array String) := do
  -- Use response file to avoid potentially exceeding CLI length limits.
  -- On Windows this is always needed; on macOS/Linux this is needed for large
  -- projects like Mathlib where the number of object files exceeds ARG_MAX.
  let rspFile := basePath.addExtension "rsp"
  let h ← IO.FS.Handle.mk rspFile .write
  args.forM fun arg =>
    -- Escape special characters
    let arg := arg.foldl (init := "") fun s c =>
      if c == '\\' || c == '"' then
        s.push '\\' |>.push c
      else
        s.push c
    h.putStr s!"\"{arg}\"\n"
  return #[s!"@{rspFile}"]

public def compileStaticLib
  (libFile : FilePath) (oFiles : Array FilePath)
  (ar : FilePath := "ar") (thin := false)
: LogIO Unit := do
  createParentDirs libFile
  -- `ar rcs` does not remove old files from the archive, so it must be deleted first
  removeFileIfExists libFile
  let args := #["rcs"]
  let args := if thin then args.push "--thin" else args
  let args := args.push libFile.toString ++ (← mkArgs libFile <| oFiles.map toString)
  proc {cmd := ar.toString, args}

public def compileSharedLib
  (libFile : FilePath) (linkArgs : Array String)
  (linker : FilePath := "cc") (macosxDeploymentTarget? : Option String := none)
: LogIO Unit := do
  createParentDirs libFile
  proc {
    cmd := linker.toString
    args := #["-shared", "-o", libFile.toString] ++ (← mkArgs libFile linkArgs)
    -- See `BuildConfig.macosxDeploymentTarget?` for details
    env := macosxDeploymentTarget?.elim #[] fun ver => #[("MACOSX_DEPLOYMENT_TARGET", some ver)]
  }

public def compileExe
  (binFile : FilePath) (linkArgs : Array String)
  (linker : FilePath := "cc") (macosxDeploymentTarget? : Option String := none)
: LogIO Unit := do
  createParentDirs binFile
  proc {
    cmd := linker.toString
    args := #["-o", binFile.toString] ++ (← mkArgs binFile linkArgs)
    -- See `BuildConfig.macosxDeploymentTarget?` for details
    env :=  macosxDeploymentTarget?.elim #[] fun ver => #[("MACOSX_DEPLOYMENT_TARGET", some ver)]
  }

/-- Download a file using `curl`, clobbering any existing file. -/
public def download
  (url : String) (file : FilePath) (headers : Array String := #[])
: LogIO PUnit := do
  if (← file.pathExists) then
    IO.FS.removeFile file
  else
    createParentDirs file
  let args := #["-s", "-S", "-f", "-o", file.toString, "-L", url]
  let args := headers.foldl (init := args) (· ++ #["-H", ·])
  proc (quiet := true) {cmd := ← Internal.getCurl, args}

/-- Unpack an archive `file` using `tar` into the directory `dir`. -/
public def untar (file : FilePath) (dir : FilePath) (gzip := true) : LogIO PUnit := do
  IO.FS.createDirAll dir
  let mut opts := "-xvv"
  if gzip then
    opts := opts.push 'z'
  proc (quiet := true) {
    cmd := "tar",
    args := #[opts, "-f", file.toString, "-C", dir.toString]
  }

/-- Pack a directory `dir` using `tar` into the archive `file`. -/
public def tar
  (dir : FilePath) (file : FilePath)
  (gzip := true) (excludePaths : Array FilePath := #[])
: LogIO PUnit := do
  createParentDirs file
  let mut args := #["-cvv"]
  if gzip then
    args := args.push "-z"
  for path in excludePaths do
    args := args.push s!"--exclude={path}"
  proc (quiet := true) {
    cmd := "tar"
    args := args ++ #["-f", file.toString, "-C", dir.toString, "."]
    -- don't pack `._` files on MacOS
    env := if Platform.isOSX then #[("COPYFILE_DISABLE", "true")] else #[]
  }
