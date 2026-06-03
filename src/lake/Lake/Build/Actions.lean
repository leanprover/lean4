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
Compute the argv for invoking `lean` on a module given its resolved `ModuleSetup`, output
artifacts, and any extra `leanArgs`. Pure: performs no IO and does not create the setup file.
Returns `(args, postponeCompile)`; when `postponeCompile` is `true`, `-c` is omitted from `args`
(the C output is produced by a follow-up `leanir` call instead — see `compileLeanModule`).

Exposed for tooling that needs to reproduce Lake's exact `lean` invocation without running it
(e.g. static build-graph extraction).
-/
public def mkLeanModuleArgs
  (leanFile : FilePath) (setup : ModuleSetup) (setupFile : FilePath)
  (arts : ModuleArtifacts) (leanArgs : Array String := #[])
: Array String × Bool := Id.run do
  let mut args := leanArgs.push leanFile.toString
  if let some oleanFile := arts.olean? then
    args := args ++ #["-o", oleanFile.toString]
  if let some ileanFile := arts.ilean? then
    args := args ++ #["-i", ileanFile.toString]
  let opts := setup.options.toOptions
  let postponeCompile := setup.isModule && Compiler.compiler.postponeCompile.get opts
  if !postponeCompile then
    if let some cFile := arts.c? then
      args := args ++ #["-c", cFile.toString]
  if let some bcFile := arts.bc? then
    args := args ++ #["-b", bcFile.toString]
  args := args ++ #["--setup", setupFile.toString]
  args := args.push "--json"
  return (args, postponeCompile)

/-- Collect the absolute output paths Lake expects lean to produce for `arts`.
Used to populate the wrapped-exec manifest's `outputs` list so workers know
which files to ship back. `setupFile` is intentionally NOT listed here — it's
an input (written by Lake before the proc invocation, read by lean), and
shipping a worker-translated copy back would clobber the head's original. -/
public def collectLeanModuleOutputPaths
  (arts : ModuleArtifacts) (postponeCompile : Bool)
: Array FilePath := Id.run do
  let mut xs : Array FilePath := #[]
  if let some f := arts.olean? then xs := xs.push f
  if let some f := arts.ilean? then xs := xs.push f
  if !postponeCompile then
    if let some f := arts.c? then xs := xs.push f
  if let some f := arts.oleanServer? then xs := xs.push f
  if let some f := arts.oleanPrivate? then xs := xs.push f
  if let some f := arts.ir? then xs := xs.push f
  if let some f := arts.bc? then xs := xs.push f
  return xs

/-- Wrapped-exec parameters (consulted only when both are populated):
* `extraInputs` — transitive olean closure declared in the manifest's
  `inputs` list, so a wrapper can know what to materialize ahead of `lean`
  (see `Lake.collectLeanInputClosure`).
* `lakeRoots` — `(workspace, lakeHome, toolchain, toolchainRoot)`; when
  `some _` AND `$LAKE_WRAPPED_EXEC` is set, the invocation is routed
  through the wrapper. Otherwise this falls through to direct `rawProc`.
* `jobId` — free-form label for logging. -/
public def compileLeanModule
  (leanFile relLeanFile : FilePath)
  (setup : ModuleSetup) (setupFile : FilePath)
  (arts : ModuleArtifacts)
  (leanArgs : Array String := #[])
  (leanPath : SearchPath := [])
  (lean : FilePath := "lean")
  (leanir : FilePath := "leanir")
  (extraInputs : Array FilePath := #[])
  (lakeRoots : Option (FilePath × FilePath × FilePath × FilePath) := none)
  (jobId : String := "")
: LogIO Unit := do
  if let some oleanFile := arts.olean? then createParentDirs oleanFile
  if let some ileanFile := arts.ilean? then createParentDirs ileanFile
  let (args, postponeCompile) := mkLeanModuleArgs leanFile setup setupFile arts leanArgs
  if !postponeCompile then
    if let some cFile := arts.c? then createParentDirs cFile
  if let some bcFile := arts.bc? then createParentDirs bcFile
  createParentDirs setupFile
  IO.FS.writeFile setupFile (toJson setup).pretty
  withLogErrorPos do
  let outputs := collectLeanModuleOutputPaths arts postponeCompile
  -- `lean` also opens any dynlibs / plugins declared in the setup at runtime
  -- (e.g. `precompileModules` projects). A sandbox wrapper that allow-lists
  -- from `inputs` would block those without them; include them so the inputs
  -- list is a complete read-set for the spawned `lean`.
  let inputs := #[leanFile, setupFile] ++ extraInputs
                ++ setup.dynlibs ++ setup.plugins.map (·.path)
  let out ← Lake.WrappedExec.runRawProcOrWrapped
    { args, cmd := lean.toString,
      env := #[("LEAN_PATH", leanPath.toString)] }
    inputs outputs lakeRoots jobId
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
  if out.exitCode ≠ 0 then
    error s!"Lean exited with code {out.exitCode}"
  if postponeCompile then
    if let (some irFile, some cFile) := (arts.ir?, arts.c?) then
      createParentDirs irFile
      createParentDirs cFile
      try
        proc {
          cmd := leanir.toString
          args := #[setupFile.toString, irFile.toString, cFile.toString]
          env := #[
            ("LEAN_PATH", leanPath.toString)
          ]
        }
      catch e =>
        if let some oleanFile := arts.olean? then
          removeFileIfExists oleanFile
        throw e

/--
Compute the argv for invoking the C compiler in object-compilation mode. Pure helper exposed for
tooling that needs to reproduce the invocation without running it.
-/
public def mkCcCompileArgs
  (oFile srcFile : FilePath) (moreArgs : Array String := #[])
: Array String :=
  #["-c", "-o", oFile.toString, srcFile.toString] ++ moreArgs

public def compileO
  (oFile srcFile : FilePath)
  (moreArgs : Array String := #[]) (compiler : FilePath := "cc")
: LogIO Unit := do
  createParentDirs oFile
  proc {
    cmd := compiler.toString
    args := mkCcCompileArgs oFile srcFile moreArgs
  }

private def escapeRspArg (arg : String) : String :=
  arg.foldl (init := "") fun s c =>
    if c == '\\' || c == '"' then
      s.push '\\' |>.push c
    else
      s.push c

/--
Render the contents of a response file in the format `mkArgs` writes: one quoted line per arg,
with `\\` and `"` escaped. Pure helper exposed for tooling that needs the rsp content without
materializing it on disk.
-/
public def renderRspContents (args : Array String) : String := Id.run do
  let mut out := ""
  for arg in args do
    out := out ++ s!"\"{escapeRspArg arg}\"\n"
  return out

public def mkArgs (basePath : FilePath) (args : Array String) : LogIO (Array String) := do
  -- Use response file to avoid potentially exceeding CLI length limits.
  -- On Windows this is always needed; on macOS/Linux this is needed for large
  -- projects like Mathlib where the number of object files exceeds ARG_MAX.
  let rspFile := basePath.addExtension "rsp"
  let h ← IO.FS.Handle.mk rspFile .write
  args.forM fun arg => h.putStr s!"\"{escapeRspArg arg}\"\n"
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

def getMacOSXDeploymentEnv : BaseIO (Array (String × Option String)) := do
  -- It is difficult to identify the correct minor version here, leading to linking warnings like:
  -- `ld64.lld: warning: /usr/lib/system/libsystem_kernel.dylib has version 13.5.0, which is newer than target minimum of 13.0.0`
  -- In order to suppress these we set the MACOSX_DEPLOYMENT_TARGET variable into the far future.
  if System.Platform.isOSX then
    match (← IO.getEnv "MACOSX_DEPLOYMENT_TARGET") with
    | some _ => return #[]
    | none => return #[("MACOSX_DEPLOYMENT_TARGET", some "99.0")]
  else
    return #[]

public def compileSharedLib
  (libFile : FilePath) (linkArgs : Array String) (linker : FilePath := "cc")
: LogIO Unit := do
  createParentDirs libFile
  proc {
    cmd := linker.toString
    args := #["-shared", "-o", libFile.toString] ++ (← mkArgs libFile linkArgs)
    env := ← getMacOSXDeploymentEnv
  }

public def compileExe
  (binFile : FilePath) (linkArgs : Array String) (linker : FilePath := "cc")
: LogIO Unit := do
  createParentDirs binFile
  proc {
    cmd := linker.toString
    args := #["-o", binFile.toString] ++ (← mkArgs binFile linkArgs)
    env := ← getMacOSXDeploymentEnv
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
  proc (quiet := true) {cmd := "curl", args}

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
