/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Proc
import Lake.Package

open System

namespace Lake

def lockfile : FilePath := buildPath / ".lake-lock"

partial def withLockFile (x : IO α) : IO α := do
  acquire
  try
    x
  finally
    IO.removeFile lockfile
  where
    acquire (firstTime := true) := do
      IO.createDirAll lockfile.parent.get!
      try
        -- TODO: lock file should ideally contain PID
        if !Platform.isWindows then
          discard <| IO.Prim.Handle.mk lockfile "wx"
        else
          -- `x` mode doesn't seem to work on Windows even though it's listed at
          -- https://docs.microsoft.com/en-us/cpp/c-runtime-library/reference/fopen-wfopen?view=msvc-160
          -- ...? Let's use the slightly racy approach then.
          if ← lockfile.pathExists then
            throw <| IO.Error.alreadyExists 0 ""
          discard <| IO.Prim.Handle.mk lockfile "w"
      catch
        | IO.Error.alreadyExists _ _ => do
          if firstTime then
            IO.eprintln s!"Waiting for prior lake invocation to finish... (remove '{lockfile}' if stuck)"
          IO.sleep (ms := 300)
          acquire (firstTime := false)
        | e => throw e

def execMake
(pkg : Package) (deps : List Package) (makeArgs leanArgs : List String := [])
: IO Unit := withLockFile do
  let timeoutArgs :=
    match pkg.timeout with
    | some t => ["-T", toString t]
    | none => []
  let leanOptsStr := " ".intercalate <| timeoutArgs ++ leanArgs
  let leanPathStr := SearchPath.toString <| pkg.buildDir :: deps.map (·.buildDir)
  let makeArgsStr := " ".intercalate makeArgs
  let moreDepsStr := " ".intercalate <| deps.map (·.oleanRoot.toString)
  let mut spawnArgs := {
    cmd := "sh"
    cwd := pkg.dir
    args := #["-c", s!"leanmake PKG={pkg.module} LEAN_OPTS=\"{leanOptsStr}\" LEAN_PATH=\"{leanPathStr}\" {makeArgsStr} MORE_DEPS+=\"{moreDepsStr}\" >&2"]
  }
  execCmd spawnArgs
