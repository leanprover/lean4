/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Leanpkg2.Manifest
import Leanpkg2.BuildConfig

open System

namespace Leanpkg2

def lockFileName : System.FilePath := ".leanpkg-lock"

partial def withLockFile (x : IO α) : IO α := do
  acquire
  try
    x
  finally
    IO.removeFile lockFileName
  where
    acquire (firstTime := true) :=
      try
        -- TODO: lock file should ideally contain PID
        if !System.Platform.isWindows then
          discard <| IO.Prim.Handle.mk lockFileName "wx"
        else
          -- `x` mode doesn't seem to work on Windows even though it's listed at
          -- https://docs.microsoft.com/en-us/cpp/c-runtime-library/reference/fopen-wfopen?view=msvc-160
          -- ...? Let's use the slightly racy approach then.
          if ← lockFileName.pathExists then
            throw <| IO.Error.alreadyExists 0 ""
          discard <| IO.Prim.Handle.mk lockFileName "w"
      catch
        | IO.Error.alreadyExists _ _ => do
          if firstTime then
            IO.eprintln s!"Waiting for prior leanpkg invocation to finish... (remove '{lockFileName}' if stuck)"
          IO.sleep (ms := 300)
          acquire (firstTime := false)
        | e => throw e

def execMake (manifest : Manifest) (makeArgs : List String) (cfg : BuildConfig) : IO Unit := withLockFile do
  let timeoutArgs :=
    match manifest.timeout with
    | some t => ["-T", toString t]
    | none => []
  let leanArgs := timeoutArgs ++ cfg.leanArgs
  let mut spawnArgs := {
    cmd := "sh"
    cwd := manifest.effectivePath
    args := #["-c", s!"\"{← IO.appDir}/leanmake\" PKG={cfg.pkg} LEAN_OPTS=\"{" ".intercalate leanArgs}\" LEAN_PATH=\"{cfg.leanPath}\" {" ".intercalate makeArgs} MORE_DEPS+=\"{" ".intercalate (cfg.moreDeps.map toString)}\" >&2"]
  }
  execCmd spawnArgs
