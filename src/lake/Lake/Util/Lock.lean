/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Gabriel Ebner, Sebastian Ullrich
-/
prelude
import Init.System.IO

/-! # Lock File Utilities

This module defines utilities to use a file to ensure mutual exclusions
between processes manipulating some shared resource. Such a file is termed
a "lock file".

Lake does not currently use a lock file. Previously, Lake used one for builds,
but this was removed in [lean4#2445][1]. Without an API for catching `Ctrl-C`
during a build, the lock file was deemed too disruptive for users.

[1]: https://github.com/leanprover/lean4/pull/2445
-/

open System
namespace Lake

@[inline] partial def busyAcquireLockFile (lockFile : FilePath) : IO PUnit := do
  busyLoop true
where
  busyLoop firstTime :=
    try
      if let some dir := lockFile.parent then
        IO.FS.createDirAll dir
      -- Remark: fail if already exists
      -- (not part of POSIX, but supported on all our platforms)
      let h ← IO.FS.Handle.mk lockFile .writeNew
      h.putStrLn <| toString <| ← IO.Process.getPID
    catch
      | .alreadyExists .. => do
        if firstTime then
          let stderr ← IO.getStderr
          stderr.putStrLn s!"warning: waiting for prior `lake build` invocation to finish... (remove '{lockFile}' if stuck)"
          stderr.flush
        IO.sleep (ms := 300)
        busyLoop false
      | e => throw e

/-- Busy wait to acquire the lock of `lockFile`, run `act`, and then release the lock. -/
@[inline] def withLockFile [Monad m] [MonadFinally m] [MonadLiftT IO m] (lockFile : FilePath) (act : m α) : m α := do
  try
    busyAcquireLockFile lockFile; act
  finally show IO _ from do
    try
      IO.FS.removeFile lockFile
    catch
      | .noFileOrDirectory .. => IO.eprintln <|
        s!"warning: `{lockFile}` was deleted before the lock was released"
      | e => throw e
