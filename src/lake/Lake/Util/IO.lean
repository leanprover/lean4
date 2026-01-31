/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.System.IO

open System

namespace Lake

/-- Creates any missing parent directories of `path`. -/
public def createParentDirs (path : FilePath) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir

/--
Remove the file at `path`.
Also removes read-only files on Windows, unlike `IO.FS.removeFile`.
-/
def removeFile (path : FilePath) : IO Unit := do
  try IO.FS.removeFile path catch
    | e@(.permissionDenied ..) =>
      if Platform.isWindows then
        let rw := {read := true, write := true}
        IO.setAccessRights path ⟨rw, rw, rw⟩
        IO.FS.removeFile path
      else throw e
    | e => throw e

/-- Remove the file at `path` if it exists. -/
public def removeFileIfExists (path : FilePath) : IO Unit := do
  try removeFile path catch
    | .noFileOrDirectory .. => pure ()
    | e => throw e

/-- Copy a file from `src` to `dst`. -/
public def copyFile (src dst : FilePath) : IO Unit := do
  let contents ← IO.FS.readBinFile src
  IO.FS.writeBinFile dst contents

/-- Returns the normalized real path of a file if it exists. Otherwise, returns `""`. -/
public def resolvePath (path : FilePath) : BaseIO FilePath := do
  match (← (IO.FS.realPath path).toBaseIO) with
  | .ok path =>
    -- Real path does not guarantee the file exists on Windows
    if (← path.pathExists) then
      return path.normalize
    else
      return ""
  | _ =>
    return ""

/-- Returns the normalized real path of a file if and only if it exists. -/
@[inline] public def resolvePath? (path : FilePath) : BaseIO (Option FilePath) := do
  let path ← resolvePath path
  return if path.toString.isEmpty then none else some path
