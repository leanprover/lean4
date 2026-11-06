/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.System.IO
import Init.System.Platform

open System

set_option doc.verso true

namespace Lake

/-- Creates any missing parent directories of {lean}`path`. -/
public def createParentDirs (path : FilePath) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir

/-- Remove the file at {lean}`path` if it exists. -/
public def removeFileIfExists (path : FilePath) : IO Unit := do
  try IO.FS.removeFile path catch
    | .noFileOrDirectory .. => pure ()
    | e => throw e

/-- Reserve a unique temporary pathname beside {lean}`path`. The caller owns its removal. -/
public partial def createTempFileFor (path : FilePath) : IO FilePath := do
  createParentDirs path
  let pid ← IO.Process.getPID
  let nonce ← IO.monoNanosNow
  let tmp := path.parent.getD "." / (".lake-cache-" ++ toString pid ++ "-" ++ toString nonce ++ ".tmp")
  try
    discard <| IO.FS.Handle.mk tmp .writeNew
    return tmp
  catch
    | .alreadyExists .. => createTempFileFor path
    | e => throw e

/-- Run an action with a unique temporary file on the destination filesystem. -/
public def withTempFileFor
  [Monad m] [MonadFinally m] [MonadLiftT IO m]
  (path : FilePath) (f : FilePath → m α)
: m α := do
  let tmp ← createTempFileFor path
  try f tmp finally removeFileIfExists tmp

/-- Publish a completed file, keeping any winner already at the destination. -/
public def publishFileIfNew (tmp path : FilePath) : IO Unit := do
  try IO.FS.hardLink tmp path catch
    | .alreadyExists .. => pure ()
    | _ =>
      try IO.FS.renameIfNew tmp path catch e =>
        unless (← path.pathExists) do throw e

/-- Publish a completed temporary file, replacing the destination. -/
public def replaceFile (tmp path : FilePath) : IO Unit := do
  try IO.FS.rename tmp path catch e =>
    if System.Platform.isWindows then
      -- Windows cannot rename over a read-only cache entry. A missing entry is recoverable.
      removeFileIfExists path
      IO.FS.rename tmp path
    else throw e

/-- Publish complete bytes, or preserve an existing winner. Replacement is atomic on POSIX. -/
public def writeBinFileAtomic
  (path : FilePath) (contents : ByteArray) (overwrite := true) (readOnly exe := false)
: IO Unit :=
  withTempFileFor path fun tmp => do
    IO.FS.writeBinFile tmp contents
    if readOnly then
      let rights := {read := true, write := false, execution := exe}
      IO.setAccessRights tmp ⟨rights, rights, rights⟩
    if overwrite then replaceFile tmp path else publishFileIfNew tmp path

/-- Atomically replace a UTF-8 file, or preserve an existing winner. -/
public def writeFileAtomic (path : FilePath) (contents : String) (overwrite := true) (readOnly := false) : IO Unit :=
  writeBinFileAtomic path contents.toUTF8 overwrite readOnly

/--
Write the UTF-8 encoded string {lean}`content` to {lean}`path`.
If the file already exists, does nothing.
-/
public def writeFileIfNew (path : FilePath) (content : String) : IO Unit := do
  let h ← try IO.FS.Handle.mk path IO.FS.Mode.writeNew catch
    | .alreadyExists .. => return
    | e => throw e
  h.putStr content

/--
Write the bytes of {lean}`content` to {lean}`path`.
If the file already exists, does nothing.
-/
public def writeBinFileIfNew (path : FilePath) (content : ByteArray) : IO Unit := do
  let h ← try IO.FS.Handle.mk path IO.FS.Mode.writeNew catch
    | .alreadyExists .. => return
    | e => throw e
  h.write content

/--
Remove a directory and all its contents.
Like {lean}`IO.FS.removeDirAll`, but does not fail if {lean}`path` does not exist
or if a file is first deleted by a racing process.
-/
public partial def removeDirAllIfExists (path : FilePath) : IO Unit := do
  let ents ← try path.readDir catch
    | .noFileOrDirectory .. => return -- path did not exist or something else was faster
    | e => throw e
  for ent in ents do
    -- Do not follow symlinks
    let mdata ← try ent.path.symlinkMetadata catch
      | .noFileOrDirectory .. => continue -- something else was faster
      | e => throw e
    if mdata.type == .dir then
      removeDirAllIfExists ent.path
    else
      removeFileIfExists ent.path
  try IO.FS.removeDir path catch
    | .noFileOrDirectory .. => return -- something else was faster
    | e => throw e

/-- Copy a file from {lean}`src` to {lean}`dst`. -/
public def copyFile (src dst : FilePath) : IO Unit := do
  let contents ← IO.FS.readBinFile src
  IO.FS.writeBinFile dst contents

/-- Copy a directory and all its contents from {lean}`src` to {lean}`dst`. -/
public partial def copyDirAll (src dst : FilePath) : IO Unit := do
  IO.FS.createDirAll dst
  let ents ← src.readDir
  for ent in ents do
    let srcPath := src / ent.fileName
    let dstPath := dst / ent.fileName
    if (← srcPath.isDir) then
      copyDirAll srcPath dstPath
    else
      copyFile srcPath dstPath

/-- Returns the normalized real path of a file if it exists. Otherwise, returns {lean}`""`. -/
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
