/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Lake.Config.Workspace
import Lake.Config.Module
import Lake.Util.IO
import Lake.Build.Common

namespace Lake
open Lean System

abbrev CacheMove := FilePath × FilePath

def isModulePath : Name → Bool
  | .str p s =>
    !s.isEmpty && s != "." && s != ".." &&
    !s.contains '/' && !s.contains '\\' && !s.contains ':' &&
    (p.isAnonymous || isModulePath p)
  | _ => false

/-- Validate the entire batch before installing any of its outputs. -/
def planCacheUnpack
  (pkg : Package) (stage : FilePath) (entries : Array (Hash × ArtifactDescr))
: ExceptT String IO (Array CacheMove × Array (Module × ArtifactDescr)) := do
  let mut seen : Std.HashSet Name := {}
  let mut moves := #[]
  let mut installed := #[]
  for (hash, descr) in entries do
    let dir := stage / hash.hex
    let files ← (dir / "lib").readDir
    let ileans := files.filter (·.fileName.endsWith ".ilean")
    unless ileans.size == 1 do
      throw "archive does not contain exactly one .ilean file"
    let some ilean := ileans[0]? | throw "missing .ilean file"
    let info ← IO.FS.readFile ilean.path
    let info ← liftExcept (Json.parse info)
    let name ← liftExcept (info.getObjValAs? Name "module")
    if seen.contains name then throw s!"overlapping archives for module {name}"
    seen := seen.insert name
    unless isModulePath name do throw "unsupported module path"
    let some mod := pkg.findModule? name | continue
    -- A deleted source must not become importable through its old archive.
    unless (← mod.leanFile.pathExists) do continue
    installed := installed.push (mod, descr)
    unless ilean.fileName == mod.fileName "ilean" do
      throw "archive basename disagrees with its module name"
    for (subdir, dest, exts) in #[
      ("lib", mod.leanLibDir, #["trace", "olean", "olean.server", "olean.private", "ilean", "ir", "ir.sig"]),
      ("ir", mod.irDir, #["c", "bc"])
    ] do
      for file in (← (dir / subdir).readDir) do
        unless (← file.path.symlinkMetadata).type == .file &&
            exts.any (mod.fileName · == file.fileName) do
          throw s!"unexpected archive output: {file.path}"
        moves := moves.push (file.path, dest / file.fileName)
  return (moves, installed)

/--
Prepare downloaded module archives in one `leantar` invocation. This only handles
a fresh build directory and nonoverlapping module bundles; other cases retain
ordinary, on-demand restoration. A subsequent build still validates all inputs.
-/
public def Package.unpackCache
  (pkg : Package) (cache : Cache) (map : CacheMap) (leantar : FilePath)
: LogIO Unit := do
  let entries := map.toArray.filterMap fun (hash, entry) => do
    let .ok descr := fromJson? (α := ArtifactDescr) entry.out | none
    if descr.ext == "ltar" then some (hash, descr) else none
  if entries.isEmpty then return
  -- Claim a fresh build directory. Staging inside it keeps renames on the
  -- same file system and lets `lake clean` reclaim an interrupted extraction.
  createParentDirs pkg.buildDir
  match (← IO.FS.createDir pkg.buildDir |>.toBaseIO) with
  | .ok _ => pure ()
  | .error (.alreadyExists ..) =>
    logInfo s!"{pkg.prettyName}: skipping bulk unpack (build directory already exists)"
    return
  | .error e => error s!"{pkg.prettyName}: cannot create build directory: {e}"
  let stage := pkg.buildDir / ".lake-unpack"
  try
    IO.FS.createDir stage
    -- Bundles store basenames, so isolate them until their .ilean identifies
    -- the full module name. The archive format and remote cache are unchanged.
    let input := Json.arr <| entries.map fun (hash, descr) => Json.mkObj [
      ("file", toJson (cache.artifactDir / descr.relPath).toString),
      ("hash", toJson hash.hex),
      ("base", toJson #[(stage / hash.hex / "lib").toString, (stage / hash.hex / "ir").toString])
    ]
    let plan ← (show IO (Except String (Array CacheMove × Array (Module × ArtifactDescr))) from do
      try
        let out ← IO.Process.output {cmd := leantar.toString, args := #["-x", "-j", "-"]} input.compress
        if out.exitCode != 0 then
          return .error s!"leantar exited with code {out.exitCode}: {out.stderr.trimAscii}"
        planCacheUnpack pkg stage entries |>.run
      catch e => return .error e.toString)
    let (moves, installed) ← match plan with
      | .ok moves => pure moves
      | .error msg =>
        logInfo s!"{pkg.prettyName}: skipping bulk unpack: {msg}"
        return
    let mut dirs : Std.HashSet FilePath := {}
    for (src, dst) in moves do
      if let some dir := dst.parent then
        unless dirs.contains dir do
          IO.FS.createDirAll dir
          dirs := dirs.insert dir
      IO.FS.rename src dst
    for (mod, descr) in installed do
      let path := cache.artifactDir / descr.relPath
      discard <| restoreArtifact mod.ltarFile {descr, path, mtime := ← getMTime path}
    logInfo s!"{pkg.prettyName}: bulk unpacked {installed.size} module archives"
  finally
    removeDirAllIfExists stage
    -- Only remove an empty directory after a skipped batch, never other outputs.
    discard <| IO.FS.removeDir pkg.buildDir |>.toBaseIO
