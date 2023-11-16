/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Index

namespace Lake

def env (cmd : String) (args : Array String := #[]) : LakeT IO UInt32 := do
  IO.Process.spawn {cmd, args, env := ← getAugmentedEnv} >>= (·.wait)

def exe (name : Name) (args  : Array String := #[]) (buildConfig : BuildConfig := {}) : LakeT LogIO UInt32 := do
  let ws ← getWorkspace
  if let some exe := ws.findLeanExe? name then
    let exeFile ← ws.runBuild (exe.build >>= (·.await)) buildConfig
    env exeFile.toString args
  else
    error s!"unknown executable `{name}`"

def uploadRelease (pkg : Package) (tag : String) : LogIO Unit := do
  let mut args :=
    #["release", "upload", tag, pkg.buildArchiveFile.toString, "--clobber"]
  if let some repo := pkg.releaseRepo? then
    args := args.append #["-R", repo]
  tar pkg.buildArchive pkg.buildDir pkg.buildArchiveFile
  logInfo s!"Uploading {tag}/{pkg.buildArchive}"
  proc {cmd := "gh", args}
