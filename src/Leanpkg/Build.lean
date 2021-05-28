/-
Copyright (c) 2021 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Lean.Data.Name
import Lean.Elab.Import
import Leanpkg.Proc

open Lean
open System

namespace Leanpkg.Build

def buildPath : FilePath := "build"
def tempBuildPath := buildPath / "temp"

structure Context where
  pkg      : Name
  leanArgs : List String
  leanPath : String
  parents  : List Name := []

structure Result where
  maxMTime : IO.FS.SystemTime
  task     : Task (Except IO.Error Unit)
  deriving Inhabited

structure State where
  modTasks : NameMap Result := ∅

abbrev BuildM := ReaderT Context <| StateT State IO

partial def buildModule (mod : Name) : BuildM Result := do
  let ctx ← read
  if ctx.parents.contains mod then
    -- cyclic import
    let cycle := ctx.parents.dropWhile (· != mod) ++ [mod]
    let cycle := cycle.reverse.map (s!"  {·}")
    throw <| IO.userError s!"import cycle detected:\n{"\n".intercalate cycle}"

  if let some r := (← get).modTasks.find? mod then
    -- already visited
    return r

  let leanFile := modToFilePath "." mod "lean"
  let leanMData ← leanFile.metadata

  -- recursively build dependencies and calculate transitive `maxMTime`
  let (imports, _, _) ← Elab.parseImports (← IO.FS.readFile leanFile) leanFile.toString
  let mut deps := #[]
  let mut maxMTime := leanMData.modified
  for i in imports do
    if i.module.getRoot == ctx.pkg then
      let dep ← withReader (fun ctx => { ctx with parents := mod :: ctx.parents }) do
        buildModule i.module
      if dep.maxMTime > maxMTime then
        maxMTime := dep.maxMTime
      deps := deps.push dep

  -- check whether we have an up-to-date .olean
  let oleanFile := modToFilePath buildPath mod "olean"
  try
    if (← oleanFile.metadata).modified >= maxMTime then
      let r := { maxMTime, task := Task.pure (Except.ok ()) }
      modify fun st => { st with modTasks := st.modTasks.insert mod r }
      return r
  catch
    | IO.Error.noFileOrDirectory .. => pure ()
    | e                             => throw e

  let task ← IO.mapTasks (tasks := deps.map (·.task) |>.toList) fun rs => do
    if let some e := rs.findSome? (fun | Except.error e => some e | Except.ok _ => none) then
      -- propagate failure
      throw e
    try
      let cFile := modToFilePath tempBuildPath mod "c"
      IO.createDirAll oleanFile.parent.get!
      IO.createDirAll cFile.parent.get!
      execCmd {
        cmd := (← IO.appDir) / "lean" |>.withExtension FilePath.exeExtension |>.toString
        args := ctx.leanArgs.toArray ++ #["-o", oleanFile.toString, "-c", cFile.toString, leanFile.toString]
        env := #[("LEAN_PATH", ctx.leanPath)]
      }
    catch e =>
      -- print errors early
      IO.eprintln e
      throw e

  let r := { maxMTime, task := task }
  modify fun st => { st with modTasks := st.modTasks.insert mod r }
  return r

def buildModules (pkg : Name) (mods : List Name) (leanArgs : List String) (leanPath : String) : IO Unit := do
  let rs ← mods.mapM buildModule |>.run { pkg, leanArgs, leanPath } |>.run' {}
  for r in rs do
    if let Except.error _ ← IO.wait r.task then
      -- actual error has already been printed above
      throw <| IO.userError "Build failed."

end Leanpkg.Build
