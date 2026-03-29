/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

import Lean.CoreM
import Lean.Util.ForEachExpr
import all Lean.Util.Path
import all Lean.Environment
import Lean.Compiler.Options
import Lean.Compiler.IR.CompilerM

import all Lean.Compiler.CSimpAttr
import Lean.Compiler.LCNF.EmitC
import Lean.Language.Lean
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.Main

/-! Lean codegen as a separate process. -/

open Lean Compiler LCNF

def mkIRData (env : Environment) : IO ModuleData := do
  -- TODO: should we use a more specific/efficient data format for IR?

  -- `exportIREntries` provides full IR for `declMapExt` and `regularInitAttr`; filter them from
  -- `mkModuleData` to prevent the latter's opaque-extern entries from overwriting the full IR
  -- in `setImportedEntries`
  let irEntries := exportIREntries env
  let irExtNames := irEntries.map (·.1)
  let modEntries := (← mkModuleData env .private).entries.filter (!irExtNames.contains ·.1)
  return { env.header with
    entries := irEntries ++ modEntries
    constants := default
    constNames := default
    -- make sure to include all names in case only `.ir` is loaded
    -- TODO: `.private` because `import all` may require otherwise unreachable IR entries
    extraConstNames := getIRExtraConstNames env .private (includeDecls := true)
  }

def setConfigOption (opts : Options) (arg : String) : IO Options := do
  if !arg.startsWith "-D" then
    throw <| .userError s!"invalid trailing argument `{arg}`, expected argument of the form `-Dopt=val`"
  let arg := arg.drop "-D".length
  let pos := arg.find '='
  if h : pos.IsAtEnd then
    throw <| .userError "invalid -D parameter, argument must contain '='"
  else
    let name := arg.sliceTo pos |>.toName
    let val := arg.sliceFrom (pos.next h) |>.copy
    if let some decl := (← getOptionDecls).find? name then
      Language.Lean.setOption opts decl name val
    else
      throw <| .userError s!"unknown option '{name}'"

public def main (args : List String) : IO UInt32 := do
  let setupFile::irFile::c::optArgs := args | do
    IO.println s!"usage: leanir <setup.json> <output.ir> <output.c> [--stat] <-Dopt=val>..."
    return 1

  let setup ← ModuleSetup.load setupFile
  let modName := setup.name

  let mut printStats := false
  let mut opts := setup.options.toOptions
  for optArg in optArgs do
    if optArg == "--stat" then
      printStats := true
    else
      opts ← setConfigOption opts optArg
  opts := Compiler.compiler.inLeanIR.set opts true
  opts := maxHeartbeats.set opts 0

  --initSearchPathInternal  -- TODO
  initSearchPath (← getBuildDir)
  -- Provide access to private scope of target module but no others; provide all IR
  let env ← profileitIO "import" opts <| withImporting do
    let imports := #[{ module := modName, importAll := true, isMeta := true }]
    -- `private` because inlining may make ext data from private imports transitively required
    -- no `arts` yet because they are for `exported`
    let (_, s) ← importModulesCore (globalLevel := .private) /-(arts := setup.importArts)-/ imports |>.run
    let s := { s with moduleNameMap := s.moduleNameMap.modify modName fun m => if m.module == modName then { m with irPhases := .runtime } else { m with irPhases := .all } }
    -- level exported because otherwise we would try to load the current module's `.ir`
    finalizeImport (leakEnv := true) (loadExts := false) (level := .exported) s imports opts
  let env := env.setMainModule modName

  let initExt {α β σ} [Inhabited σ] (ext : PersistentEnvExtension α β σ) (env : Environment) : IO Environment := do
    let s := ext.toEnvExtension.getState env
    let newState ← ext.addImportedFn s.importedEntries { env := env, opts := {} }
    return ext.toEnvExtension.setState (asyncMode := .sync) env { s with state := newState }

  let env ← initExt Lean.Compiler.CSimp.ext.ext env
  let env ← initExt Meta.instanceExtension.ext env
  let env ← initExt classExtension env
  let env ← initExt Meta.Match.Extension.extension env

  let some modIdx := env.getModuleIdx? modName
    | throw <| IO.userError s!"module '{modName}' not found"

  let decls := impureSigExt.getModuleEntries env modIdx
  let decls := decls.filter (isExtern env ·.name)
  let env := decls.foldl (fun env decl => impureSigExt.addEntry env decl) env
  let env := decls.foldl (fun env decl => setDeclPublic env decl.name) env

  -- Fill `declMapExt` with functions compiled already in `lean` so the set of "local" decls is
  -- unchanged and also for calculation of `extraConstNames` above
  -- TODO: we do manually-added externs only as others need more state sync around ground exprs etc
  let is := Lean.IR.declMapExt.toEnvExtension.getState env
  let unbox : Name → Name
    | .str f "_boxed" => f
    | f => f
  let newState :=  is.importedEntries[modIdx]!.foldl (fun (decls, m) d => if isExtern env (unbox d.name) then (d::decls, m.insert d.name d) else (decls, m)) is.state
  let env := Lean.IR.declMapExt.toEnvExtension.setState (asyncMode := .sync) env { is with state := newState }

  let some mod := env.header.moduleData[modIdx]? | unreachable!
  -- Make sure we record the actual IR dependencies, not ourselves
  let env := { env with base.private.header.imports := mod.imports }
  let _ : MonadExceptOf _ CoreM := MonadAlwaysExcept.except
  let res? ← EIO.toBaseIO <| Core.CoreM.run (ctx := { fileName := irFile, fileMap := default, options := opts })
      (s := { env }) try
    let decls := postponedCompileDeclsExt.getModuleEntries env modIdx
    -- Load postponed decls and iterate over them, removing each entry to avoid infinite recursion.
    -- NOTE: `decls` is in the original order of declarations so initializing and managing the
    -- extension would not be necessary for that, we could just leave it empty. However, there are
    -- cases like a `[csimp]` replacement being defined below the original function in the same file
    -- where allowing `LCNF.main` to reorder compilation based on dependencies seems to be the
    -- simpler solution (as we may make the csimp replacement before the replacement has been
    -- compiled).
    modifyEnv (postponedCompileDeclsExt.setState · (decls.foldl (fun s e => e.declNames.foldl (·.insert · e) s) {}))
    for decl in decls do
      for decl in decl.declNames do
        try
          resumeCompilation decl (← getOptions)
        finally
          addTraceAsMessages
      for msg in (← Core.getAndEmptyMessageLog).unreported do
        IO.eprintln (← msg.toString)
  catch e =>
    unless e.isInterrupt do
      logError e.toMessageData

  let .ok (_, s) := res? | unreachable!
  let env := s.env

  for msg in s.messages.unreported do
    IO.eprintln (← msg.toString)

  if s.messages.hasErrors then
   return 1

  -- Make sure to change the module name so we derive a different base address
  saveModuleData irFile (env.mainModule ++ `ir) (← mkIRData env)

  let .ok out ← IO.FS.Handle.mk c .write |>.toBaseIO
    | IO.eprintln s!"failed to create '{c}'"
      return 1
  profileitIO "C code generation" opts do
    let data ← Compiler.LCNF.emitC modName
      |>.toIO' { fileName := irFile, fileMap := default } { env }
    out.write data.toUTF8

  displayCumulativeProfilingTimes
  if printStats then
    env.displayStats
  return 0
