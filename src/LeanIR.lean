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
import Lean.Compiler.IR.EmitC
import Lean.Language.Lean

open Lean

@[extern "lean_ir_export_entries"]
opaque exportIREntries (env : Environment) : Array (Name × Array EnvExtensionEntry)

def mkIRData (env : Environment) : IO ModuleData :=
  -- TODO: should we use a more specific/efficient data format for IR?
  return { env.header with
    entries := exportIREntries env ++ (← mkModuleData env .exported).entries
    constants := default
    constNames := default
    -- make sure to include all names in case only `.ir` is loaded
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
    IO.println s!"usage: leanir <setup.json> <module> <output.ir> <output.c> <-Dopt=val>..."
    return 1

  let setup ← ModuleSetup.load setupFile
  let mod := setup.name

  let mut opts := setup.options.toOptions
  for optArg in optArgs do
    opts ← setConfigOption opts optArg

  initSearchPathInternal
  -- Provide access to private scope of target module but no others; provide all IR
  let env ← profileitIO "import" opts <| withImporting do
    let imports := #[{ module := mod, importAll := true, isMeta := true }]
    let (_, s) ← importModulesCore (globalLevel := .exported) (arts := setup.importArts) imports |>.run
    let s := { s with moduleNameMap := s.moduleNameMap.modify mod fun m => if m.module == mod then { m with irPhases := .runtime } else { m with irPhases := .all } }
    finalizeImport (leakEnv := true) (loadExts := false) (level := .exported) s imports opts
  let env := env.setMainModule mod

  let is := Lean.Compiler.CSimp.ext.ext.toEnvExtension.getState env
  let newState ← Lean.Compiler.CSimp.ext.ext.addImportedFn is.importedEntries { env := env, opts := {} }
  let env := Lean.Compiler.CSimp.ext.ext.toEnvExtension.setState (asyncMode := .sync) env { is with state := newState }

  let is := Meta.instanceExtension.ext.toEnvExtension.getState env
  let newState ← Meta.instanceExtension.ext.addImportedFn is.importedEntries { env := env, opts := {} }
  let env := Meta.instanceExtension.ext.toEnvExtension.setState (asyncMode := .sync) env { is with state := newState }

  let is := classExtension.toEnvExtension.getState env
  let newState ← classExtension.addImportedFn is.importedEntries { env := env, opts := {} }
  let env := classExtension.toEnvExtension.setState (asyncMode := .sync) env { is with state := newState }

  let some modIdx := env.getModuleIdx? mod
    | throw <| IO.userError s!"module '{mod}' not found"

  let decls := postponedCompileDeclsExt.getModuleEntries env modIdx
  let env := postponedCompileDeclsExt.setState env (decls.foldl (fun s e => s.insert e.declName e) {})

  let decls := Compiler.LCNF.impureSigExt.getModuleEntries env modIdx
  let decls := decls.filter (isExtern env ·.name)
  let env := decls.foldl (fun env decl => Compiler.LCNF.impureSigExt.addEntry env decl) env
  let env := decls.foldl (fun env decl => Compiler.LCNF.setDeclPublic env decl.name) env

  -- Fill `declMapExt` with functions compiled already in `lean` so the set of "local" decls is
  -- unchanged and also for calculation of `extraConstNames` above
  -- TODO: do manually-added externs only as others need more state sync around ground exprs etc
  let is := Lean.IR.declMapExt.toEnvExtension.getState env
  let unbox : Name → Name
    | .str f "_boxed" => f
    | f => f
  let newState :=  is.importedEntries[modIdx]!.foldl (fun (decls, m) d => if isExtern env (unbox d.name) then (d::decls, m.insert d.name d) else (decls, m)) is.state
  let env := Lean.IR.declMapExt.toEnvExtension.setState (asyncMode := .sync) env { is with state := newState }

  let some mod := env.header.moduleData[modIdx]? | unreachable!
  -- Make sure we record the actual IR dependencies, not ourselves
  let env := { env with base.private.header.imports := mod.imports }
  let _ : MonadAlwaysExcept _ CoreM := inferInstance
  let res? ← EIO.toBaseIO <| Core.CoreM.run (ctx := { fileName := irFile, fileMap := default, options := opts })
      (s := { env }) try
    let decls := postponedCompileDeclsExt.getModuleEntries (← getEnv) modIdx
    modifyEnv (postponedCompileDeclsExt.setState · (decls.foldl (fun s e => s.insert e.declName e) {}))
    for decl in decls do
      if !(postponedCompileDeclsExt.getState (← getEnv) |>.contains decl.declName) then
        continue
      match (← getConstInfo decl.declName) with
      | .defnInfo info =>
        modifyEnv (postponedCompileDeclsExt.modifyState · fun s => info.all.foldl (·.erase) s)
        doCompile (logErrors := decl.logErrors) info.all.toArray
      | _ =>
        modifyEnv (postponedCompileDeclsExt.modifyState · fun s => s.erase decl.declName)
        doCompile (logErrors := decl.logErrors) #[decl.declName]
  catch e =>
    unless e.isInterrupt do
      logError e.toMessageData
  finally
    addTraceAsMessages

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
  let data ← IO.ofExcept <| IR.emitC env env.mainModule
  out.write data.toUTF8

  displayCumulativeProfilingTimes
  return 0
where doCompile logErrors decls := do
  let state ← Core.saveState
  try
    compileDeclsImpl decls
  catch e =>
    state.restore
    if logErrors then
      throw e
