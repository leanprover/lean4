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

public def main (args : List String) : IO UInt32 := do
  let [setupFile, mod, irFile] := args | do
    IO.println s!"usage: leanir <setup.json> <module> <output.ir>"
    return 1

  let mod := mod.toName
  let setup ← ModuleSetup.load setupFile
  initSearchPathInternal
  -- Provide access to private scope of target module but no others; provide all IR
  let env ← withImporting do
    let imports := #[{ module := mod, importAll := true, isMeta := true }]
    let (_, s) ← importModulesCore (globalLevel := .exported) (arts := setup.importArts) imports |>.run
    let s := { s with moduleNameMap := s.moduleNameMap.modify mod fun mod => { mod with irPhases := .runtime } }
    finalizeImport (leakEnv := true) (loadExts := true /-TODO?-/) (level := .exported)
      s imports setup.options.toOptions
  let some modIdx := env.getModuleIdx? mod
    | throw <| IO.userError s!"module '{mod}' not found"
  let some mod := env.header.moduleData[modIdx]? | unreachable!
  -- Make sure we record the actual IR dependencies, not ourselves
  let env := { env with base.private.header.imports := mod.imports }
  let res? ← EIO.toBaseIO <| Core.CoreM.run (ctx := { fileName := irFile, fileMap := default, options := setup.options.toOptions })
      (s := { env }) try
    let decls := postponedCompileDeclsExt.getModuleEntries env modIdx
    modifyEnv (postponedCompileDeclsExt.setState · (decls.foldl (·.insert) {}))
    withOptions (Compiler.compiler.checkMeta.set · false) do
    --withOptions (·.set `trace.Compiler true) do
    --withOptions (·.set `trace.compiler.ir true) do
    for decl in decls do
      match (← getConstInfo decl) with
      | .defnInfo info =>
        modifyEnv (postponedCompileDeclsExt.modifyState · fun s => info.all.foldl (·.erase) s)
        compileDeclsImpl info.all.toArray
      | _ =>
        modifyEnv (postponedCompileDeclsExt.modifyState · fun s => s.erase decl)
        compileDeclsImpl #[decl]
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
  return 0
