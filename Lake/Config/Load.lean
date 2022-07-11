/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Elab.Frontend
import Lake.DSL.Attributes
import Lake.DSL.Extensions
import Lake.Config.FacetConfig
import Lake.Config.TargetConfig

namespace Lake
open Lean System

/-- Main module `Name` of a Lake configuration file. -/
def configModuleName : Name := `lakefile

/-- The default name of the Lake configuration file (i.e., `lakefile.lean`). -/
def defaultConfigFile : FilePath := "lakefile.lean"

deriving instance BEq, Hashable for Import

/- Cache for the imported header environment of Lake configuration files. -/
initialize importEnvCache : IO.Ref (Std.HashMap (List Import) Environment) ← IO.mkRef {}

/-- Like `Lean.Elab.processHeader`, but using `importEnvCache`. -/
def processHeader (header : Syntax) (opts : Options) (trustLevel : UInt32)
(inputCtx : Parser.InputContext) : StateT MessageLog IO Environment := do
  try
    let imports := Elab.headerToImports header
    if let some env := (← importEnvCache.get).find? imports then
      return env
    let env ← importModules imports opts trustLevel
    importEnvCache.modify (·.insert imports env)
    return env
  catch e =>
    let pos := inputCtx.fileMap.toPosition <| header.getPos?.getD 0
    modify (·.add { fileName := inputCtx.fileName, data := toString e, pos })
    mkEmptyEnvironment

/-- Like `Lean.Environment.evalConstCheck` but with plain universe-polymorphic `Except`. -/
unsafe def evalConstCheck (α) (env : Environment) (opts : Options) (type : Name) (const : Name) : Except String α :=
  match env.find? const with
  | none => throw s!"unknown constant '{const}'"
  | some info =>
    match info.type with
    | Expr.const c _ =>
      if c != type then
        throwUnexpectedType
      else
        env.evalConst α opts const
    | _ => throwUnexpectedType
where
  throwUnexpectedType : Except String α :=
    throw s!"unexpected type at '{const}', `{type}` expected"

namespace Package

/-- Unsafe implementation of `load`. -/
unsafe def loadUnsafe (dir : FilePath) (configOpts : NameMap String)
(configFile := dir / defaultConfigFile) (leanOpts := Options.empty)
: LogIO Package := do

  -- Read File & Initialize Environment
  let input ← IO.FS.readFile configFile
  let inputCtx := Parser.mkInputContext input configFile.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header leanOpts 1024 inputCtx messages
  let env := env.setMainModule configModuleName

  -- Configure Extensions
  let env := dirExt.setState env dir
  let env := optsExt.setState env configOpts

  -- Elaborate File
  let commandState := Elab.Command.mkState env messages leanOpts
  let s ← Elab.IO.processCommands inputCtx parserState commandState
  for msg in s.commandState.messages.toList do
    match msg.severity with
    | MessageSeverity.information => logInfo (← msg.toString)
    | MessageSeverity.warning     => logWarning (← msg.toString)
    | MessageSeverity.error       => logError (← msg.toString)

   -- Extract Configuration
  if s.commandState.messages.hasErrors then
    error s!"package configuration `{configFile}` has errors"

  -- Load Package Configuration
  let env := s.commandState.env
  let pkgDeclName ←
    match packageAttr.ext.getState env |>.toList with
    | [] => error s!"configuration file is missing a `package` declaration"
    | [name] => pure name
    | _ => error s!"configuration file has multiple `package` declarations"
  let config ← IO.ofExcept <|
    evalConstCheck PackageConfig env leanOpts ``PackageConfig pkgDeclName
  if config.extraDepTarget.isSome then
    logWarning <| "`extraDepTarget` has been deprecated. " ++
      "Try to use a custom target or raise an issue about your use case."

  -- Tag Load Helpers
  let mkTagMap {α} (attr) (f : Name → IO α) : IO (NameMap α) :=
    attr.ext.getState env |>.foldM (init := {}) fun map declName =>
      return map.insert declName <| ← f declName
  let mkDTagMap {β} (attr : TagAttribute) (f : (n : Name) → IO (β n)) : IO (DNameMap β) :=
    attr.ext.getState env |>.foldM (init := {}) fun map declName =>
      return map.insert declName <| ← f declName
  let evalConst (α typeName declName) : IO α :=
    IO.ofExcept (evalConstCheck α env leanOpts typeName declName)
  let evalConstMap {α β} (f : α → β) (declName) : IO β :=
    match env.evalConst α leanOpts declName with
    | .ok a => pure <| f a
    | .error e => throw <| IO.userError e

  -- Load Dependency, Script, Facet, & Target Configurations
  let dependencies ←
    packageDepAttr.ext.getState env |>.foldM (init := #[]) fun arr name => do
      return arr.push <| ← evalConst Dependency ``Dependency name
  let scripts ← mkTagMap scriptAttr fun declName => do
    let fn ← IO.ofExcept <| evalConstCheck ScriptFn env leanOpts ``ScriptFn declName
    return {fn, doc? := (← findDocString? env declName)}
  let leanLibConfigs ← mkTagMap leanLibAttr
    (evalConst LeanLibConfig ``LeanLibConfig)
  let leanExeConfigs ← mkTagMap leanExeAttr
    (evalConst LeanExeConfig ``LeanExeConfig)
  let externLibConfigs ← mkTagMap externLibAttr
    (evalConst ExternLibConfig ``ExternLibConfig)
  let opaqueModuleFacetConfigs ← mkDTagMap moduleFacetAttr fun name => do
    match evalConstCheck ModuleFacetDecl env leanOpts ``ModuleFacetDecl name with
    | .ok decl =>
      if h : name = decl.name then
        return OpaqueModuleFacetConfig.mk (h ▸ decl.config)
      else
        error s!"Facet was defined as `{decl.name}`, but was registered as `{name}`"
    | .error e => throw <| IO.userError e
  let opaquePackageFacetConfigs ← mkDTagMap packageFacetAttr fun name => do
    match evalConstCheck PackageFacetDecl env leanOpts ``PackageFacetDecl name with
    | .ok decl =>
      if h : name = decl.name then
        return OpaquePackageFacetConfig.mk (h ▸ decl.config)
      else
        error s!"Facet was defined as `{decl.name}`, but was registered as `{name}`"
    | .error e => throw <| IO.userError e
  let opaqueTargetConfigs ← mkTagMap targetAttr
    (evalConstMap OpaqueTargetConfig.mk)
  let defaultTargets :=
    defaultTargetAttr.ext.getState env |>.fold (init := #[]) fun arr name =>
      arr.push name

  -- Construct the Package
  if leanLibConfigs.isEmpty && leanExeConfigs.isEmpty && config.defaultFacet ≠ .none then
    logWarning <| "Package targets are deprecated. " ++
      "Add a `lean_exe` and/or `lean_lib` default target to the package instead."
  return {
    dir, config, scripts, dependencies,
    leanLibConfigs, leanExeConfigs, externLibConfigs,
    opaqueModuleFacetConfigs, opaquePackageFacetConfigs, opaqueTargetConfigs,
    defaultTargets
  }


/--
Load the package located in
the given directory with the given configuration file.
-/
@[implementedBy loadUnsafe]
opaque load (dir : FilePath) (configOpts : NameMap String)
(configFile := dir / defaultConfigFile) (leanOpts := Options.empty)  : LogIO Package
