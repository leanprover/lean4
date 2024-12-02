/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.DSL.Attributes
import Lake.Config.Workspace
import Lean.DocString

/-! # Lean Configuration Evaluator

This module contains the definitions to load Lake configuration objects from
a Lean environment elaborated from a Lake configuration file.
-/

open System Lean

namespace Lake

/-- Unsafe implementation of `evalConstCheck`. -/
unsafe def unsafeEvalConstCheck (env : Environment) (opts : Options) (α) (type : Name) (const : Name) : Except String α :=
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

/-- Like `Lean.Environment.evalConstCheck`, but with plain universe-polymorphic `Except`. -/
@[implemented_by unsafeEvalConstCheck] opaque evalConstCheck
(env : Environment) (opts : Options) (α) (type : Name) (const : Name) : Except String α

/-- Construct a `DNameMap` from the declarations tagged with `attr`. -/
def mkTagMap
(env : Environment) (attr : OrderedTagAttribute)
[Monad m] (f : (n : Name) → m (β n)) : m (DNameMap β) :=
  let entries := attr.getAllEntries env
  entries.foldlM (init := {}) fun map declName =>
    return map.insert declName <| ← f declName

/-- Construct a `OrdNameMap` from the declarations tagged with `attr`. -/
def mkOrdTagMap
(env : Environment) (attr : OrderedTagAttribute)
[Monad m] (f : (n : Name) → m β) : m (OrdNameMap β) :=
  let entries := attr.getAllEntries env
  entries.foldlM (init := .mkEmpty entries.size) fun map declName =>
    return map.insert declName <| ← f declName

/-- Load a `PackageConfig` from a configuration environment. -/
def PackageConfig.loadFromEnv
(env : Environment) (opts := Options.empty) : Except String PackageConfig := do
  let declName ←
    match packageAttr.getAllEntries env |>.toList with
    | [] => error s!"configuration file is missing a `package` declaration"
    | [name] => pure name
    | _ => error s!"configuration file has multiple `package` declarations"
  evalConstCheck env opts _  ``PackageConfig declName

/--
Load the optional elements of a `Package` from the Lean environment.
This is done after loading its core configuration but before resolving
its dependencies.
-/
def Package.loadFromEnv
  (self : Package) (env : Environment) (opts : Options)
: LogIO Package := do
  let strName := self.name.toString (escape := false)

  -- Load Script, Facet, Target, and Hook Configurations
  let scripts ← mkTagMap env scriptAttr fun scriptName => do
    let name := strName ++ "/" ++ scriptName.toString (escape := false)
    let fn ← IO.ofExcept <| evalConstCheck env opts ScriptFn ``ScriptFn scriptName
    return {name, fn, doc? := ← findDocString? env scriptName : Script}
  let defaultScripts ← defaultScriptAttr.getAllEntries env |>.mapM fun name =>
    if let some script := scripts.find? name then pure script else
      error s!"package is missing script `{name}` marked as a default"
  let leanLibConfigs ← IO.ofExcept <| mkOrdTagMap env leanLibAttr fun name =>
    evalConstCheck env opts LeanLibConfig ``LeanLibConfig name
  let leanExeConfigs ← IO.ofExcept <| mkOrdTagMap env leanExeAttr fun name =>
    evalConstCheck env opts LeanExeConfig ``LeanExeConfig name
  let externLibConfigs ← mkTagMap env externLibAttr fun name =>
    match evalConstCheck env opts ExternLibDecl ``ExternLibDecl name with
    | .ok decl =>
      if h : decl.pkg = self.config.name ∧ decl.name = name then
        return h.1 ▸ h.2 ▸ decl.config
      else
        error s!"target was defined as `{decl.pkg}/{decl.name}`, but was registered as `{self.name}/{name}`"
    | .error e => error e
  let opaqueTargetConfigs ← mkTagMap env targetAttr fun name =>
    match evalConstCheck env opts TargetDecl ``TargetDecl name with
    | .ok decl =>
      if h : decl.pkg = self.config.name ∧ decl.name = name then
        return OpaqueTargetConfig.mk <| h.1 ▸ h.2 ▸ decl.config
      else
        error s!"target was defined as `{decl.pkg}/{decl.name}`, but was registered as `{self.name}/{name}`"
    | .error e => error e
  let defaultTargets := defaultTargetAttr.getAllEntries env
  let postUpdateHooks ← postUpdateAttr.getAllEntries env |>.mapM fun name =>
    match evalConstCheck env opts PostUpdateHookDecl ``PostUpdateHookDecl name with
    | .ok decl =>
      if h : decl.pkg = self.config.name then
        return OpaquePostUpdateHook.mk ⟨h ▸ decl.fn⟩
      else
        error s!"post-update hook was defined in `{decl.pkg}`, but was registered in `{self.name}`"
    | .error e => error e
  let depConfigs ← IO.ofExcept <| packageDepAttr.getAllEntries env |>.mapM fun name =>
    evalConstCheck env opts Dependency ``Dependency name
  let testDrivers := testDriverAttr.getAllEntries env
  let testDriver ←
    if testDrivers.size > 1 then
      error s!"{self.name}: only one script, executable, or library can be tagged @[test_driver]"
    else if h : testDrivers.size > 0 then
      if self.config.testDriver.isEmpty then
        pure (testDrivers[0]'h |>.toString)
      else
        error s!"{self.name}: cannot both set testDriver and use @[test_driver]"
    else
      pure self.config.testDriver
  let lintDrivers := lintDriverAttr.getAllEntries env
  let lintDriver ←
    if lintDrivers.size > 1 then
      error s!"{self.name}: only one script or executable can be tagged @[linter]"
    else if h : lintDrivers.size > 0 then
      if self.config.lintDriver.isEmpty then
        pure (lintDrivers[0]'h |>.toString)
      else
        error s!"{self.name}: cannot both set linter and use @[linter]"
    else
      pure self.config.lintDriver

  -- Deprecation warnings
  unless self.config.manifestFile.isNone do
    logWarning s!"{self.name}: package configuration option `manifestFile` is deprecated"
  unless self.config.moreServerArgs.isEmpty do
    logWarning s!"{self.name}: package configuration option `moreServerArgs` is deprecated in favor of `moreServerOptions`"

  -- Fill in the Package
  return {self with
    depConfigs, leanLibConfigs, leanExeConfigs, externLibConfigs
    opaqueTargetConfigs, defaultTargets, scripts, defaultScripts
    testDriver, lintDriver,  postUpdateHooks
  }

/--
Load module/package facets into a `Workspace` from a configuration environment.
-/
def Workspace.addFacetsFromEnv
(env : Environment) (opts : Options) (self : Workspace) : Except String Workspace := do
  let mut ws := self
  for name in moduleFacetAttr.getAllEntries env do
    match evalConstCheck env opts ModuleFacetDecl ``ModuleFacetDecl name with
    | .ok decl => ws := ws.addModuleFacetConfig <| decl.config
    | .error e => error e
  for name in packageFacetAttr.getAllEntries env do
    match evalConstCheck env opts PackageFacetDecl ``PackageFacetDecl name with
    | .ok decl => ws := ws.addPackageFacetConfig <| decl.config
    | .error e => error e
  for name in libraryFacetAttr.getAllEntries env do
    match evalConstCheck env opts LibraryFacetDecl ``LibraryFacetDecl name with
    | .ok decl => ws := ws.addLibraryFacetConfig <| decl.config
    | .error e => error e
  return ws
