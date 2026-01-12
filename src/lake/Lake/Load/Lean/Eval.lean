/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lean.Environment
public import Lake.Config.Workspace
import Lake.DSL.Attributes
import Lean.DocString

/-! # Lean Configuration Evaluator

This module contains the definitions to load Lake configuration objects from
a Lean environment elaborated from a Lake configuration file.
-/

open System Lean

namespace Lake

/-- Unsafe implementation of `evalConstCheck`. -/
private unsafe def unsafeEvalConstCheck
  (env : Environment) (opts : Options) (α) [TypeName α] (const : Name)
: Except String α :=
  match env.find? const with
  | none => throw s!"unknown constant '{const}'"
  | some info =>
    match info.type with
    | Expr.const c _ =>
      if c != TypeName.typeName α then
        throwUnexpectedType
      else
        env.evalConst α opts const
    | _ => throwUnexpectedType
where
  throwUnexpectedType : Except String α :=
    throw s!"unexpected type at '{const}', `{TypeName.typeName α}` expected"

/--
Like `Lean.Environment.evalConstCheck`,
but with plain universe-polymorphic `Except`.
-/
@[implemented_by unsafeEvalConstCheck]
private opaque evalConstCheck
  (env : Environment) (opts : Options) (α : Type) [TypeName α] (const : Name)
: Except String α

/-- Construct a `DNameMap` from the declarations tagged with `attr`. -/
private def mkDTagMap
  (env : Environment) (attr : OrderedTagAttribute)
  [Monad m] (f : (n : Name) → m (β n))
: m (DNameMap β) :=
  let entries := attr.getAllEntries env
  entries.foldlM (init := {}) fun map declName =>
    return map.insert declName <| ← f declName

/-- Construct a `NameMap` from the declarations tagged with `attr`. -/
private def mkTagMap
  (env : Environment) (attr : OrderedTagAttribute)
  [Monad m] (f : (n : Name) → m β)
: m (NameMap β) :=
  let entries := attr.getAllEntries env
  entries.foldlM (init := {}) fun map declName =>
    return map.insert declName <| ← f declName

/-- Construct a `OrdNameMap` from the declarations tagged with `attr`. -/
private def mkOrdTagMap
  (env : Environment) (attr : OrderedTagAttribute)
  [Monad m] (f : (n : Name) → m β)
: m (OrdNameMap β) :=
  let entries := attr.getAllEntries env
  entries.foldlM (init := .mkEmpty entries.size) fun map declName =>
    return map.insert declName <| ← f declName

/-- Load a `PackageDecl` from a configuration environment. -/
public def PackageDecl.loadFromEnv
  (env : Environment) (opts := Options.empty)
: Except String PackageDecl := do
  let declName ←
    match packageAttr.getAllEntries env |>.toList with
    | [] => error s!"configuration file is missing a `package` declaration"
    | [name] => pure name
    | _ => error s!"configuration file has multiple `package` declarations"
  evalConstCheck env opts _ declName

/--
Load the optional elements of a `Package` from the Lean environment.
This is done after loading its core configuration but before resolving
its dependencies.
-/
public def Package.loadFromEnv
  (self : Package) (env : Environment) (opts : Options)
: LogIO Package := do

  -- load target, script, hook, and driver configurations
  let constTargetMap ← IO.ofExcept <| mkOrdTagMap env targetAttr fun name => do
    evalConstCheck env opts ConfigDecl name
  let targetDecls ← constTargetMap.toArray.mapM fun decl => do
    if h : decl.pkg = self.keyName then
      return .mk decl h
    else
      error s!"\
        target '{decl.name}' was defined in package '{decl.pkg}', \
        but registered under '{self.keyName}'"
  let targetDeclMap ← targetDecls.foldlM (init := {}) fun m decl => do
    if let some orig := m.get? decl.name then
      error s!"\
        {self.prettyName}: target '{decl.name}' was already defined as a '{orig.kind}', \
        but then redefined as a '{decl.kind}'"
    else
      return m.insert decl.name (.mk decl rfl)
  let defaultTargets ← defaultTargetAttr.getAllEntries env |>.mapM fun name =>
    if let some decl := constTargetMap.find? name then pure decl.name else
      error s!"{self.prettyName}: package is missing target '{name}' marked as a default"
  let scripts ← mkTagMap env scriptAttr fun scriptName => do
    let name := self.prettyName ++ "/" ++ scriptName.toString (escape := false)
    let fn ← IO.ofExcept <| evalConstCheck env opts ScriptFn scriptName
    return {name, fn, doc? := ← findDocString? env scriptName : Script}
  let defaultScripts ← defaultScriptAttr.getAllEntries env |>.mapM fun name =>
    if let some script := scripts.get? name then pure script else
      error s!"{self.prettyName}: package is missing script '{name}' marked as a default"
  let postUpdateHooks ← postUpdateAttr.getAllEntries env |>.mapM fun name =>
    match evalConstCheck env opts PostUpdateHookDecl name with
    | .ok decl =>
      if h : decl.pkg = self.keyName then
        return OpaquePostUpdateHook.mk ⟨cast (by rw [h, keyName]) decl.fn⟩
      else
        error s!"post-update hook was defined in '{decl.pkg}', but was registered in '{self.keyName}'"
    | .error e => error e
  let depConfigs ← IO.ofExcept <| packageDepAttr.getAllEntries env |>.mapM fun name =>
    evalConstCheck env opts Dependency name
  let testDrivers ← testDriverAttr.getAllEntries env |>.mapM fun name =>
    if let some decl := constTargetMap.find? name then
      pure decl.name
    else if scripts.contains name then
      pure name
    else
      error s!"{self.prettyName}: package is missing script or target '{name}' marked as a test driver"
  let testDriver ←
    if testDrivers.size > 1 then
      error s!"{self.prettyName}: only one script, executable, or library can be tagged @[test_driver]"
    else if h : testDrivers.size > 0 then
      if self.config.testDriver.isEmpty then
        pure (testDrivers[0]'h |>.toString)
      else
        error s!"{self.prettyName}: cannot both set testDriver and use @[test_driver]"
    else
      pure self.config.testDriver
  let lintDrivers ← lintDriverAttr.getAllEntries env |>.mapM fun name =>
    if let some decl := constTargetMap.find? name then
      pure decl.name
    else if scripts.contains name then
      pure name
    else
      error s!"{self.prettyName}: package is missing script or target '{name}' marked as a lint driver"
  let lintDriver ←
    if lintDrivers.size > 1 then
      error s!"{self.prettyName}: only one script or executable can be tagged @[lint_driver]"
    else if h : lintDrivers.size > 0 then
      if self.config.lintDriver.isEmpty then
        pure (lintDrivers[0]'h |>.toString)
      else
        error s!"{self.prettyName}: cannot both set lintDriver and use @[lint_driver]"
    else
      pure self.config.lintDriver

  -- Deprecation warnings
  unless self.config.manifestFile.isNone do
    logWarning s!"{self.prettyName}: package configuration option 'manifestFile' is deprecated"

  -- Fill in the Package
  return {self with
    depConfigs, targetDecls, targetDeclMap
    defaultTargets, scripts, defaultScripts
    testDriver, lintDriver,  postUpdateHooks
  }

/--
Load module/package facets into a `Workspace` from a configuration environment.
-/
public def Workspace.addFacetsFromEnv
  (env : Environment) (opts : Options) (self : Workspace)
: Except String Workspace := do
  let mut ws := self
  for name in moduleFacetAttr.getAllEntries env do
    let decl ← evalConstCheck env opts ModuleFacetDecl name
    ws := ws.addModuleFacetConfig decl.config
  for name in packageFacetAttr.getAllEntries env do
    let decl ← evalConstCheck env opts PackageFacetDecl name
    ws := ws.addPackageFacetConfig decl.config
  for name in libraryFacetAttr.getAllEntries env do
    let decl ← evalConstCheck env opts LibraryFacetDecl name
    ws := ws.addLibraryFacetConfig decl.config
  return ws
