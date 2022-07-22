/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.DSL.Attributes
import Lake.Config.FacetConfig
import Lake.Config.TargetConfig
import Lake.Load.Elab

namespace Lake
open Lean System

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
@[implementedBy unsafeEvalConstCheck] opaque evalConstCheck
(env : Environment) (opts : Options) (α) (type : Name) (const : Name) : Except String α

/-- Construct a `NameMap` from the declarations tagged with `attr`. -/
def mkTagMap
(env : Environment) (attr : TagAttribute)
[Monad m]  (f : Name → m α) : m (NameMap α) :=
  attr.ext.getState env |>.foldM (init := {}) fun map declName =>
    return map.insert declName <| ← f declName

/-- Construct a `DNameMap` from the declarations tagged with `attr`. -/
def mkDTagMap
(env : Environment) (attr : TagAttribute)
[Monad m] (f : (n : Name) → m (β n)) : m (DNameMap β) :=
  attr.ext.getState env |>.foldM (init := {}) fun map declName =>
    return map.insert declName <| ← f declName

/-- Load a `PackageConfig` from a configuration environment. -/
def PackageConfig.loadFromEnv
(env : Environment) (opts := Options.empty) : Except String PackageConfig := do
  let declName ←
    match packageAttr.ext.getState env |>.toList with
    | [] => error s!"configuration file is missing a `package` declaration"
    | [name] => pure name
    | _ => error s!"configuration file has multiple `package` declarations"
  evalConstCheck env opts _  ``PackageConfig declName

/--
Load the remainder of a `Package`
from its configuration environment after resolving its dependencies.
-/
def Package.finalize (self : Package) (deps : Array Package) : LogIO Package := do
  let env := self.configEnv; let opts := self.leanOpts

  -- Load Script, Facet, & Target Configurations
  let scripts ← mkTagMap env scriptAttr fun name => do
    let fn ← IO.ofExcept <| evalConstCheck env opts ScriptFn ``ScriptFn name
    return {fn, doc? := (← findDocString? env name)}
  let leanLibConfigs ← IO.ofExcept <| mkTagMap env leanLibAttr fun name =>
    evalConstCheck env opts LeanLibConfig ``LeanLibConfig name
  let leanExeConfigs ← IO.ofExcept <| mkTagMap env leanExeAttr fun name =>
    evalConstCheck env opts LeanExeConfig ``LeanExeConfig name
  let externLibConfigs ← IO.ofExcept <| mkTagMap env externLibAttr fun name =>
    evalConstCheck env opts ExternLibConfig ``ExternLibConfig name
  let opaqueModuleFacetConfigs ← mkDTagMap env moduleFacetAttr fun name => do
    match evalConstCheck env opts  ModuleFacetDecl ``ModuleFacetDecl name with
    | .ok decl =>
      if h : name = decl.name then
        return OpaqueModuleFacetConfig.mk (h ▸ decl.config)
      else
        error s!"facet was defined as `{decl.name}`, but was registered as `{name}`"
    | .error e => error e
  let opaquePackageFacetConfigs ← mkDTagMap env packageFacetAttr fun name => do
    match evalConstCheck env opts  PackageFacetDecl ``PackageFacetDecl name with
    | .ok decl =>
      if h : name = decl.name then
        return OpaquePackageFacetConfig.mk (h ▸ decl.config)
      else
        error s!"facet was defined as `{decl.name}`, but was registered as `{name}`"
    | .error e => error e
  let opaqueTargetConfigs ← mkTagMap env targetAttr fun declName =>
    match evalConstCheck env opts TargetConfig ``TargetConfig declName with
    | .ok a => pure <| OpaqueTargetConfig.mk a
    | .error e => error e
  let defaultTargets := defaultTargetAttr.ext.getState env |>.fold (·.push ·) #[]

  -- Issue Warnings
  if self.config.extraDepTarget.isSome then
    logWarning <| "`extraDepTarget` has been deprecated. " ++
      "Try to use a custom target or raise an issue about your use case."
  if leanLibConfigs.isEmpty && leanExeConfigs.isEmpty && self.defaultFacet ≠ .none then
    logWarning <| "Package targets are deprecated. " ++
      "Add a `lean_exe` and/or `lean_lib` default target to the package instead."

  -- Fill in the Package
  return {self with
    opaqueDeps := deps.map (.mk ·)
    leanLibConfigs, leanExeConfigs, externLibConfigs
    opaqueModuleFacetConfigs, opaquePackageFacetConfigs, opaqueTargetConfigs
    defaultTargets, scripts
  }
