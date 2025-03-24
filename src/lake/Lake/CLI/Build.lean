/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Config.Monad
import Lake.Build.Job
import Lake.CLI.Error

open System Lean

namespace Lake

/-! ## Build Target Specifiers -/

structure BuildSpec where
  info : BuildInfo
  buildable := true
  format : OutFormat → BuildData info.key → String := nullFormat

@[inline] def mkBuildSpec
  (info : BuildInfo) [FormatQuery α] [h : FamilyOut BuildData info.key α]
: BuildSpec where
  info
  buildable := true
  format := h.family_key_eq_type ▸ formatQuery

@[inline] def mkConfigBuildSpec
  (info : BuildInfo)
  (config : FacetConfig Fam ι facet) (h : BuildData info.key = Fam facet)
: BuildSpec where
  info
  buildable := config.buildable
  format := h ▸ config.format

@[inline] protected def BuildSpec.fetch (self : BuildSpec) : FetchM (Job (BuildData self.info.key)) := do
  maybeRegisterJob self.info.key.toSimpleString (← self.info.fetch)

@[inline] protected def BuildSpec.build (self : BuildSpec) : FetchM OpaqueJob := do
  return (← self.fetch).toOpaque

@[inline] protected def BuildSpec.query (self : BuildSpec) (fmt : OutFormat) : FetchM (Job String) := do
  maybeRegisterJob self.info.key.toSimpleString =<< do
    return (← self.info.fetch).map (self.format fmt)

def buildSpecs (specs : Array BuildSpec) : FetchM (Job Unit) := do
  return Job.mixArray (← specs.mapM (·.build))

def querySpecs (specs : Array BuildSpec) (fmt : OutFormat) : FetchM (Job (Array String)) := do
  return Job.collectArray (← specs.mapM (·.query fmt))

/-! ## Parsing CLI Build Target Specifiers -/

def parsePackageSpec (ws : Workspace) (spec : String) : Except CliError Package :=
  if spec.isEmpty then
    return ws.root
  else
    match ws.findPackage? <| stringToLegalOrSimpleName spec with
    | some pkg => return pkg
    | none => throw <| CliError.unknownPackage spec

open Module in
def resolveModuleTarget
  (ws : Workspace) (mod : Module) (facet : Name)
: Except CliError BuildSpec :=
  if facet.isAnonymous then
    return mkBuildSpec (mod.facet leanArtsFacet)
  else if let some config := ws.findModuleFacetConfig? facet then do
    return mkConfigBuildSpec (mod.facet facet) config rfl
  else
    throw <| CliError.unknownFacet "module" facet

def resolveLibTarget
  (ws : Workspace) (lib : LeanLib) (facet : Name := .anonymous)
: Except CliError (Array BuildSpec) :=
  if facet.isAnonymous then
    lib.defaultFacets.mapM (resolveFacet ·)
  else
    Array.singleton <$> resolveFacet facet
where
  resolveFacet facet :=
    if let some config := ws.findLibraryFacetConfig? facet then do
      return mkConfigBuildSpec (lib.facet facet) config rfl
    else
      throw <| CliError.unknownFacet "library" facet

def resolveExeTarget
  (exe : LeanExe) (facet : Name)
: Except CliError BuildSpec :=
  if facet.isAnonymous || facet == `exe then
    return mkBuildSpec exe.exe
  else
    throw <| CliError.unknownFacet "executable" facet

def resolveExternLibTarget
  (lib : ExternLib) (facet : Name)
: Except CliError BuildSpec :=
  if facet.isAnonymous || facet = `static then
    return mkBuildSpec lib.static
  else if facet = `shared then
    return mkBuildSpec lib.shared
  else
    throw <| CliError.unknownFacet "external library" facet

set_option linter.unusedVariables false in
def resolveCustomTarget
  (pkg : Package) (name facet : Name) (config : TargetConfig pkg.name name)
: Except CliError BuildSpec :=
  if !facet.isAnonymous then
    throw <| CliError.invalidFacet name facet
  else do
    return {info := pkg.target name, format := config.format}

def resolveTargetInPackage
  (ws : Workspace) (pkg : Package) (target facet : Name)
: Except CliError (Array BuildSpec) :=
  if let some config := pkg.findTargetConfig? target then
    Array.singleton <$> resolveCustomTarget pkg target facet config
  else if let some exe := pkg.findLeanExe? target then
    Array.singleton <$> resolveExeTarget exe facet
  else if let some lib := pkg.findExternLib? target then
    Array.singleton <$> resolveExternLibTarget lib facet
  else if let some lib := pkg.findLeanLib? target then
    resolveLibTarget ws lib facet
  else if let some mod := pkg.findTargetModule? target then
    Array.singleton <$> resolveModuleTarget ws mod facet
  else
    throw <| CliError.missingTarget pkg.name (target.toString false)

def resolveDefaultPackageTarget
  (ws : Workspace) (pkg : Package)
: Except CliError (Array BuildSpec) :=
  pkg.defaultTargets.flatMapM (resolveTargetInPackage ws pkg · .anonymous)

def resolvePackageTarget
  (ws : Workspace) (pkg : Package) (facet : Name)
: Except CliError (Array BuildSpec) :=
  if facet.isAnonymous then
    resolveDefaultPackageTarget ws pkg
  else if let some config := ws.findPackageFacetConfig? facet then do
    return #[mkConfigBuildSpec (pkg.facet facet) config rfl]
  else
    throw <| CliError.unknownFacet "package" facet

def resolveTargetInWorkspace
  (ws : Workspace) (target : Name) (facet : Name)
: Except CliError (Array BuildSpec) :=
  if let some ⟨pkg, config⟩ := ws.findTargetConfig? target then
    Array.singleton <$> resolveCustomTarget pkg target facet config
  else if let some exe := ws.findLeanExe? target then
    Array.singleton <$> resolveExeTarget exe facet
  else if let some lib := ws.findExternLib? target then
    Array.singleton <$> resolveExternLibTarget lib facet
  else if let some lib := ws.findLeanLib? target then
    resolveLibTarget ws lib facet
  else if let some pkg := ws.findPackage? target then
    resolvePackageTarget ws pkg facet
  else if let some mod := ws.findTargetModule? target then
    Array.singleton <$> resolveModuleTarget ws mod facet
  else
    throw <| CliError.unknownTarget target

def resolveTargetBaseSpec
  (ws : Workspace) (spec : String) (facet : Name)
: Except CliError (Array BuildSpec) := do
  match spec.splitOn "/" with
  | [spec] =>
    if spec.isEmpty then
      resolvePackageTarget ws ws.root facet
    else if spec.startsWith "@" then
      let pkg ← parsePackageSpec ws <| spec.drop 1
      resolvePackageTarget ws pkg facet
    else if spec.startsWith "+" then
      let mod := spec.drop 1 |>.toName
      if let some mod := ws.findTargetModule? mod then
        Array.singleton <$> resolveModuleTarget ws mod facet
      else
        throw <| CliError.unknownModule mod
    else
      resolveTargetInWorkspace ws (stringToLegalOrSimpleName spec) facet
  | [pkgSpec, targetSpec] =>
    let pkgSpec := if pkgSpec.startsWith "@" then pkgSpec.drop 1 else pkgSpec
    let pkg ← parsePackageSpec ws pkgSpec
    if targetSpec.isEmpty then
      resolvePackageTarget ws pkg facet
    else if targetSpec.startsWith "+" then
      let mod := targetSpec.drop 1 |>.toName
      if let some mod := pkg.findTargetModule? mod then
        Array.singleton <$> resolveModuleTarget ws mod facet
      else
        throw <| CliError.unknownModule mod
    else
      resolveTargetInPackage ws pkg (stringToLegalOrSimpleName targetSpec) facet
  | _ =>
    throw <| CliError.invalidTargetSpec spec '/'

def parseExeTargetSpec
  (ws : Workspace) (spec : String)
: Except CliError LeanExe := do
  match spec.splitOn "/" with
  | [targetSpec] =>
    let targetName := stringToLegalOrSimpleName targetSpec
    match ws.findLeanExe? targetName with
    | some exe => return exe
    | none => throw <| CliError.unknownExe spec
  | [pkgSpec, targetSpec] =>
    let pkgSpec := if pkgSpec.startsWith "@" then pkgSpec.drop 1 else pkgSpec
    let pkg ← parsePackageSpec ws pkgSpec
    let targetName := stringToLegalOrSimpleName targetSpec
    match pkg.findLeanExe? targetName with
    | some exe => return exe
    | none => throw <| CliError.unknownExe spec
  | _ =>
    throw <| CliError.invalidTargetSpec spec '/'

def parseTargetSpec
  (ws : Workspace) (spec : String)
: Except CliError (Array BuildSpec) := do
  match spec.splitOn ":" with
  | [spec] =>
    resolveTargetBaseSpec ws spec .anonymous
  | [rootSpec, facet] =>
    resolveTargetBaseSpec ws rootSpec facet.toName
  | _ =>
    throw <| CliError.invalidTargetSpec spec ':'

def parseTargetSpecs
  (ws : Workspace) (specs : List String)
: Except CliError (Array BuildSpec) := do
  let mut results := #[]
  for spec in specs do
    results := results ++ (← parseTargetSpec ws spec)
  if results.isEmpty then
    results ← resolveDefaultPackageTarget ws ws.root
  return results
