/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Index
import Lake.CLI.Error

namespace Lake

/-! ## Build Target Specifiers -/

structure BuildSpec where
  info : BuildInfo
  getBuildJob : BuildData info.key → BuildJob Unit

@[inline] def BuildSpec.getJob (self : BuildSpec) (data : BuildData self.info.key) : Job Unit :=
  discard <| self.getBuildJob data

@[inline] def BuildData.toBuildJob
[FamilyOut BuildData k (BuildJob α)] (data : BuildData k) : BuildJob Unit :=
  discard <| ofFamily data

@[inline] def mkBuildSpec (info : BuildInfo)
[FamilyOut BuildData info.key (BuildJob α)] : BuildSpec :=
  {info, getBuildJob := BuildData.toBuildJob}

@[inline] def mkConfigBuildSpec (facetType : String)
(info : BuildInfo) (config : FacetConfig Fam ι facet) (h : BuildData info.key = Fam facet)
: Except CliError BuildSpec := do
  let some getJob := config.getJob?
    | throw <| CliError.nonCliFacet facetType facet
  return {info, getBuildJob := h ▸ getJob}

def BuildSpec.build (self : BuildSpec) : RecBuildM (Job Unit) :=
  self.getJob <$> buildIndexTop' self.info

def buildSpecs (specs : Array BuildSpec) : BuildM PUnit := do
  let jobs ← RecBuildM.run do specs.mapM (·.build)
  jobs.forM (discard <| ·.await)

/-! ## Parsing CLI Build Target Specifiers -/

def parsePackageSpec (ws : Workspace) (spec : String) : Except CliError Package :=
  if spec.isEmpty then
    return ws.root
  else
    match ws.findPackage? <| stringToLegalOrSimpleName spec with
    | some pkg => return pkg
    | none => throw <| CliError.unknownPackage spec

open Module in
def resolveModuleTarget (ws : Workspace) (mod : Module) (facet : Name) : Except CliError BuildSpec :=
  if facet.isAnonymous then
    return mkBuildSpec <| mod.facet leanArtsFacet
  else if let some config := ws.findModuleFacetConfig? facet then do
    mkConfigBuildSpec "module" (mod.facet facet) config rfl
  else
    throw <| CliError.unknownFacet "module" facet

def resolveLibTarget (ws : Workspace) (lib : LeanLib) (facet : Name) : Except CliError (Array BuildSpec) :=
  if facet.isAnonymous then
    lib.defaultFacets.mapM (resolveFacet ·)
  else
    Array.singleton <$> resolveFacet facet
where
  resolveFacet facet :=
    if let some config := ws.findLibraryFacetConfig? facet then do
      mkConfigBuildSpec "library" (lib.facet facet) config rfl
    else
      throw <| CliError.unknownFacet "library" facet

def resolveExeTarget (exe : LeanExe) (facet : Name) : Except CliError BuildSpec :=
  if facet.isAnonymous || facet == `exe then
    return mkBuildSpec exe.exe
  else
    throw <| CliError.unknownFacet "executable" facet

def resolveExternLibTarget (lib : ExternLib) (facet : Name) : Except CliError BuildSpec :=
  if facet.isAnonymous || facet = `static then
    return mkBuildSpec lib.static
  else if facet = `shared then
    return mkBuildSpec lib.shared
  else
    throw <| CliError.unknownFacet "external library" facet

def resolveCustomTarget (pkg : Package)
(name facet : Name) (config : TargetConfig pkg.name name) : Except CliError BuildSpec :=
  if !facet.isAnonymous then
    throw <| CliError.invalidFacet name facet
  else do
    let info := pkg.target name
    have h : BuildData info.key = CustomData (pkg.name, name) := rfl
    return {info, getBuildJob := h ▸ config.getJob}

def resolveTargetInPackage (ws : Workspace)
(pkg : Package) (target facet : Name) : Except CliError (Array BuildSpec) :=
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

def resolveDefaultPackageTarget (ws : Workspace) (pkg : Package) : Except CliError (Array BuildSpec) :=
  pkg.defaultTargets.concatMapM (resolveTargetInPackage ws pkg · .anonymous)

def resolvePackageTarget (ws : Workspace) (pkg : Package) (facet : Name) : Except CliError (Array BuildSpec) :=
  if facet.isAnonymous then
    resolveDefaultPackageTarget ws pkg
  else if let some config := ws.findPackageFacetConfig? facet then do
    Array.singleton <$> mkConfigBuildSpec "package" (pkg.facet facet) config rfl
  else
    throw <| CliError.unknownFacet "package" facet

def resolveTargetInWorkspace (ws : Workspace)
(target : Name) (facet : Name) : Except CliError (Array BuildSpec) :=
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
(ws : Workspace) (spec : String) (facet : Name) : Except CliError (Array BuildSpec) := do
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

def parseExeTargetSpec (ws : Workspace) (spec : String) : Except CliError LeanExe := do
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

def parseTargetSpec (ws : Workspace) (spec : String) : Except CliError (Array BuildSpec) := do
  match spec.splitOn ":" with
  | [spec] =>
    resolveTargetBaseSpec ws spec .anonymous
  | [rootSpec, facet] =>
    resolveTargetBaseSpec ws rootSpec facet.toName
  | _ =>
    throw <| CliError.invalidTargetSpec spec ':'

def parseTargetSpecs (ws : Workspace) (specs : List String) : Except CliError (Array BuildSpec) := do
  let mut results := #[]
  for spec in specs do
    results := results ++ (← parseTargetSpec ws spec)
  if results.isEmpty then
    results ← resolveDefaultPackageTarget ws ws.root
  return results
