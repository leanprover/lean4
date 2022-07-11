/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build
import Lake.CLI.Error

namespace Lake

def Package.defaultTarget (self : Package) : OpaqueTarget :=
  match self.defaultFacet with
  | .exe => self.exeTarget.withoutInfo
  | .staticLib => self.staticLibTarget.withoutInfo
  | .sharedLib => self.sharedLibTarget.withoutInfo
  | .leanLib => self.leanLibTarget.withoutInfo
  | .none => Target.nil

def parsePackageSpec (ws : Workspace) (spec : String) : Except CliError Package :=
  if spec.isEmpty then
    return ws.root
  else
    match ws.findPackage? spec.toName with
    | some pkg => return pkg
    | none => throw <| CliError.unknownPackage spec

open Module in
def resolveModuleTarget (ws : Workspace) (mod : Module) (facet : Name) : Except CliError OpaqueTarget :=
  if facet.isAnonymous || facet == `bin  then
    return mod.facetTarget leanBinFacet
  else if facet == `ilean then
    return mod.facetTarget ileanFacet
  else if facet == `olean then
    return mod.facetTarget oleanFacet
  else if facet == `c then
    return mod.facetTarget cFacet
  else if facet == `o then
    return mod.facetTarget oFacet
  else if facet == `dynlib then
    return mod.facetTarget dynlibFacet
  else if let some config := ws.findModuleFacetConfig? facet then
    if let some (.up ⟨_, h⟩) := config.result_eq_target? then
      have := config.familyDefTarget h
      return mod.facetTarget facet
    else
      throw <| CliError.nonTargetFacet "module" facet
  else
    throw <| CliError.unknownFacet "module" facet

def resolveLibTarget (lib : LeanLib) (facet : Name) : Except CliError OpaqueTarget :=
  if facet.isAnonymous || facet == `lean then
    return lib.leanTarget
  else if facet == `static then
    return lib.staticLibTarget |>.withoutInfo
  else if facet == `shared then
    return lib.sharedLibTarget |>.withoutInfo
  else
    throw <| CliError.unknownFacet "library" facet

def resolveExeTarget (exe : LeanExe) (facet : Name) : Except CliError OpaqueTarget :=
  if facet.isAnonymous || facet == `exe then
    return exe.target |>.withoutInfo
  else
    throw <| CliError.unknownFacet "executable" facet

def resolveTargetInPackage (ws : Workspace) (pkg : Package) (target : Name) (facet : Name) : Except CliError OpaqueTarget :=
  if let some config := pkg.findTargetConfig? target then
    if !facet.isAnonymous then
      throw <| CliError.invalidFacet target facet
    else if h : pkg.name = config.package then
      have : FamilyDef CustomData (pkg.name, config.name) (ActiveBuildTarget config.resultType) :=
        ⟨by simp [h]⟩
      return pkg.customTarget config.name |>.target
    else
      throw <| CliError.badTarget pkg.name target config.package config.name
  else if let some exe := pkg.findLeanExe? target then
    resolveExeTarget exe facet
  else if let some lib := pkg.findExternLib? target then
    if facet.isAnonymous then
      return lib.target.withoutInfo
    else
      throw <| CliError.invalidFacet target facet
  else if let some lib := pkg.findLeanLib? target then
    resolveLibTarget lib facet
  else if let some mod := pkg.findModule? target then
    resolveModuleTarget ws mod facet
  else
    throw <| CliError.missingTarget pkg.name (target.toString false)

def resolveDefaultPackageTarget (ws : Workspace) (pkg : Package) : Except CliError OpaqueTarget :=
  if pkg.defaultTargets.isEmpty then
    return pkg.defaultTarget
  else
    return Target.collectOpaqueArray <| ←
      pkg.defaultTargets.mapM (resolveTargetInPackage ws pkg · .anonymous)

def resolvePackageTarget (ws : Workspace) (pkg : Package) (facet : Name) : Except CliError OpaqueTarget :=
  if facet.isAnonymous then
    resolveDefaultPackageTarget ws pkg
  else if facet == `exe then
    return pkg.exeTarget.withoutInfo
  else if facet == `staticLib then
    return pkg.staticLibTarget.withoutInfo
  else if facet == `sharedLib then
    return pkg.sharedLibTarget.withoutInfo
  else if facet == `leanLib then
    return pkg.leanLibTarget.withoutInfo
  else if let some config := ws.findPackageFacetConfig? facet then
    if let some (.up ⟨_, h⟩) := config.result_eq_target? then
      have := config.familyDefTarget h
      return pkg.facet facet |>.target
    else
      throw <| CliError.nonTargetFacet "package" facet
  else
    throw <| CliError.unknownFacet "package" facet

def resolveTargetInWorkspace (ws : Workspace) (target : Name) (facet : Name) : Except CliError OpaqueTarget :=
  if let some (pkg, config) := ws.findTargetConfig? target then
    if !facet.isAnonymous then
      throw <| CliError.invalidFacet config.name facet
    else if h : pkg.name = config.package then
      have : FamilyDef CustomData (pkg.name, config.name) (ActiveBuildTarget config.resultType) :=
        ⟨by simp [h]⟩
      return pkg.customTarget config.name |>.target
    else
      throw <| CliError.badTarget pkg.name target config.package config.name
  else if let some exe := ws.findLeanExe? target then
    resolveExeTarget exe facet
  else if let some lib := ws.findExternLib? target then
    if facet.isAnonymous then
      return lib.target.withoutInfo
    else
      throw <| CliError.invalidFacet target facet
  else if let some lib := ws.findLeanLib? target then
    resolveLibTarget lib facet
  else if let some pkg := ws.findPackage? target then
    resolvePackageTarget ws pkg facet
  else if let some mod := ws.findModule? target then
    resolveModuleTarget ws mod facet
  else
    throw <| CliError.unknownTarget target

def resolveTargetBaseSpec (ws : Workspace) (spec : String) (facet : Name) : Except CliError OpaqueTarget := do
  match spec.splitOn "/" with
  | [spec] =>
    if spec.isEmpty then
      resolvePackageTarget ws ws.root facet
    else if spec.startsWith "@" then
      let pkg ← parsePackageSpec ws <| spec.drop 1
      resolvePackageTarget ws pkg facet
    else if spec.startsWith "+" then
      let mod := spec.drop 1 |>.toName
      if let some mod := ws.findModule? mod then
        resolveModuleTarget ws mod facet
      else
        throw <| CliError.unknownModule mod
    else
      resolveTargetInWorkspace ws spec.toName facet
  | [pkgSpec, targetSpec] =>
    let pkgSpec := if pkgSpec.startsWith "@" then pkgSpec.drop 1 else pkgSpec
    let pkg ← parsePackageSpec ws pkgSpec
    if targetSpec.startsWith "+" then
      let mod := targetSpec.drop 1 |>.toName
      if let some mod := pkg.findModule? mod then
        resolveModuleTarget ws mod facet
      else
        throw <| CliError.unknownModule mod
    else
      resolveTargetInPackage ws pkg targetSpec facet
  | _ =>
    throw <| CliError.invalidTargetSpec spec '/'

def parseTargetSpec (ws : Workspace) (spec : String) : Except CliError OpaqueTarget := do
  match spec.splitOn ":" with
  | [spec] =>
    resolveTargetBaseSpec ws spec .anonymous
  | [rootSpec, facet] =>
    resolveTargetBaseSpec ws rootSpec (Name.ofString facet)
  | _ =>
    throw <| CliError.invalidTargetSpec spec ':'
