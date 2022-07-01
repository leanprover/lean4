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
def resolveModuleTarget (ws : Workspace) (mod : Module) (facet : String) : Except CliError OpaqueTarget :=
  if facet.isEmpty || facet == "bin"  then
    return mod.facetTarget leanBinFacet
  else if facet == "ilean" then
    return mod.facetTarget ileanFacet
  else if facet == "olean" then
    return mod.facetTarget oleanFacet
  else if facet == "c" then
    return mod.facetTarget cFacet
  else if facet == "o" then
    return mod.facetTarget oFacet
  else if facet == "dynlib" then
    return mod.facetTarget dynlibFacet
  else if let some config := ws.findModuleFacetConfig? facet then
    return mod.facetTarget config.name
  else
    throw <| CliError.unknownFacet "module" facet

def resolveLibTarget (lib : LeanLib) (facet : String) : Except CliError OpaqueTarget :=
  if facet.isEmpty || facet == "lean" || facet == "oleans" then
    return lib.leanTarget
  else if facet == "static" then
    return lib.staticLibTarget |>.withoutInfo
  else if facet == "shared" then
    return lib.sharedLibTarget |>.withoutInfo
  else
    throw <| CliError.unknownFacet "library" facet

def resolveExeTarget (exe : LeanExe) (facet : String) : Except CliError OpaqueTarget :=
  if facet.isEmpty || facet == "exe" then
    return exe.target |>.withoutInfo
  else
    throw <| CliError.unknownFacet "executable" facet

def resolveTargetInPackage (ws : Workspace) (pkg : Package) (target : Name) (facet : String) : Except CliError OpaqueTarget :=
  if let some target := pkg.findTargetConfig? target then
    return pkg.customTarget target.name |>.target
  else if let some exe := pkg.findLeanExe? target then
    resolveExeTarget exe facet
  else if let some lib := pkg.findExternLib? target then
    if facet.isEmpty then
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
      pkg.defaultTargets.mapM (resolveTargetInPackage ws pkg · "")

def resolvePackageTarget (ws : Workspace) (pkg : Package) (facet : String) : Except CliError OpaqueTarget :=
  if facet.isEmpty then
    resolveDefaultPackageTarget ws pkg
  else if facet == "exe" || facet == "bin" then
    return pkg.exeTarget.withoutInfo
  else if facet == "staticLib" then
    return pkg.staticLibTarget.withoutInfo
  else if facet == "sharedLib" then
    return pkg.sharedLibTarget.withoutInfo
  else if facet == "leanLib" || facet == "oleans" then
    return pkg.leanLibTarget.withoutInfo
  else if let some config := ws.findPackageFacetConfig? facet then
    return pkg.facet config.name |>.target
  else
    throw <| CliError.unknownFacet "package" facet

def resolveTargetInWorkspace (ws : Workspace) (spec : String) (facet : String) : Except CliError OpaqueTarget :=
  if let some (pkg, target) := ws.findTargetConfig? spec then
    return pkg.customTarget target.name |>.target
  else if let some exe := ws.findLeanExe? spec.toName then
    resolveExeTarget exe facet
  else if let some lib := ws.findExternLib? spec.toName then
    if facet.isEmpty then
      return lib.target.withoutInfo
    else
      throw <| CliError.invalidFacet spec facet
  else if let some lib := ws.findLeanLib? spec.toName then
    resolveLibTarget lib facet
  else if let some pkg := ws.findPackage? spec.toName then
    resolvePackageTarget ws pkg facet
  else if let some mod := ws.findModule? spec.toName then
    resolveModuleTarget ws mod facet
  else
    throw <| CliError.unknownTarget spec

def resolveTargetBaseSpec (ws : Workspace) (spec : String) (facet := "") : Except CliError OpaqueTarget := do
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
      resolveTargetInWorkspace ws spec facet
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
      resolveTargetInPackage ws pkg spec facet
  | _ =>
    throw <| CliError.invalidTargetSpec spec '/'

def parseTargetSpec (ws : Workspace) (spec : String) : Except CliError OpaqueTarget := do
  match spec.splitOn ":" with
  | [spec] =>
    resolveTargetBaseSpec ws spec
  | [rootSpec, facet] =>
    resolveTargetBaseSpec ws rootSpec facet
  | _ =>
    throw <| CliError.invalidTargetSpec spec ':'
