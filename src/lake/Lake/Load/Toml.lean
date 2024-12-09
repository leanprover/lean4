/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Toml.Load
import Lake.Toml.Decode
import Lake.Config.Package
import Lake.Util.Log

open Lean Parser

/-! # TOML Loader

This module contains the main definitions to load a package from a
Lake configuration file written in TOML.
-/

namespace Lake
open System (FilePath)

open Toml

/-! ## Data Decoders -/

def takeNamePart (ss : Substring) (pre : Name) : (Substring × Name) :=
  if ss.isEmpty then
    (ss, .anonymous)
  else
    let curr := ss.front
    if isIdBeginEscape curr then
      let ss := ss.drop 1
      let startPos := ss.startPos
      let ss := ss.dropWhile (!isIdEndEscape ·)
      if isIdEndEscape ss.front then
        let id := ss.str.extract startPos ss.startPos
        (ss, Name.str pre id)
      else
        (ss, .anonymous)
    else if isIdFirst curr then
      let startPos := ss.startPos
      let ss := ss.drop 1 |>.dropWhile isIdRest
      let id := ss.str.extract startPos ss.startPos
      (ss, Name.str pre id)
    else if curr.isDigit then
      let startPos := ss.startPos
      let ss := ss.drop 1 |>.dropWhile Char.isDigit
      let digits := ss.str.extract startPos ss.startPos
      let n := (Syntax.decodeNatLitVal? digits).get!
      (ss, Name.num pre n)
    else
      (ss, .anonymous)

partial def takeName (ss : Substring) : (Substring × Name) :=
  let rec takeRest ss pre :=
    if ss.front == '.' then
      let startPos := ss.startPos
      let (ss, n) := takeNamePart (ss.drop 1) pre
      if n.isAnonymous then ({ss with startPos}, pre) else takeRest ss n
    else
      (ss, pre)
  let (ss, n) := takeNamePart ss .anonymous
  if n.isAnonymous then (ss, .anonymous) else takeRest ss n

def Glob.ofString? (v : String) : Option Glob := do
  let (ss, n) := takeName v.toSubstring
  if n.isAnonymous then failure
  if h : ss.str.atEnd ss.startPos then
    return .one n
  else if ss.str.get' ss.startPos h == '.' then
    match (ss.drop 1).front with
    | '+' => return .submodules n
    | '*' => return .andSubmodules n
    | _ => failure
  else
    failure

protected def Glob.decodeToml (v : Value) : Except DecodeError Glob := do
  match inline <| Glob.ofString? (← v.decodeString) with
  | some v => return v
  | none => throw <| .mk v.ref "expected glob"

instance : DecodeToml Glob := ⟨(Glob.decodeToml ·)⟩

protected def LeanOptionValue.decodeToml : Value → Except DecodeError LeanOptionValue
| .string _ v => return .ofString v
| .boolean _ v => return .ofBool v
| .integer _ (.ofNat v) => return .ofNat v
| x => throw (.mk x.ref "expected string, boolean, or nonnegative integer")

instance : DecodeToml LeanOptionValue := ⟨(LeanOptionValue.decodeToml ·)⟩

protected def LeanOption.decodeToml (v : Value) : Except (Array DecodeError) LeanOption := do
  match v with
  | .array ref vs =>
    if h : vs.size = 2 then ensureDecode do
      let name : Name ← tryDecode <| decodeToml vs[0]
      let value ← tryDecode <| decodeToml vs[1]
      return {name, value}
    else
      throw #[.mk ref "expected array of size 2"]
  | .table ref t => ensureDecode do
    let name ← t.tryDecode `name ref
    let value ← t.tryDecode `value ref
    return {name, value}
  | v =>
    throw #[.mk v.ref "expected array or table"]

instance : DecodeToml LeanOption := ⟨LeanOption.decodeToml⟩

protected def BuildType.decodeToml (v : Value) : Except DecodeError BuildType := do
  match inline <| BuildType.ofString? (← v.decodeString) with
  | some v => return v
  | none => throw <| .mk v.ref "expected one of 'debug', 'relWithDebInfo', 'minSizeRel', 'release'"

instance : DecodeToml BuildType := ⟨(BuildType.decodeToml ·)⟩

protected def Backend.decodeToml (v : Value) : Except DecodeError Backend := do
  match inline <| Backend.ofString? (← v.decodeString) with
  | some v => return v
  | none => throw <| .mk v.ref "expected one of 'c', 'llvm', or 'default'"

instance : DecodeToml Backend := ⟨(Backend.decodeToml ·)⟩

partial def decodeLeanOptionsAux
  (v : Value) (k : Name) (vs : Except (Array DecodeError) (Array LeanOption))
: Except (Array DecodeError) (Array LeanOption) :=
  match v with
  | .table _ t => t.items.foldl (init := vs) fun vs (k',v) =>
    decodeLeanOptionsAux v (k ++ k') vs
  | v => mergeErrors vs (decodeToml v) fun vs v => vs.push ⟨k,v⟩

def decodeLeanOptions (v : Value) : Except (Array DecodeError) (Array LeanOption) :=
  match v with
  | .array _ vs => decodeArray vs
  | .table _ t => t.items.foldl (init := .ok #[]) fun vs (k,v) => decodeLeanOptionsAux v k vs
  | v =>
    throw #[.mk v.ref "expected array or table"]

protected def StdVer.decodeToml (v : Value) : Except (Array DecodeError) LeanVer := do
  match StdVer.parse (← v.decodeString) with
  | .ok v => return v
  | .error e => throw #[.mk v.ref e]

instance : DecodeToml StdVer := ⟨(StdVer.decodeToml ·)⟩

protected def StrPat.decodeToml (v : Value) (presets : NameMap StrPat := {}) : Except (Array DecodeError) StrPat :=
  match v with
  | .array _ vs => .mem <$> decodeArray vs
  | .table r t => do
    if let some pre ← t.decode? `startsWith then
      return .startsWith pre
    else if let some name ← t.decode? `preset then
      if let some preset := presets.find? name then
        return preset
      else
        throw #[.mk r s!"unknown preset '{name}'"]
    else
      throw #[.mk r "expected 'startsWith' or 'preset'"]
  | v => throw #[.mk v.ref "expected array or table"]

instance : DecodeToml StrPat := ⟨(StrPat.decodeToml ·)⟩

/-! ## Configuration Decoders -/

protected def WorkspaceConfig.decodeToml (t : Table) : Except (Array DecodeError) WorkspaceConfig := ensureDecode do
  let packagesDir ← t.tryDecodeD `packagesDir defaultPackagesDir
  return {packagesDir}

instance : DecodeToml WorkspaceConfig := ⟨fun v => do WorkspaceConfig.decodeToml (← v.decodeTable)⟩

protected def LeanConfig.decodeToml (t : Table) : Except (Array DecodeError) LeanConfig := ensureDecode do
  let buildType ← t.tryDecodeD `buildType .release
  let backend ← t.tryDecodeD `backend .default
  let platformIndependent ← t.tryDecode? `platformIndependent
  let leanOptions ← optDecodeD #[] (t.find? `leanOptions) decodeLeanOptions
  let moreServerOptions ← optDecodeD #[] (t.find? `moreServerOptions) decodeLeanOptions
  let moreLeanArgs ← t.tryDecodeD `moreLeanArgs #[]
  let weakLeanArgs ← t.tryDecodeD `weakLeanArgs #[]
  let moreLeancArgs ← t.tryDecodeD `moreLeancArgs #[]
  let weakLeancArgs ← t.tryDecodeD `weakLeancArgs #[]
  let moreLinkArgs ← t.tryDecodeD `moreLinkArgs #[]
  let weakLinkArgs ← t.tryDecodeD `weakLinkArgs #[]
  return {
    buildType, backend, platformIndependent, leanOptions, moreServerOptions,
    moreLeanArgs, weakLeanArgs, moreLeancArgs, weakLeancArgs, moreLinkArgs, weakLinkArgs
  }

instance : DecodeToml LeanConfig := ⟨fun v => do LeanConfig.decodeToml (← v.decodeTable)⟩

protected def PackageConfig.decodeToml (t : Table) (ref := Syntax.missing) : Except (Array DecodeError) PackageConfig := ensureDecode do
  let name ← stringToLegalOrSimpleName <$> t.tryDecode `name ref
  let precompileModules ← t.tryDecodeD `precompileModules false
  let moreGlobalServerArgs ← t.tryDecodeD `moreGlobalServerArgs #[]
  let srcDir ← t.tryDecodeD `srcDir "."
  let buildDir ← t.tryDecodeD `buildDir defaultBuildDir
  let leanLibDir ← t.tryDecodeD `leanLibDir defaultLeanLibDir
  let nativeLibDir ← t.tryDecodeD `nativeLibDir defaultNativeLibDir
  let binDir ← t.tryDecodeD `binDir defaultBinDir
  let irDir ← t.tryDecodeD `irDir defaultIrDir
  let releaseRepo ← t.tryDecode? `releaseRepo
  let buildArchive? ← t.tryDecode? `buildArchive
  let preferReleaseBuild ← t.tryDecodeD `preferReleaseBuild false
  let testRunner ← t.tryDecodeD `testRunner ""
  let testDriver ← t.tryDecodeD `testDriver ""
  let testDriver := if ¬testRunner.isEmpty ∧ testDriver.isEmpty then testRunner else testDriver
  let testDriverArgs ← t.tryDecodeD `testDriverArgs #[]
  let lintDriver ← t.tryDecodeD `lintDriver ""
  let lintDriverArgs ← t.tryDecodeD `lintDriverArgs #[]
  let version : StdVer ← t.tryDecodeD `version {}
  let versionTags ← optDecodeD defaultVersionTags (t.find? `versionTags)
    <| StrPat.decodeToml (presets := versionTagPresets)
  let description ← t.tryDecodeD `description ""
  let keywords ← t.tryDecodeD `keywords #[]
  let homepage ← t.tryDecodeD `homepage ""
  let license ← t.tryDecodeD `license ""
  let licenseFiles : Array FilePath ← t.tryDecodeD `licenseFiles #["LICENSE"]
  let readmeFile ← t.tryDecodeD `readmeFile "README.md"
  let reservoir ← t.tryDecodeD `reservoir true
  let toLeanConfig ← tryDecode <| LeanConfig.decodeToml t
  let toWorkspaceConfig ← tryDecode <| WorkspaceConfig.decodeToml t
  return {
    name, precompileModules, moreGlobalServerArgs
    srcDir, buildDir, leanLibDir, nativeLibDir, binDir, irDir
    releaseRepo, buildArchive?, preferReleaseBuild
    testDriver, testDriverArgs, lintDriver, lintDriverArgs
    version, versionTags, description, keywords, homepage, reservoir
    license, licenseFiles, readmeFile
    toLeanConfig, toWorkspaceConfig
  }

instance : DecodeToml PackageConfig := ⟨fun v => do PackageConfig.decodeToml (← v.decodeTable) v.ref⟩

protected def LeanLibConfig.decodeToml (t : Table) (ref := Syntax.missing) : Except (Array DecodeError) LeanLibConfig := ensureDecode do
  let name : Name ← t.tryDecode `name ref
  let srcDir ← t.tryDecodeD `srcDir "."
  let roots ← t.tryDecodeD `roots #[name]
  let globs ← optDecodeD (roots.map Glob.one) (t.find? `globs) (·.decodeArrayOrSingleton)
  let libName ← t.tryDecodeD `libName (name.toString (escape := false))
  let precompileModules ← t.tryDecodeD `precompileModules false
  let defaultFacets ← t.tryDecodeD `defaultFacets #[LeanLib.leanArtsFacet]
  let toLeanConfig ← tryDecode <| LeanConfig.decodeToml t
  return {
    name, srcDir, roots, globs, libName,
    precompileModules, defaultFacets, toLeanConfig
  }

instance : DecodeToml LeanLibConfig := ⟨fun v => do LeanLibConfig.decodeToml (← v.decodeTable) v.ref⟩

protected def LeanExeConfig.decodeToml (t : Table) (ref := Syntax.missing) : Except (Array DecodeError) LeanExeConfig := ensureDecode do
  let name ← stringToLegalOrSimpleName <$> t.tryDecode `name ref
  let srcDir ← t.tryDecodeD `srcDir "."
  let root ← t.tryDecodeD `root name
  let exeName ← t.tryDecodeD `exeName (name.toStringWithSep "-" (escape := false))
  let supportInterpreter ← t.tryDecodeD `supportInterpreter false
  let toLeanConfig ← tryDecode <| LeanConfig.decodeToml t
  return {name, srcDir, root, exeName, supportInterpreter, toLeanConfig}

instance : DecodeToml LeanExeConfig := ⟨fun v => do LeanExeConfig.decodeToml (← v.decodeTable) v.ref⟩

protected def DependencySrc.decodeToml (t : Table) (ref := Syntax.missing) : Except (Array DecodeError) DependencySrc := do
  let typeVal ← t.decodeValue `type
  match (← typeVal.decodeString) with
  | "path" =>
    return .path (← t.decode `dir)
  | "git" => ensureDecode do
    return .git (← t.tryDecode `url ref) (← t.tryDecode? `rev) (← t.tryDecode? `subDir)
  | _ =>
    throw #[DecodeError.mk typeVal.ref "expected one of 'path' or 'git'"]

instance : DecodeToml DependencySrc := ⟨fun v => do DependencySrc.decodeToml (← v.decodeTable) v.ref⟩

protected def Dependency.decodeToml (t : Table) (ref := Syntax.missing) : Except (Array DecodeError) Dependency := ensureDecode do
  let name ← stringToLegalOrSimpleName <$> t.tryDecode `name ref
  let rev? ← t.tryDecode? `rev
  let src? : Option DependencySrc ← id do
    if let some dir ← t.tryDecode? `path then
      return some <| .path dir
    else if let some g := t.find? `git then
      match g with
      | .string _ url =>
        return some <| .git url rev? (← t.tryDecode? `subDir)
      | .table ref t =>
        return some <| .git (← t.tryDecode `url ref) rev? (← t.tryDecode? `subDir)
      | _ =>
        modify (·.push <| .mk g.ref "expected string or table")
        return default
    else
      t.tryDecode? `source
  let scope ← t.tryDecodeD `scope ""
  let version? ← id do
    if let some ver ← t.tryDecode? `version then
      return some ver
    else if let some rev := rev? then
      return if src?.isSome then none else some s!"git#{rev}"
    else
      return none
  let opts ← t.tryDecodeD `options {}
  return {name, scope, version?, src?, opts}

instance : DecodeToml Dependency := ⟨fun v => do Dependency.decodeToml (← v.decodeTable) v.ref⟩

/-! ## Root Loader -/

/--
Load a `Package` from a TOML Lake configuration file.
The resulting package does not yet include any dependencies.
-/
def loadTomlConfig (cfg: LoadConfig) : LogIO Package := do
  let input ← IO.FS.readFile cfg.configFile
  let ictx := mkInputContext input cfg.relConfigFile.toString
  match (← loadToml ictx |>.toBaseIO) with
  | .ok table =>
    let (pkg, errs) := Id.run <| StateT.run (s := (#[] : Array DecodeError)) do
      let config ← tryDecode <| PackageConfig.decodeToml table
      let leanLibConfigs ← mkRBArray (·.name) <$> table.tryDecodeD `lean_lib #[]
      let leanExeConfigs ← mkRBArray (·.name) <$> table.tryDecodeD `lean_exe #[]
      let defaultTargets ← table.tryDecodeD `defaultTargets #[]
      let defaultTargets := defaultTargets.map stringToLegalOrSimpleName
      let depConfigs ← table.tryDecodeD `require #[]
      return {
        dir := cfg.pkgDir
        relDir := cfg.relPkgDir
        relConfigFile := cfg.relConfigFile
        scope := cfg.scope
        remoteUrl := cfg.remoteUrl
        config, depConfigs, leanLibConfigs, leanExeConfigs
        defaultTargets
      }
    if errs.isEmpty then
      return pkg
    else
      errorWithLog <| errs.forM fun {ref, msg} =>
        let pos := ictx.fileMap.toPosition <| ref.getPos?.getD 0
        logError <| mkErrorStringWithPos ictx.fileName pos msg
  | .error log =>
    errorWithLog <| log.forM fun msg => do logError (← msg.toString)
