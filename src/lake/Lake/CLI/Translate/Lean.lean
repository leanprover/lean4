/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.DSL
import Lake.Config.Package
import Lean.Parser.Module

/-! # Lean Translation

Converts a declarative Lake configuration into a Lean module.
-/

namespace Lake
open DSL System Lean Syntax Parser Module

/-! ## General Helpers -/

private local instance : Quote FilePath where
  quote path := quote path.toString

private local instance : BEq FilePath where
  beq a b := a.normalize == b.normalize

private local instance : Quote Bool where
  quote b := mkIdent <| if b then `true else `false

@[inline] def addDeclField [Quote α] (name : Name) (val : α) (fs : Array DeclField) : Array DeclField :=
  fs.push <| Unhygienic.run `(declField|$(mkIdent name) := $(quote val))

@[inline] def addDeclField? [Quote α] (name : Name) (val? : Option α) (fs : Array DeclField) : Array DeclField :=
  if let some val := val? then addDeclField name val fs else fs

@[inline] def addDeclFieldD [Quote α] [BEq α] (name : Name) (val : α) (default : α) (fs : Array DeclField) : Array DeclField :=
  if val == default then fs else addDeclField name val fs

@[inline] def addDeclFieldNotEmpty [Quote α] (name : Name) (val : Array α) (fs : Array DeclField) : Array DeclField :=
  if val.isEmpty then fs else addDeclField name val fs

/-! ## Value Encoders -/

protected def BuildType.quote : BuildType → Term
| .debug => mkCIdent ``debug
| .minSizeRel => mkCIdent ``minSizeRel
| .relWithDebInfo => mkCIdent ``relWithDebInfo
| .release => mkCIdent ``release

instance : Quote BuildType := ⟨BuildType.quote⟩

protected def Backend.quote : Backend → Term
| .c => mkCIdent ``c
| .llvm => mkCIdent ``llvm
| .default => mkCIdent ``default

instance : Quote Backend := ⟨Backend.quote⟩

def quoteLeanOptionValue : LeanOptionValue → Term
| .ofString v => quote v
| .ofBool v => quote v
| .ofNat v => quote v

private local instance : Quote LeanOptionValue := ⟨quoteLeanOptionValue⟩

def quoteLeanOption (opt : LeanOption) : Term := Unhygienic.run do
  `(⟨$(quote opt.name), $(quote opt.value)⟩)

private local instance : Quote LeanOption := ⟨quoteLeanOption⟩

/-! ## Configuration Encoders -/

def WorkspaceConfig.addDeclFields (cfg : WorkspaceConfig) (fs : Array DeclField) : Array DeclField :=
  addDeclFieldD `packagesDir cfg.packagesDir defaultPackagesDir fs

def LeanConfig.addDeclFields (cfg : LeanConfig) (fs : Array DeclField) : Array DeclField :=
  fs
  |> addDeclFieldD `buildType  cfg.buildType .release
  |> addDeclFieldD `backend cfg.backend .default
  |> addDeclField? `platformIndependent cfg.platformIndependent
  |> addDeclFieldNotEmpty `leanOptions cfg.leanOptions
  |> addDeclFieldNotEmpty `moreServerOptions cfg.moreServerOptions
  |> addDeclFieldNotEmpty `moreLeanArgs cfg.moreLeanArgs
  |> addDeclFieldNotEmpty `weakLeanArgs cfg.weakLeanArgs
  |> addDeclFieldNotEmpty `moreLeancArgs cfg.moreLeancArgs
  |> addDeclFieldNotEmpty `weakLeancArgs cfg.weakLeancArgs
  |> addDeclFieldNotEmpty `moreLinkArgs cfg.moreLinkArgs
  |> addDeclFieldNotEmpty `weakLinkArgs cfg.weakLinkArgs

@[inline] def mkDeclValWhere? (fields : Array DeclField) : Option (TSyntax ``declValWhere) :=
  if fields.isEmpty then none else Unhygienic.run `(declValWhere|where $fields*)

def PackageConfig.mkSyntax (cfg : PackageConfig) : PackageDecl := Unhygienic.run do
  let declVal? := mkDeclValWhere? <|Array.empty
    |> addDeclFieldD `precompileModules cfg.precompileModules false
    |> addDeclFieldD `moreGlobalServerArgs cfg.moreGlobalServerArgs #[]
    |> addDeclFieldD `srcDir cfg.srcDir "."
    |> addDeclFieldD `buildDir cfg.buildDir defaultBuildDir
    |> addDeclFieldD `leanLibDir cfg.leanLibDir defaultLeanLibDir
    |> addDeclFieldD `nativeLibDir cfg.nativeLibDir defaultNativeLibDir
    |> addDeclFieldD `binDir cfg.binDir defaultBinDir
    |> addDeclFieldD `irDir cfg.irDir defaultIrDir
    |> addDeclField? `releaseRepo (cfg.releaseRepo <|> cfg.releaseRepo?)
    |> addDeclFieldD `buildArchive (cfg.buildArchive?.getD cfg.buildArchive) (defaultBuildArchive cfg.name)
    |> addDeclFieldD `preferReleaseBuild cfg.preferReleaseBuild false
    |> cfg.toWorkspaceConfig.addDeclFields
    |> cfg.toLeanConfig.addDeclFields
  `(packageDecl|package $(mkIdent cfg.name) $[$declVal?]?)

private def getEscapedNameParts? (acc : List String) : Name → Option (List String)
  | Name.anonymous => if acc.isEmpty then none else some acc
  | Name.str n s => do
    let s ← Name.escapePart s
    getEscapedNameParts? (s::acc) n
  | Name.num _ _ => none

def mkNameLit? (n : Name) : Option NameLit :=
  getEscapedNameParts? [] n  |>.map fun ss => mkNameLit ("`" ++ ".".intercalate ss)

protected def Glob.quote (glob : Glob) : Term := Unhygienic.run do
  match glob with
  | .one n => return quote n
  | .submodules n =>
    match mkNameLit? n with
    | some lit =>`($lit:name.+)
    | none => return mkCApp ``submodules #[quote n]
  | .andSubmodules n =>
    match mkNameLit? n with
    | some lit =>`($lit:name.*)
    | none => return mkCApp ``andSubmodules #[quote n]

local instance : Quote Glob := ⟨Glob.quote⟩

@[inline] private def mkConfigAttrs? (defaultTarget : Bool) : Option Attributes :=
  if defaultTarget then Unhygienic.run `(Term.attributes|@[default_target]) else none

protected def LeanLibConfig.mkSyntax (cfg : LeanLibConfig) (defaultTarget := false) : LeanLibDecl := Unhygienic.run do
  let declVal? := mkDeclValWhere? <| Array.empty
    |> addDeclFieldD `srcDir cfg.srcDir "."
    |> addDeclFieldD `roots cfg.roots #[cfg.name]
    |> addDeclFieldD `globs cfg.globs (cfg.roots.map .one)
    |> addDeclFieldD `libName cfg.libName (cfg.name.toString (escape := false))
    |> addDeclFieldD `precompileModules cfg.precompileModules false
    |> addDeclFieldD `defaultFacets cfg.defaultFacets #[LeanLib.leanArtsFacet]
    |> cfg.toLeanConfig.addDeclFields
  let attrs? := mkConfigAttrs? defaultTarget
  `(leanLibDecl|$[$attrs?:attributes]? lean_lib $(mkIdent cfg.name) $[$declVal?]?)

protected def LeanExeConfig.mkSyntax (cfg : LeanExeConfig) (defaultTarget := false) : LeanExeDecl := Unhygienic.run do
  let declVal? := mkDeclValWhere? <| Array.empty
    |> addDeclFieldD `srcDir cfg.srcDir "."
    |> addDeclFieldD `root cfg.root cfg.name
    |> addDeclFieldD `exeName cfg.exeName (cfg.name.toStringWithSep "-" (escape := false))
    |> addDeclFieldD `supportInterpreter cfg.supportInterpreter false
    |> cfg.toLeanConfig.addDeclFields
  let attrs? := mkConfigAttrs? defaultTarget
  `(leanExeDecl|$[$attrs?:attributes]? lean_exe $(mkIdent cfg.name) $[$declVal?]?)

protected def Dependency.mkSyntax (cfg : Dependency) : RequireDecl:= Unhygienic.run do
  let opts? := none
  match cfg.src with
  | .path dir =>
    `(requireDecl|require $(mkIdent cfg.name) from $(quote dir):term $[with $opts?]?)
  | .git url rev? subDir? =>
    `(requireDecl|require $(mkIdent cfg.name) from git $(quote url)
      $[@ $(rev?.map quote)]? $[/ $(subDir?.map quote)]? $[with $opts?]?)

/-! ## Root Encoder -/

/-- Create a Lean module that encodes the declarative configuration of the package. -/
def Package.mkLeanConfig (pkg : Package) : TSyntax ``module := Unhygienic.run do
  let pkgConfig := pkg.config.mkSyntax
  let defaultTargets := pkg.defaultTargets.foldl NameSet.insert NameSet.empty
  let requires := pkg.depConfigs.map (·.mkSyntax)
  let leanLibs := pkg.leanLibConfigs.toArray.map fun cfg =>
    cfg.mkSyntax (defaultTargets.contains cfg.name)
  let leanExes := pkg.leanExeConfigs.toArray.map fun cfg =>
    cfg.mkSyntax (defaultTargets.contains cfg.name)
  `(module|
  import $(mkIdent `Lake)
  open $(mkIdent `System) $(mkIdent `Lake) $(mkIdent `DSL)
  $pkgConfig:command
  $[$requires:command]*
  $[$leanLibs:command]*
  $[$leanExes:command]*
  )
