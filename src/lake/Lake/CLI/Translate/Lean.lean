/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
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

private local instance [Quote α] : Quote (Array α) where
  quote xs := let xs : Array Term := xs.map quote; Unhygienic.run `(#[$xs,*])

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

protected def LeanVer.quote (v : LeanVer) : Term := Unhygienic.run do
  let lit := Syntax.mkLit interpolatedStrLitKind  v.toString.quote
  let stx := mkNode interpolatedStrKind #[lit]
  `(v!$stx)

private local instance : Quote LeanVer := ⟨LeanVer.quote⟩

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

def PackageConfig.mkSyntax (cfg : PackageConfig)
  (testDriver := cfg.testDriver) (lintDriver := cfg.lintDriver)
: PackageDecl := Unhygienic.run do
  have : Quote Term := ⟨id⟩
  let declVal? := mkDeclValWhere? <| Array.empty
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
    |> addDeclFieldD `testDriver testDriver ""
    |> addDeclFieldD `testDriverArgs cfg.testDriverArgs #[]
    |> addDeclFieldD `lintDriver lintDriver ""
    |> addDeclFieldD `lintDriverArgs cfg.lintDriverArgs #[]
    |> addDeclFieldD `version cfg.version {}
    |> addDeclField? `versionTags (quoteVerTags? cfg.versionTags)
    |> addDeclFieldD `description cfg.description ""
    |> addDeclFieldD `keywords cfg.keywords #[]
    |> addDeclFieldD `homepage cfg.homepage ""
    |> addDeclFieldD `license cfg.license ""
    |> addDeclFieldD `licenseFiles cfg.licenseFiles #["LICENSE"]
    |> addDeclFieldD `readmeFile cfg.readmeFile "README.md"
    |> addDeclFieldD `reservoir cfg.reservoir true
    |> cfg.toWorkspaceConfig.addDeclFields
    |> cfg.toLeanConfig.addDeclFields
  `(packageDecl|package $(mkIdent cfg.name):ident $[$declVal?]?)
  where
    quoteVerTags? (pat : StrPat) : Option Term :=
      match pat with
      | .mem xs => if xs.isEmpty then Unhygienic.run `(∅) else some (quote xs)
      | .startsWith pre => Unhygienic.run `(.$(mkIdent `startsWith) $(quote pre))
      | .satisfies _ n =>
        if n.isAnonymous || n == `default then none else
        Unhygienic.run `(.$(mkIdent n))

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

protected def LeanLibConfig.mkSyntax
  (cfg : LeanLibConfig) (defaultTarget := false)
: LeanLibDecl := Unhygienic.run do
  let declVal? := mkDeclValWhere? <| Array.empty
    |> addDeclFieldD `srcDir cfg.srcDir "."
    |> addDeclFieldD `roots cfg.roots #[cfg.name]
    |> addDeclFieldD `globs cfg.globs (cfg.roots.map .one)
    |> addDeclFieldD `libName cfg.libName (cfg.name.toString (escape := false))
    |> addDeclFieldD `precompileModules cfg.precompileModules false
    |> addDeclFieldD `defaultFacets cfg.defaultFacets #[LeanLib.leanArtsFacet]
    |> cfg.toLeanConfig.addDeclFields
  let attrs? ← if defaultTarget then some <$> `(Term.attributes|@[default_target]) else pure none
  `(leanLibDecl|$[$attrs?:attributes]? lean_lib $(mkIdent cfg.name):ident $[$declVal?]?)

protected def LeanExeConfig.mkSyntax
  (cfg : LeanExeConfig) (defaultTarget := false)
: LeanExeDecl := Unhygienic.run do
  let declVal? := mkDeclValWhere? <| Array.empty
    |> addDeclFieldD `srcDir cfg.srcDir "."
    |> addDeclFieldD `root cfg.root cfg.name
    |> addDeclFieldD `exeName cfg.exeName (cfg.name.toStringWithSep "-" (escape := false))
    |> addDeclFieldD `supportInterpreter cfg.supportInterpreter false
    |> cfg.toLeanConfig.addDeclFields
    let attrs? ← if defaultTarget then some <$> `(Term.attributes|@[default_target]) else pure none
  `(leanExeDecl|$[$attrs?:attributes]? lean_exe $(mkIdent cfg.name):ident $[$declVal?]?)

protected def Dependency.mkSyntax (cfg : Dependency) : RequireDecl := Unhygienic.run do
  let src? ← cfg.src?.mapM fun src =>
    match src with
    | .path dir =>
      `(fromSource|$(quote dir):term)
    | .git url rev? subDir? =>
      `(fromSource|git $(quote url) $[@ $(rev?.map quote)]? $[/ $(subDir?.map quote)]?)
  let ver? ←
    if let some ver := cfg.version? then
      if ver.startsWith "git#" then
        some <$> `(verSpec|git $(quote <| ver.drop 4))
      else
        some <$> `(verSpec|$(quote ver):term)
    else
      pure none
  let scope? := if cfg.scope.isEmpty then none else some (quote cfg.scope)
  let opts? := if cfg.opts.isEmpty then none else some <| Unhygienic.run do
    cfg.opts.foldM (init := mkCIdent ``NameMap.empty) fun stx opt val =>
      `($stx |>.insert $(quote opt) $(quote val))
  `(requireDecl|require $[$scope? /]? $(mkIdent cfg.name):ident $[@ $ver?]?
    $[from $src?]? $[with $opts?]?)

/-! ## Root Encoder -/

/-- Create a Lean module that encodes the declarative configuration of the package. -/
def Package.mkLeanConfig (pkg : Package) : TSyntax ``module := Unhygienic.run do
  let defaultTargets := pkg.defaultTargets.foldl NameSet.insert NameSet.empty
  let pkgConfig := pkg.config.mkSyntax pkg.testDriver pkg.lintDriver
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
