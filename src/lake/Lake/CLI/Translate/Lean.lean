/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.DSL
import Lake.Config.Package
import Lean.Parser.Module

open System Lean Syntax Parser Module

/-! # Lean Translation

Converts a declarative Lake configuration into a Lean module.
-/

namespace Lake
open DSL

/-! ## General Helpers -/

/-- Like `Quote`, but with some custom Lake-specific instances. -/
class ToLean (α : Type u) (k : SyntaxNodeKind := `term) where
  toLean : α → TSyntax k

export ToLean (toLean)

instance (priority := low) [Quote α k] : ToLean α k where
  toLean := quote

instance : ToLean FilePath where
  toLean path := toLean path.toString

instance [ToLean α] : ToLean (Array α) where
  toLean xs := let xs : Array Term := xs.map toLean; Unhygienic.run `(#[$xs,*])

private local instance : BEq FilePath where
  beq a b := a.normalize == b.normalize

instance : ToLean Bool where
  toLean b := mkIdent <| if b then `true else `false

class AddDeclField (σ : Type u) (name : Name) where
  addDeclField : σ → Array DeclField → Array DeclField

abbrev addDeclField (cfg : σ) (name : Name) [AddDeclField σ name] (fs : Array DeclField) : Array DeclField :=
  AddDeclField.addDeclField name cfg fs

@[inline] def addDeclFieldCore [ToLean α] (name : Name) (val : α) (fs : Array DeclField) : Array DeclField :=
  fs.push <| Unhygienic.run `(declField|$(mkIdent name) := $(toLean val))

@[inline] def addDeclFieldNotEmpty [ToLean α] (name : Name) (val : Array α) (fs : Array DeclField) : Array DeclField :=
  if val.isEmpty then fs else addDeclFieldCore name val fs

instance [ToLean α] [field : ConfigField σ name (Array α)] : AddDeclField σ name where
  addDeclField cfg := addDeclFieldNotEmpty name (field.get cfg)

@[inline] def addDeclFieldD [ToLean α] [BEq α] (name : Name) (val : α) (default : α) (fs : Array DeclField) : Array DeclField :=
  if val == default then fs else addDeclFieldCore name val fs

instance [ToLean α] [BEq α] [field : ConfigField σ name α] : AddDeclField σ name where
  addDeclField cfg := addDeclFieldD name (field.get cfg) (field.mkDefault cfg)

@[inline] def addDeclField? [ToLean α] (name : Name) (val? : Option α) (fs : Array DeclField) : Array DeclField :=
  if let some val := val? then addDeclFieldCore name val fs else fs

instance [ToLean α] [field : ConfigField σ name (Option α)] : AddDeclField σ name where
  addDeclField cfg := addDeclField? name (field.get cfg)

@[inline] def mkDeclValWhere? (fields : Array DeclField) : Option (TSyntax ``declValWhere) :=
  if fields.isEmpty then none else Unhygienic.run `(declValWhere|where $fields*)

/-! ## Value Encoders -/

protected def BuildType.toLean : BuildType → Term
| .debug => mkCIdent ``debug
| .minSizeRel => mkCIdent ``minSizeRel
| .relWithDebInfo => mkCIdent ``relWithDebInfo
| .release => mkCIdent ``release

instance : ToLean BuildType := ⟨BuildType.toLean⟩

set_option linter.unusedVariables false

protected def Backend.toLean : Backend → Term
| .c => mkCIdent ``c
| .llvm => mkCIdent ``llvm
| .default => mkCIdent ``default

instance : ToLean Backend := ⟨Backend.toLean⟩

def quoteLeanOptionValue : LeanOptionValue → Term
| .ofString v => toLean v
| .ofBool v => toLean v
| .ofNat v => toLean v

instance : ToLean LeanOptionValue := ⟨quoteLeanOptionValue⟩

def quoteLeanOption (opt : LeanOption) : Term := Unhygienic.run do
  `(⟨$(toLean opt.name), $(toLean opt.value)⟩)

instance : ToLean LeanOption := ⟨quoteLeanOption⟩

protected def LeanVer.toLean (v : LeanVer) : Term := Unhygienic.run do
  let lit := Syntax.mkLit interpolatedStrLitKind v.toString.quote
  let stx := mkNode interpolatedStrKind #[lit]
  `(v!$stx)

instance : ToLean LeanVer := ⟨LeanVer.toLean⟩

private def getEscapedNameParts? (acc : List String) : Name → Option (List String)
  | Name.anonymous => if acc.isEmpty then none else some acc
  | Name.str n s => do
    let s ← Name.escapePart s
    getEscapedNameParts? (s::acc) n
  | Name.num _ _ => none

def mkNameLit? (n : Name) : Option NameLit :=
  getEscapedNameParts? [] n  |>.map fun ss => mkNameLit ("`" ++ ".".intercalate ss)

protected def Glob.toLean (glob : Glob) : Term := Unhygienic.run do
  match glob with
  | .one n => return toLean n
  | .submodules n =>
    match mkNameLit? n with
    | some lit =>`($lit:name.+)
    | none => return mkCApp ``submodules #[toLean n]
  | .andSubmodules n =>
    match mkNameLit? n with
    | some lit =>`($lit:name.*)
    | none => return mkCApp ``andSubmodules #[toLean n]

instance : ToLean Glob := ⟨Glob.toLean⟩

def quoteVerTags? (pat : StrPat) : Option Term :=
  match pat with
  | .mem xs => if xs.isEmpty then Unhygienic.run `(∅) else some (toLean xs)
  | .startsWith pre => Unhygienic.run `(.$(mkIdent `startsWith) $(toLean pre))
  | .satisfies _ n =>
    if n.isAnonymous || n == `default then none else
    Unhygienic.run `(.$(mkIdent n))

instance : AddDeclField (PackageConfig n) `versionTags where
  addDeclField cfg := addDeclField? `versionTags (quoteVerTags? cfg.versionTags)

/-! ## Configuration Encoders -/

def WorkspaceConfig.addDeclFields (cfg : WorkspaceConfig) (fs : Array DeclField) : Array DeclField :=
  addDeclField cfg `packagesDir fs

def LeanConfig.addDeclFields (cfg : LeanConfig) (fs : Array DeclField) : Array DeclField :=
  fs
  |> addDeclField cfg `buildType
  |> addDeclField cfg `backend
  |> addDeclField cfg `platformIndependent
  |> addDeclField cfg `leanOptions
  |> addDeclField cfg `moreServerOptions
  |> addDeclField cfg `moreLeanArgs
  |> addDeclField cfg `weakLeanArgs
  |> addDeclField cfg `moreLeancArgs
  |> addDeclField cfg `weakLeancArgs
  |> addDeclField cfg `moreLinkArgs
  |> addDeclField cfg `weakLinkArgs

def PackageConfig.mkDeclFields (cfg : PackageConfig n) : Array DeclField :=
  Array.empty
  |> addDeclField cfg `precompileModules
  |> addDeclField cfg `moreGlobalServerArgs
  |> addDeclField cfg `srcDir
  |> addDeclField cfg `buildDir
  |> addDeclField cfg `leanLibDir
  |> addDeclField cfg `nativeLibDir
  |> addDeclField cfg `binDir
  |> addDeclField cfg `irDir
  |> addDeclField cfg `releaseRepo
  |> addDeclField cfg `buildArchive
  |> addDeclField cfg `preferReleaseBuild
  |> addDeclField cfg `testDriver
  |> addDeclField cfg `testDriverArgs
  |> addDeclField cfg `lintDriver
  |> addDeclField cfg `lintDriverArgs
  |> addDeclField cfg `version
  |> addDeclField cfg `versionTags
  |> addDeclField cfg `description
  |> addDeclField cfg `keywords
  |> addDeclField cfg `homepage
  |> addDeclField cfg `license
  |> addDeclField cfg `licenseFiles
  |> addDeclField cfg `readmeFile
  |> addDeclField cfg `reservoir
  |> cfg.toWorkspaceConfig.addDeclFields
  |> cfg.toLeanConfig.addDeclFields

def PackageConfig.mkCommand (cfg : PackageConfig n) : PackageCommand := Unhygienic.run do
  let declVal? := mkDeclValWhere? cfg.mkDeclFields
  `(packageCommand|package $(mkIdent n):ident $[$declVal?]?)

protected def LeanLibConfig.mkDeclFields (cfg : LeanLibConfig n) : Array DeclField :=
  Array.empty
  |> addDeclField cfg `srcDir
  |> addDeclField cfg `roots
  |> addDeclField cfg `globs
  |> addDeclField cfg `libName
  |> addDeclField cfg `precompileModules
  |> addDeclField cfg `defaultFacets
  |> cfg.toLeanConfig.addDeclFields

protected def LeanLibConfig.mkCommand
  (cfg : LeanLibConfig n) (defaultTarget := false)
: LeanLibCommand := Unhygienic.run do
  let declVal? := mkDeclValWhere? cfg.mkDeclFields
  let attrs? ← if defaultTarget then some <$> `(Term.attributes|@[default_target]) else pure none
  `(leanLibCommand|$[$attrs?:attributes]? lean_lib $(mkIdent n):ident $[$declVal?]?)

protected def LeanExeConfig.mkDeclFields (cfg : LeanExeConfig n) : Array DeclField :=
  Array.empty
  |> addDeclField cfg `srcDir
  |> addDeclField cfg `root
  |> addDeclField cfg `exeName
  |> addDeclField cfg `supportInterpreter
  |> cfg.toLeanConfig.addDeclFields

protected def LeanExeConfig.mkCommand
  (cfg : LeanExeConfig n) (defaultTarget := false)
: LeanExeCommand := Unhygienic.run do
  let declVal? := mkDeclValWhere? cfg.mkDeclFields
  let attrs? ← if defaultTarget then some <$> `(Term.attributes|@[default_target]) else pure none
  `(leanExeCommand|$[$attrs?:attributes]? lean_exe $(mkIdent n):ident $[$declVal?]?)

/-! ## Dependency Configuration Encoder -/

protected def Dependency.mkSyntax (cfg : Dependency) : RequireDecl := Unhygienic.run do
  let src? ← cfg.src?.mapM fun src =>
    match src with
    | .path dir =>
      `(fromSource|$(toLean dir):term)
    | .git url rev? subDir? =>
      `(fromSource|git $(toLean url) $[@ $(rev?.map toLean)]? $[/ $(subDir?.map toLean)]?)
  let ver? ←
    if let some ver := cfg.version? then
      if ver.startsWith "git#" then
        some <$> `(verSpec|git $(toLean <| ver.drop 4))
      else
        some <$> `(verSpec|$(toLean ver):term)
    else
      pure none
  let scope? := if cfg.scope.isEmpty then none else some (toLean cfg.scope)
  let opts? := if cfg.opts.isEmpty then none else some <| Unhygienic.run do
    cfg.opts.foldM (init := mkCIdent ``NameMap.empty) fun stx opt val =>
      `($stx |>.insert $(toLean opt) $(toLean val))
  `(requireDecl|require $[$scope? /]? $(mkIdent cfg.name):ident $[@ $ver?]?
    $[from $src?]? $[with $opts?]?)

/-! ## Root Encoder -/

/-- Create a Lean module that encodes the declarative configuration of the package. -/
def Package.mkLeanConfig (pkg : Package) : TSyntax ``module := Unhygienic.run do
  let defaultTargets := pkg.defaultTargets.foldl NameSet.insert NameSet.empty
  let pkgConfig : PackageConfig pkg.name :=
    {pkg.config with testDriver := pkg.testDriver, lintDriver := pkg.lintDriver}
  let pkgConfig := pkgConfig.mkCommand
  let requires := pkg.depConfigs.map (·.mkSyntax)
  let leanLibs := pkg.targetDecls.filterMap fun t => t.leanLibConfig?.map fun cfg =>
    cfg.mkCommand (defaultTargets.contains cfg.name)
  let leanExes := pkg.targetDecls.filterMap fun t => t.leanExeConfig?.map fun cfg =>
    cfg.mkCommand (defaultTargets.contains cfg.name)
  `(module|
  import $(mkIdent `Lake)
  open $(mkIdent `System) $(mkIdent `Lake) $(mkIdent `DSL)
  $pkgConfig:command
  $[$requires:command]*
  $[$leanLibs:command]*
  $[$leanExes:command]*
  )
