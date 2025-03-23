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

private local instance : BEq FilePath where
  beq a b := a.normalize == b.normalize

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

instance : ToLean Bool where
  toLean b := mkIdent <| if b then `true else `false

class AddDeclField (σ : Type u) (name : Name) where
  addDeclField : σ → Array DeclField → Array DeclField

abbrev addDeclField (cfg : σ) (name : Name) [AddDeclField σ name] (fs : Array DeclField) : Array DeclField :=
  AddDeclField.addDeclField name cfg fs

def addDeclFieldCore
  (name : Name) (val : Term) (fs : Array DeclField)
: Array DeclField :=
  fs.push <| Unhygienic.run `(declField|$(mkIdent name) := $val)

@[inline] def addDeclFieldNotEmpty
  [ToLean α] (name : Name) (val : Array α) (fs : Array DeclField)
: Array DeclField :=
  if val.isEmpty then fs else addDeclFieldCore name (toLean val) fs

instance [ToLean α] [field : ConfigField σ name (Array α)] : AddDeclField σ name where
  addDeclField cfg := addDeclFieldNotEmpty name (field.get cfg)

@[inline] def addDeclFieldD
  [ToLean α] [BEq α] (name : Name) (val : α) (default : α) (fs : Array DeclField)
: Array DeclField :=
  if val == default then fs else addDeclFieldCore name (toLean val) fs

instance [ToLean α] [BEq α] [field : ConfigField σ name α] : AddDeclField σ name where
  addDeclField cfg := addDeclFieldD name (field.get cfg) (field.mkDefault cfg)

@[inline] def addDeclField?
  [ToLean α] (name : Name) (val? : Option α) (fs : Array DeclField)
: Array DeclField :=
  if let some val := val? then addDeclFieldCore name (toLean val) fs else fs

instance [ToLean α] [field : ConfigField σ name (Option α)] : AddDeclField σ name where
  addDeclField cfg := addDeclField? name (field.get cfg)

class MkDeclFields (α : Type u) where
  mkDeclFields : α → Array DeclField

export MkDeclFields (mkDeclFields)

def mkDeclValWhere? (fields : Array DeclField) : Option (TSyntax ``declValWhere) :=
  if fields.isEmpty then none else Unhygienic.run `(declValWhere|where $fields*)

/-! ## Value Encoders -/

protected def BuildType.toLean : BuildType → Term
| .debug => mkCIdent ``debug
| .minSizeRel => mkCIdent ``minSizeRel
| .relWithDebInfo => mkCIdent ``relWithDebInfo
| .release => mkCIdent ``release

instance : ToLean BuildType := ⟨BuildType.toLean⟩

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

/-! ## Dependency Configuration Encoder -/

def Dependency.mkRequire (cfg : Dependency) : RequireDecl := Unhygienic.run do
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

/-! ## Package & Target Configuration Encoders -/

private def genMkDeclFields
  (cmds : Array Command)
  (tyName : Name) [info : ConfigInfo tyName] (takesName : Bool)
  (exclude : Array Name := #[])
: MacroM (Array Command) := do
  let val ← `(fs)
  let ty := if takesName then Syntax.mkCApp tyName #[mkIdent `n] else mkCIdent tyName
  let val ← info.fields.foldlM (init := val) fun val {name, canonical, ..} => do
    if !canonical || exclude.contains name then
      return val
    else
      `($val |> addDeclField cfg $(quote name))
  let id ← mkIdentFromRef <| `_root_ ++ tyName.str "mkDeclFields"
  let cmds ← cmds.push <$> `(def $id (cfg : $ty) (fs : Array DeclField := #[]) := $val)
  let instId ← mkIdentFromRef <| `_root_ ++ tyName.str "instMkDeclFields"
  let cmds ← cmds.push <$> `(instance $instId:ident : MkDeclFields $ty := ⟨$id⟩)
  return cmds

local macro "gen_lean_encoders%" : command => do
  let cmds := #[]
  -- Targets
  let cmds ← genMkDeclFields cmds ``LeanConfig false
    (exclude := #[`dynlibs, `plugins])
  let cmds ← genMkDeclFields cmds ``LeanLibConfig true
    (exclude := #[`nativeFacets, `dynlibs, `plugins])
  let cmds ← genMkDeclFields cmds ``LeanExeConfig true
    (exclude := #[`nativeFacets, `dynlibs, `plugins])
  -- Package
  let cmds ← genMkDeclFields cmds ``WorkspaceConfig false
  let cmds ← genMkDeclFields cmds ``PackageConfig true
    (exclude := #[`nativeFacets, `dynlibs, `plugins])
  return ⟨mkNullNode cmds⟩

gen_lean_encoders%

def PackageConfig.mkCommand (cfg : PackageConfig n) : PackageCommand := Unhygienic.run do
  let declVal? := mkDeclValWhere? (mkDeclFields cfg)
  `(packageCommand|package $(mkIdent n):ident $[$declVal?]?)

protected def LeanLibConfig.mkCommand
  (cfg : LeanLibConfig n) (defaultTarget : Bool)
: Command := Unhygienic.run do
  let declVal? := mkDeclValWhere? (mkDeclFields cfg)
  let attrs? ← if defaultTarget then some <$> `(Term.attributes|@[default_target]) else pure none
  `(leanLibCommand|$[$attrs?:attributes]? lean_lib $(mkIdent n):ident $[$declVal?]?)

protected def LeanExeConfig.mkCommand
  (cfg : LeanExeConfig n) (defaultTarget : Bool)
: Command := Unhygienic.run do
  let declVal? := mkDeclValWhere? (mkDeclFields cfg)
  let attrs? ← if defaultTarget then some <$> `(Term.attributes|@[default_target]) else pure none
  `(leanExeCommand|$[$attrs?:attributes]? lean_exe $(mkIdent n):ident $[$declVal?]?)

@[inline] def Package.mkTargetCommands
  (pkg : Package) (defaultTargets : NameSet) (kind : Name)
  (mkCommand : {n : Name} → ConfigType kind pkg.name n → Bool → Command)
: Array Command :=
  pkg.targetDecls.filterMap fun t => (t.config? kind).map fun cfg =>
    mkCommand cfg (defaultTargets.contains t.name)

/-! ## Root Encoder -/

/-- Create a Lean module that encodes the declarative configuration of the package. -/
def Package.mkLeanConfig (pkg : Package) : TSyntax ``module := Unhygienic.run do
  let pkgConfig : PackageConfig pkg.name :=
    {pkg.config with testDriver := pkg.testDriver, lintDriver := pkg.lintDriver}
  let defaultTargets := pkg.defaultTargets.foldl NameSet.insert NameSet.empty
  `(module|
  import $(mkIdent `Lake)
  open $(mkIdent `System) $(mkIdent `Lake) $(mkIdent `DSL)
  $(pkgConfig.mkCommand):command
  $[$(pkg.depConfigs.map (·.mkRequire)):command]*
  $[$(pkg.mkTargetCommands defaultTargets `lean_lib LeanLibConfig.mkCommand):command]*
  $[$(pkg.mkTargetCommands defaultTargets `lean_exe LeanExeConfig.mkCommand):command]*
  )
