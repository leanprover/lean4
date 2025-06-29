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

class ToLean? (α : Type u) where
  toLean? : α → Option Term

export ToLean? (toLean?)

instance (priority := high) [ToLean α] : ToLean? α where
  toLean? a := some (toLean a)

def quoteArray? [ToLean? α] (as : Array α) : Option Term :=
  toLean <$> as.foldl (init := some #[]) fun vs? a => do
    let vs ← vs?
    let v ← toLean? a
    return vs.push v

instance [ToLean? α] : ToLean? (Array α) where
  toLean? as := quoteArray? as

class AddDeclField (σ : Type u) (name : Name) where
  addDeclField : σ → Array DeclField → Array DeclField

abbrev addDeclField (cfg : σ) (name : Name) [AddDeclField σ name] (fs : Array DeclField) : Array DeclField :=
  AddDeclField.addDeclField name cfg fs

def addDeclFieldCore
  (name : Name) (val : Term) (fs : Array DeclField)
: Array DeclField :=
  fs.push <| Unhygienic.run `(declField|$(mkIdent name) := $val)

instance [ToLean? α] [field : ConfigField σ name α] : AddDeclField σ name where
  addDeclField cfg fs := if let some v := toLean? (field.get cfg) then addDeclFieldCore name v fs else fs

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

@[inline] private def quoteSingleton? [ToLean? α] (name : Name) (a : α) : Option Term :=
  toLean? a |>.map fun a => Unhygienic.run `(.$(mkIdent name) $a)

protected def Pattern.toLean? [ToLean? (PatternDescr α β)] (p : Pattern α β) : Option Term :=
  match p.name with
  | .anonymous =>
    p.descr?.bind toLean?
  | `default =>
    none
  | n =>
    Unhygienic.run `(.$(mkIdent n))

instance [ToLean? (PatternDescr α β)] : ToLean? (Pattern α β) := ⟨Pattern.toLean?⟩

protected partial def PattternDescr.toLean? [ToLean? β] (p : PatternDescr α β) : Option Term :=
  have : ToLean? (PatternDescr α β) := ⟨PattternDescr.toLean?⟩
  match p with
  | .not p => quoteSingleton? `not p
  | .any p => quoteSingleton? `any p
  | .all p => quoteSingleton? `all p
  | .coe p => toLean? p

instance [ToLean? β] : ToLean? (PatternDescr α β) := ⟨PattternDescr.toLean?⟩

protected def StrPatDescr.toLean (pat : StrPatDescr) : Term :=
  match pat with
  | .mem xs => if xs.isEmpty then Unhygienic.run `(∅) else (toLean xs)
  | .startsWith affix => Unhygienic.run `(.$(mkIdent `startsWith) $(toLean affix))
  | .endsWith affix => Unhygienic.run `(.$(mkIdent `endsWith) $(toLean affix))

instance : ToLean StrPatDescr := ⟨StrPatDescr.toLean⟩

protected def PathPatDescr.toLean? (p : PathPatDescr) : Option Term :=
  match p with
  | .path p => quoteSingleton? `path p
  | .extension p => quoteSingleton? `extension p
  | .fileName p => quoteSingleton? `fileName p

instance : ToLean? PathPatDescr := ⟨PathPatDescr.toLean?⟩

@[inline] protected def PartialBuildKey.toLean (k : PartialBuildKey) : Term :=
  go k []
where
  go k (fs : List Name) := Unhygienic.run do
    match k with
    | .module n =>
      `(`+$(mkIdent n)$(mkSuffixes fs)*)
    | .package n =>
      if n.isAnonymous then
        `(`@$(mkSuffixes fs):facetSuffix*)
      else
        `(`@$(mkIdent n)$(mkSuffixes fs)*)
    | .packageTarget p t =>
      let t ←
        if let some t := t.eraseSuffix? moduleTargetIndicator then
          `(packageTargetLit|+$(mkIdent t))
        else
          `(packageTargetLit|$(mkIdent t):ident)
      if p.isAnonymous then
        `(`@/$t$(mkSuffixes fs)*)
      else
        `(`@$(mkIdent p)/$t$(mkSuffixes fs)*)
    | .facet k f =>
      return go k (f :: fs)
  mkSuffixes facets : Array (TSyntax ``facetSuffix) :=
    facets.toArray.map fun f => Unhygienic.run `(facetSuffix|:$(mkIdent f))

instance : ToLean PartialBuildKey := ⟨PartialBuildKey.toLean⟩
instance : ToLean (Target α) := ⟨(·.key.toLean)⟩

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
  let cmds ← genMkDeclFields cmds ``LeanLibConfig true
    (exclude := #[`nativeFacets])
  let cmds ← genMkDeclFields cmds ``LeanExeConfig true
    (exclude := #[`nativeFacets])
  let cmds ← genMkDeclFields cmds ``InputFileConfig true
  let cmds ← genMkDeclFields cmds ``InputDirConfig true
  -- Package
  let cmds ← genMkDeclFields cmds ``WorkspaceConfig false
  let cmds ← genMkDeclFields cmds ``PackageConfig true
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

protected def InputFileConfig.mkCommand
  (cfg : InputFileConfig n) (defaultTarget : Bool)
: Command := Unhygienic.run do
  let declVal? := mkDeclValWhere? (mkDeclFields cfg)
  let attrs? ← if defaultTarget then some <$> `(Term.attributes|@[default_target]) else pure none
  `(inputFileCommand|$[$attrs?:attributes]? input_file $(mkIdent n):ident $[$declVal?]?)

protected def InputDirConfig.mkCommand
  (cfg : InputDirConfig n) (defaultTarget : Bool)
: Command := Unhygienic.run do
  let declVal? := mkDeclValWhere? (mkDeclFields cfg)
  let attrs? ← if defaultTarget then some <$> `(Term.attributes|@[default_target]) else pure none
  `(inputDirCommand|$[$attrs?:attributes]? input_dir $(mkIdent n):ident $[$declVal?]?)

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
  $[$(pkg.mkTargetCommands defaultTargets LeanLib.configKind LeanLibConfig.mkCommand):command]*
  $[$(pkg.mkTargetCommands defaultTargets LeanExe.configKind LeanExeConfig.mkCommand):command]*
  $[$(pkg.mkTargetCommands defaultTargets InputFile.configKind InputFileConfig.mkCommand):command]*
  $[$(pkg.mkTargetCommands defaultTargets InputDir.configKind InputDirConfig.mkCommand):command]*
  )
