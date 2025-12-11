/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Toml.Encode
public import Lake.Config.Package
meta import Lake.Config.LeanLibConfig
meta import Lake.Config.LeanExeConfig
meta import Lake.Config.InputFileConfig
meta import Lake.Config.PackageConfig

/-! # TOML Translation

Converts a declarative Lake configuration into a TOML table.
-/

namespace Lake
open Lean System Toml

/-! ## General Helpers -/

private local instance : BEq FilePath where
  beq a b := a.normalize == b.normalize

class EncodeField (σ : Type u) (name : Name) (α : Type u) where
  encodeField : α → Value

instance [ToToml α] : EncodeField σ name α := ⟨toToml⟩

class InsertField (σ : Type u) (name : Name) where
  insertField : σ → Table → Table

abbrev Toml.Table.insertField
  (cfg : σ) (name : Name) [field : InsertField σ name] (t : Table)
: Table := InsertField.insertField name cfg t

instance [SmartInsert α] [field : ConfigField σ name α] : InsertField σ name where
  insertField cfg t := t.smartInsert name (field.get cfg)

instance [enc : EncodeField σ name α] [BEq α] [field : ConfigField σ name α] : InsertField σ name where
  insertField cfg t := t.insertD name (field.get cfg) (field.mkDefault cfg) (enc := ⟨enc.encodeField⟩)

/-! ## Value Encoders -/

public instance : ToToml LeanVer := ⟨(toToml <| toString ·)⟩
public instance : ToToml BuildType := ⟨(toToml ·.toString)⟩
public instance : ToToml Glob := ⟨(toToml ·.toString)⟩

public instance : ToToml Backend := ⟨(toToml ·.toString)⟩

public instance : SmartInsert Backend where
  smartInsert k v t := match v with | .default => t | v => t.insert k (toToml v)

public def Toml.encodeLeanOptionValue (v : LeanOptionValue) : Value :=
  match v with
  | .ofString s => toToml s
  | .ofBool b => toToml b
  | .ofNat n => toToml n

public instance : ToToml LeanOptionValue := ⟨encodeLeanOptionValue⟩

public def Toml.encodeLeanOptions (opts : Array LeanOption) : Table :=
  opts.foldl (init := {}) fun vs ⟨k,v⟩ => vs.insert k (toToml v)

public instance : ToToml (Array LeanOption) where
  toToml opts := .table .missing <| encodeLeanOptions opts

@[inline] private def encodeSingleton? [ToToml? α] (name : Name) (a : α) : Option Value :=
  toToml? a |>.map fun v => toToml <| Table.empty.insert name v

mutual

public partial def Pattern.toToml? [ToToml? β] (p : Pattern α β) : Option Value :=
  have : ToToml? (PatternDescr α β) := ⟨PatternDescr.toToml?⟩
  match p.name with
  | .anonymous =>
    p.descr?.bind toToml?
  | `default =>
    none
  | `star =>
    toToml "*"
  | n =>
    toToml <| Table.empty.insert `preset n

public partial def PatternDescr.toToml?
  [ToToml? β] (p : PatternDescr α β) : Option Value
:=
  have : ToToml? (Pattern α β) := ⟨Pattern.toToml?⟩
  match p with
  | .not p => encodeSingleton? `not p
  | .any p => encodeSingleton? `any p
  | .all p => encodeSingleton? `all p
  | .coe p => toToml? p

end

public instance [ToToml? β] : ToToml? (Pattern α β) := ⟨Pattern.toToml?⟩
public instance [ToToml? β] : ToToml? (PatternDescr α β) := ⟨PatternDescr.toToml?⟩

public protected def StrPatDescr.toToml (p : StrPatDescr) : Value :=
  match p with
  | .mem xs => toToml xs
  | .startsWith affix => toToml <| Table.empty.insert `startsWith (toToml affix)
  | .endsWith affix => toToml <| Table.empty.insert `endsWith (toToml affix)

instance : ToToml StrPatDescr := ⟨StrPatDescr.toToml⟩

public protected def PathPatDescr.toToml? (p : PathPatDescr) : Option Value :=
  match p with
  | .path p => encodeSingleton? `path p
  | .extension p => encodeSingleton? `extension p
  | .fileName p => encodeSingleton? `fileName p

instance : ToToml? PathPatDescr := ⟨PathPatDescr.toToml?⟩

public def encodeFacets (facets : Array Name) : Value :=
  toToml <| facets.map (toToml <| Name.eraseHead ·)

instance : EncodeField (LeanLibConfig n) `defaultFacets (Array Name) := ⟨encodeFacets⟩

instance : ToToml BuildKey := ⟨(toToml ·.toString)⟩
instance : ToToml PartialBuildKey := ⟨(toToml ·.toString)⟩
instance : ToToml (Target α) := ⟨(toToml ·.key.toString)⟩

/-! ## Dependency Configuration Encoders -/

public protected def Dependency.toToml (dep : Dependency) (t : Table  := {}) : Table :=
  let t := t
    |>.insert `name dep.name
    |>.insertD `scope dep.scope ""
    |>.smartInsert `version dep.version?
  let t :=
    if let some src := dep.src? then
      match src with
      | .path dir => t.insert `path (toToml dir)
      | .git url rev subDir? =>
        t.insert `git url
        |>.smartInsert `rev rev
        |>.smartInsert `subDir subDir?
    else
      t
  t.smartInsert `options <| dep.opts.foldl (·.insert · ·) Table.empty

public instance : ToToml Dependency := ⟨(toToml ·.toToml)⟩

/-! ## Package & Target Configuration Encoders -/

private meta def genToToml
  (cmds : Array Command)
  (tyName : Name) [info : ConfigInfo tyName]
  (exclude : Array Name := #[])
: MacroM (Array Command) := do
  let val ← if info.arity == 0 then `(t) else
    `(t.insert `name $(mkIdent <| .mkSimple s!"x_{info.arity}"))
  let tyArgs := info.arity.fold (init := Array.emptyWithCapacity info.arity) fun i _ as =>
    as.push (mkIdent <| .mkSimple s!"x_{i+1}")
  let ty := Syntax.mkCApp tyName tyArgs
  let val ← info.fields.foldlM (init := val) fun val {name, canonical, ..} => do
    if !canonical || exclude.contains name then
      return val
    else
      `($val |>.insertField cfg $(quote name))
  let id ← mkIdentFromRef <| `_root_ ++ tyName.str "toToml"
  let cmds ← cmds.push <$> `(def $id (cfg : $ty) (t : Table := {}) := $val)
  let instId ← mkIdentFromRef <| `_root_ ++ tyName.str "instToToml"
  let cmds ← cmds.push <$> `(instance $instId:ident : ToToml $ty := ⟨(toToml ·.toToml)⟩)
  return cmds

local macro "gen_toml_encoders%" : command => do
  let cmds := #[]
  -- Targets
  let cmds ← genToToml cmds ``LeanConfig
  let cmds ← genToToml cmds ``LeanLibConfig
    (exclude := #[`nativeFacets])
  let cmds ← genToToml cmds ``LeanExeConfig
    (exclude := #[`nativeFacets])
  let cmds ← genToToml cmds ``InputFileConfig
  let cmds ← genToToml cmds ``InputDirConfig
  -- Package
  let cmds ← genToToml cmds ``WorkspaceConfig
  let cmds ← genToToml cmds ``PackageConfig
  return ⟨mkNullNode cmds⟩

gen_toml_encoders%

@[inline] def Package.mkTomlTargets
  (pkg : Package) (kind : Name)
  (toToml : {n : Name} → ConfigType kind pkg.keyName n → Table)
: Array Table :=
  pkg.targetDecls.filterMap (·.config? kind |>.map toToml)

/-! ## Root Encoder -/

/-- Create a TOML table that encodes the declarative configuration of the package. -/
public def Package.mkTomlConfig (pkg : Package) (t : Table := {}) : Table :=
  let cfg : PackageConfig pkg.keyName pkg.origName :=
    {pkg.config with testDriver := pkg.testDriver, lintDriver := pkg.lintDriver}
  cfg.toToml t
  |>.smartInsert `defaultTargets pkg.defaultTargets
  |>.smartInsert `require pkg.depConfigs
  |>.smartInsert LeanLib.keyword (pkg.mkTomlTargets LeanLib.configKind LeanLibConfig.toToml)
  |>.smartInsert LeanExe.keyword (pkg.mkTomlTargets LeanExe.configKind LeanExeConfig.toToml)
  |>.smartInsert InputFile.keyword (pkg.mkTomlTargets InputFile.configKind InputFileConfig.toToml)
  |>.smartInsert InputDir.keyword (pkg.mkTomlTargets InputDir.configKind InputDirConfig.toToml)
