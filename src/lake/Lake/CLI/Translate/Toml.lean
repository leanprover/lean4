/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Toml.Encode
import Lake.Config.Package

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

instance : ToToml LeanVer := ⟨(toToml <| toString ·)⟩
instance : ToToml BuildType := ⟨(toToml ·.toString)⟩
instance : ToToml Glob := ⟨(toToml ·.toString)⟩

instance : ToToml Backend := ⟨(toToml ·.toString)⟩

instance : SmartInsert Backend where
  smartInsert k v t := match v with | .default => t | v => t.insert k (toToml v)

def Toml.encodeLeanOptionValue (v : LeanOptionValue) : Value :=
  match v with
  | .ofString s => toToml s
  | .ofBool b => toToml b
  | .ofNat n => toToml n

instance : ToToml LeanOptionValue := ⟨encodeLeanOptionValue⟩

def Toml.encodeLeanOptions (opts : Array LeanOption) : Table :=
  opts.foldl (init := {}) fun vs ⟨k,v⟩ => vs.insert k (toToml v)

instance : ToToml (Array LeanOption) where
  toToml opts := .table .missing <| encodeLeanOptions opts

@[inline] private def encodeSingleton? [ToToml? α] (name : Name) (a : α) : Option Value :=
  toToml? a |>.map fun v => toToml <| Table.empty.insert name v

mutual

partial def Pattern.toToml? [ToToml? β] (p : Pattern α β) : Option Value :=
  have : ToToml? (PatternDescr α β) := ⟨PattternDescr.toToml?⟩
  match p.name with
  | .anonymous =>
    p.descr?.bind toToml?
  | `default =>
    none
  | `star =>
    toToml "*"
  | n =>
    toToml <| Table.empty.insert `preset n

partial def PattternDescr.toToml?
  [ToToml? β] (p : PatternDescr α β) : Option Value
:=
  have : ToToml? (Pattern α β) := ⟨Pattern.toToml?⟩
  match p with
  | .not p => encodeSingleton? `not p
  | .any p => encodeSingleton? `any p
  | .all p => encodeSingleton? `all p
  | .coe p => toToml? p

end

instance [ToToml? β] : ToToml? (Pattern α β) := ⟨Pattern.toToml?⟩
instance [ToToml? β] : ToToml? (PatternDescr α β) := ⟨PattternDescr.toToml?⟩

protected def StrPatDescr.toToml (p : StrPatDescr) : Value :=
  match p with
  | .mem xs => toToml xs
  | .startsWith affix => toToml <| Table.empty.insert `startsWith (toToml affix)
  | .endsWith affix => toToml <| Table.empty.insert `endsWith (toToml affix)

instance : ToToml StrPatDescr := ⟨StrPatDescr.toToml⟩

protected def PathPatDescr.toToml? (p : PathPatDescr) : Option Value :=
  match p with
  | .path p => encodeSingleton? `path p
  | .extension p => encodeSingleton? `extension p
  | .fileName p => encodeSingleton? `fileName p

instance : ToToml? PathPatDescr := ⟨PathPatDescr.toToml?⟩

def encodeFacets (facets : Array Name) : Value :=
  toToml <| facets.map (toToml <| Name.eraseHead ·)

instance : EncodeField (LeanLibConfig n) `defaultFacets (Array Name) := ⟨encodeFacets⟩

instance : ToToml BuildKey := ⟨(toToml ·.toString)⟩
instance : ToToml PartialBuildKey := ⟨(toToml ·.toString)⟩
instance : ToToml (Target α) := ⟨(toToml ·.key.toString)⟩

/-! ## Dependency Configuration Encoders -/

protected def Dependency.toToml (dep : Dependency) (t : Table  := {}) : Table :=
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
  t.smartInsert `options <| dep.opts.fold (·.insert · ·) Table.empty

instance : ToToml Dependency := ⟨(toToml ·.toToml)⟩

/-! ## Package & Target Configuration Encoders -/

private def genToToml
  (cmds : Array Command)
  (tyName : Name) [info : ConfigInfo tyName] (takesName : Bool)
  (exclude : Array Name := #[])
: MacroM (Array Command) := do
  let val ← if takesName then `(t.insert `name $(mkIdent `n)) else `(t)
  let ty := if takesName then Syntax.mkCApp tyName #[mkIdent `n] else mkCIdent tyName
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
  let cmds ← genToToml cmds ``LeanConfig false
  let cmds ← genToToml cmds ``LeanLibConfig true
    (exclude := #[`nativeFacets])
  let cmds ← genToToml cmds ``LeanExeConfig true
    (exclude := #[`nativeFacets])
  let cmds ← genToToml cmds ``InputFileConfig true
  let cmds ← genToToml cmds ``InputDirConfig true
  -- Package
  let cmds ← genToToml cmds ``WorkspaceConfig false
  let cmds ← genToToml cmds ``PackageConfig true
  return ⟨mkNullNode cmds⟩

gen_toml_encoders%

@[inline] def Package.mkTomlTargets
  (pkg : Package) (kind : Name)
  (toToml : {n : Name} → ConfigType kind pkg.name n → Table)
: Array Table :=
  pkg.targetDecls.filterMap (·.config? kind |>.map toToml)

/-! ## Root Encoder -/

/-- Create a TOML table that encodes the declarative configuration of the package. -/
def Package.mkTomlConfig (pkg : Package) (t : Table := {}) : Table :=
  let cfg : PackageConfig pkg.name :=
    {pkg.config with testDriver := pkg.testDriver, lintDriver := pkg.lintDriver}
  cfg.toToml t
  |>.smartInsert `defaultTargets pkg.defaultTargets
  |>.smartInsert `require pkg.depConfigs
  |>.smartInsert LeanLib.keyword (pkg.mkTomlTargets LeanLib.configKind LeanLibConfig.toToml)
  |>.smartInsert LeanExe.keyword (pkg.mkTomlTargets LeanExe.configKind LeanExeConfig.toToml)
  |>.smartInsert InputFile.keyword (pkg.mkTomlTargets InputFile.configKind InputFileConfig.toToml)
  |>.smartInsert InputDir.keyword (pkg.mkTomlTargets InputDir.configKind InputDirConfig.toToml)
