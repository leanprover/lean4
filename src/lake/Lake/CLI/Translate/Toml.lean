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

class InsertField (σ : Type u) (name : Name) where
  insertField : σ → Table → Table

abbrev Toml.Table.insertField
  (cfg : σ) (name : Name) [field : InsertField σ name] (t : Table)
: Table := InsertField.insertField name cfg t

instance [SmartInsert α] [field : ConfigField σ name α] : InsertField σ name where
  insertField cfg t := t.smartInsert name (field.get cfg)

instance [ToToml α] [BEq α] [field : ConfigField σ name α] : InsertField σ name where
  insertField cfg t := t.insertD name (field.get cfg) (field.mkDefault cfg)

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

def smartInsertVerTags (pat : StrPat) (t : Table) : Table :=
  match pat with
  | .mem s => t.insert `versionTags (toToml s)
  | .startsWith p => t.insert `versionTags.startsWith (toToml p)
  | .satisfies _ n =>
    if n.isAnonymous || n == `default then t else
    t.insert `versionTags.preset (toToml n)

instance : InsertField (PackageConfig n) `versionTags where
  insertField cfg := smartInsertVerTags cfg.versionTags

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
    (exclude := #[`dynlibs, `plugins])
  let cmds ← genToToml cmds ``LeanLibConfig true
    (exclude := #[`nativeFacets, `dynlibs, `plugins])
  let cmds ← genToToml cmds ``LeanExeConfig true
    (exclude := #[`nativeFacets, `dynlibs, `plugins])
  -- Package
  let cmds ← genToToml cmds ``WorkspaceConfig false
  let cmds ← genToToml cmds ``PackageConfig true
    (exclude := #[`nativeFacets, `dynlibs, `plugins])
  return ⟨mkNullNode cmds⟩

gen_toml_encoders%

@[inline] def Toml.Table.insertTargets
  (pkg : Package) (kind : Name)
  (toToml : {n : Name} → ConfigType kind pkg.name n → Table) (t : Table)
: Table :=
  t.smartInsert kind <| pkg.targetDecls.filterMap (·.config? kind |>.map toToml)

/-! ## Root Encoder -/

/-- Create a TOML table that encodes the declarative configuration of the package. -/
def Package.mkTomlConfig (pkg : Package) (t : Table := {}) : Table :=
  let cfg : PackageConfig pkg.name :=
    {pkg.config with testDriver := pkg.testDriver, lintDriver := pkg.lintDriver}
  cfg.toToml t
  |>.smartInsert `defaultTargets pkg.defaultTargets
  |>.smartInsert `require pkg.depConfigs
  |>.insertTargets pkg `lean_lib LeanLibConfig.toToml
  |>.insertTargets pkg `lean_exe LeanExeConfig.toToml
